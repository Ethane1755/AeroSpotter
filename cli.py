from __future__ import annotations

import concurrent.futures
import csv
import gzip
import importlib
import json
import math
import re
import threading
import webbrowser
from dataclasses import dataclass
from datetime import datetime, timedelta, timezone
from html import unescape
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

import exifread
import piexif
import piexif.helper
import questionary
from rich.console import Console
from questionary import Style
from timezonefinder import TimezoneFinder
from typing import Any
from zoneinfo import ZoneInfo

import requests
import typer

# Application setup and shared configuration.
app = typer.Typer(help="AeroSpotter CLI (Home Lab NAS Edition)")
console = Console()

NAS_API_URL = "http://100.109.73.11:5000/api/adsb/bbox"
BUFFER_MINUTES = 5

AIRLINE_PREFIXES = {
}

AIRCRAFT_MODEL_MAP = {
    "A20N": "Airbus A320neo",
    "A21N": "Airbus A321neo",
    "A320": "Airbus A320-200",
    "A321": "Airbus A321-200",
    "A332": "Airbus A330-200",
    "A333": "Airbus A330-300",
    "A359": "Airbus A350-900",
    "A35K": "Airbus A350-1000",
    "B738": "Boeing 737-800",
    "B38M": "Boeing 737 MAX 8",
    "B77W": "Boeing 777-300ER",
    "B789": "Boeing 787-9",
    "B78X": "Boeing 787-10",
    "B744": "Boeing 747-400",
    "GLF4": "Gulfstream IV",
    "AT76": "ATR 72-600",
    "ZZZC": "Unknown Type (ZZZC)",
}

_EXTS = [".jpg", ".jpeg", ".png", ".cr2", ".nef", ".arw", ".dng", ".raf"]
SUPPORTED_EXTENSIONS = {ext.lower() for ext in _EXTS} | {ext.upper() for ext in _EXTS}
RAW_EXTENSIONS = {ext for ext in SUPPORTED_EXTENSIONS if ext.lower() not in [".jpg", ".jpeg", ".png"]}
_TIMEZONE_FINDER = TimezoneFinder(in_memory=True)

live_ac_cache = {}
known_hints_by_icao: dict[str, dict[str, str]] = {}
known_hints_by_callsign: dict[str, dict[str, str]] = {}
known_hints_by_reg: dict[str, dict[str, str]] = {}
traffic_db_cache_by_icao: dict[str, dict[str, str]] = {}
traffic_db_cache_by_reg: dict[str, dict[str, str]] = {}
traffic_db_missing: set[str] = set()
traffic_db_reg_missing: set[str] = set()
traffic_db_disabled = False
traffic_db_initialized = False
traffic_import_attempted = False
traffic_import_error: str | None = None
traffic_aircraft: Any | None = None
traffic_db_frame: Any | None = None
traffic_db_lock = threading.Lock()
local_db_cache_by_icao: dict[str, dict[str, str]] = {}
local_db_cache_by_reg: dict[str, dict[str, str]] = {}
local_db_missing: set[str] = set()
local_db_reg_missing: set[str] = set()
local_db_disabled = False
local_db_field_limit_set = False
local_db_lock = threading.Lock()
airline_map_loaded = False
airline_map_lock = threading.Lock()

TILE_CACHE_ROOT = Path.home() / ".cache" / "aerospotter" / "osm_tiles"
DB_DIR = Path(__file__).parent / "database"
AIRLINE_MAP_PATH = DB_DIR / "iata_airlines.csv"
LOCAL_DB_GZ_PATH = DB_DIR / "aircraft-database-complete-2025-08.csv.gz"
LOCAL_DB_CSV_FALLBACK_PATH = DB_DIR / "aircraft-database-complete-2025-08.csv"
UNKNOWN_TOKENS = {
    "",
    "N/A",
    "N/A (?)",
    "NONE",
    "NULL",
    "UNKNOWN",
    "UNKNOWN (?)",
    "NAN",
}
SUMMARY_PATTERN = re.compile(
    r"AeroSpotter:\\s*(?P<callsign>.*?)\\s*\\|\\s*Reg:\\s*(?P<reg>.*?)\\s*\\|\\s*Model:\\s*(?P<model>.*?)\\s*\\|\\s*Airline:\\s*(?P<owner>[^<\\r\\n]+)",
    re.IGNORECASE,
)

custom_style = Style([
    ('qmark', 'fg:#00ffff bold'),
    ('question', 'bold'),
    ('answer', 'fg:#00ff00 bold'),
    ('pointer', 'fg:#ff00ff bold'),
    ('highlighted', 'fg:#00ffff bold'),
    ('selected', 'fg:#cc5454'),
    ('instruction', 'fg:#888888 italic')
])

# Data models used to carry image and location metadata.
@dataclass(slots=True)
class LocationContext:
    latitude: float
    longitude: float
    timezone_name: str
    source: str

@dataclass(slots=True)
class ExifMetadata:
    image_path: Path
    captured_at_local: datetime | None
    raw_datetime: str | None
    offset_time: str | None
    latitude: float | None
    longitude: float | None

    @property
    def has_gps(self) -> bool:
        return self.latitude is not None and self.longitude is not None

# Network lookups and candidate enrichment.

def _is_unknown(value: str | None) -> bool:
    normalized = _clean_value(value)
    if not normalized:
        return True
    return normalized.upper() in UNKNOWN_TOKENS


def _clean_value(value: str | None) -> str:
    if value is None:
        return ""

    cleaned = str(value).strip()
    while len(cleaned) >= 2 and cleaned[0] == cleaned[-1] and cleaned[0] in {"'", '"'}:
        cleaned = cleaned[1:-1].strip()
    return cleaned


def _normalize_icao(value: str | None) -> str:
    normalized = _clean_value(value).lower()
    if not normalized:
        return "N/A"
    return normalized if normalized else "N/A"


def _normalize_reg(value: str | None) -> str:
    cleaned = _clean_value(value)
    if not cleaned:
        return ""
    return cleaned.replace("*", "").strip().upper()


def _prefer_known(current: str, fallback: str | None) -> str:
    if _is_unknown(current) and not _is_unknown(fallback):
        return _clean_value(fallback)
    return current


def _merge_hint_values(reg: str, model: str, owner: str, hint: dict[str, str]) -> tuple[str, str, str]:
    """Apply one hint dict onto current values, keeping existing known fields."""
    reg = _prefer_known(reg, hint.get("reg"))
    model = _prefer_known(model, hint.get("model"))
    owner = (owner, hint.get("owner"))
    return reg, model, owner


def _upsert_known_hint(icao: str, callsign: str, reg: str, model: str, owner: str) -> None:
    fact = {
        "callsign": callsign.strip(),
        "reg": reg.strip(),
        "model": model.strip(),
        "owner": owner.strip(),
    }

    if icao and icao != "N/A":
        bucket = known_hints_by_icao.setdefault(icao, {})
        for key, value in fact.items():
            if key not in bucket or _is_unknown(bucket.get(key)):
                if not _is_unknown(value):
                    bucket[key] = value

    if not _is_unknown(callsign):
        callsign_key = callsign.strip().upper()
        bucket = known_hints_by_callsign.setdefault(callsign_key, {})
        for key, value in fact.items():
            if key not in bucket or _is_unknown(bucket.get(key)):
                if not _is_unknown(value):
                    bucket[key] = value

    reg_key = _normalize_reg(reg)
    if reg_key:
        bucket = known_hints_by_reg.setdefault(reg_key, {})
        for key, value in fact.items():
            if key not in bucket or _is_unknown(bucket.get(key)):
                if not _is_unknown(value):
                    bucket[key] = value


def _extract_facts_from_text(content: str) -> list[dict[str, str]]:
    facts: list[dict[str, str]] = []
    for match in SUMMARY_PATTERN.finditer(content):
        facts.append(
            {
                "callsign": unescape(match.group("callsign")).strip(),
                "reg": unescape(match.group("reg")).strip(),
                "model": unescape(match.group("model")).strip(),
                "owner": unescape(match.group("owner")).strip(),
            }
        )
    return facts


def _load_local_hints(search_root: Path, recursive: bool) -> int:
    loaded = 0
    paths = search_root.rglob("*") if recursive else search_root.iterdir()
    for path in paths:
        if path.suffix.lower() not in {".xmp", ".md"}:
            continue
        try:
            content = path.read_text(encoding="utf-8", errors="ignore")
        except OSError:
            continue

        for fact in _extract_facts_from_text(content):
            _upsert_known_hint("N/A", fact["callsign"], fact["reg"], fact["model"], fact["owner"])
            loaded += 1
    return loaded


def _build_batch_hints(raw_results: list[dict]) -> dict[str, dict[str, str]]:
    hints: dict[str, dict[str, str]] = {}
    for flight in raw_results:
        icao = _normalize_icao(flight.get("hex", "N/A"))
        if icao == "N/A":
            continue
        bucket = hints.setdefault(icao, {})
        candidate_fact = {
            "callsign": str(flight.get("flight") or "N/A").strip(),
            "reg": str(flight.get("registration") or "N/A").strip(),
            "model": str(flight.get("typecode") or "N/A").strip(),
            "owner": str(flight.get("owner") or "N/A").strip(),
        }
        for key, value in candidate_fact.items():
            if key not in bucket or _is_unknown(bucket.get(key)):
                if not _is_unknown(value):
                    bucket[key] = value
    return hints


def _load_airline_prefixes() -> None:
    global airline_map_loaded

    if airline_map_loaded:
        return

    with airline_map_lock:
        if airline_map_loaded:
            return

        if AIRLINE_MAP_PATH.exists():
            try:
                with AIRLINE_MAP_PATH.open("r", encoding="utf-8", errors="ignore", newline="") as csv_file:
                    reader = csv.DictReader(csv_file, delimiter="^")
                    for row in reader:
                        icao_code = _clean_value(row.get("icao_code")).upper()
                        name = _clean_value(row.get("name"))
                        if len(icao_code) == 3 and not _is_unknown(name):
                            AIRLINE_PREFIXES.setdefault(icao_code, name)
            except OSError:
                pass

        airline_map_loaded = True


def _extract_callsign_prefix(callsign: str) -> str:
    letters = [ch for ch in callsign if ch.isalpha()]
    if len(letters) < 3:
        return ""
    return "".join(letters[:3]).upper()


def _infer_airline(callsign: str, airline: str) -> str:
    if not _is_unknown(airline):
        return airline

    _load_airline_prefixes()
    prefix = _extract_callsign_prefix(callsign)
    if prefix and prefix in AIRLINE_PREFIXES:
        return AIRLINE_PREFIXES[prefix]

    return "Private / Unknown Operator"


def _expand_model(model: str) -> str:
    normalized = _clean_value(model)
    if not normalized:
        return model
    return AIRCRAFT_MODEL_MAP.get(normalized.upper(), normalized)


def _ensure_local_db_field_limit() -> None:
    global local_db_field_limit_set

    if local_db_field_limit_set:
        return

    try:
        csv.field_size_limit(16 * 1024 * 1024)
    except (OverflowError, ValueError):
        pass

    local_db_field_limit_set = True


def _local_hint_from_row(row: dict[str, Any]) -> dict[str, str]:
    reg = _clean_value(row.get("registration") or "N/A")
    model = _clean_value(row.get("model") or row.get("typecode") or "N/A")
    owner = _clean_value(row.get("owner") or row.get("operator") or row.get("operatorIcao") or "N/A")
    return {"reg": reg, "model": model, "owner": owner}


def _resolve_local_db_path() -> Path | None:
    if LOCAL_DB_GZ_PATH.exists():
        return LOCAL_DB_GZ_PATH
    if LOCAL_DB_CSV_FALLBACK_PATH.exists():
        return LOCAL_DB_CSV_FALLBACK_PATH
    return None


def _scan_local_db(
    unresolved_icaos: set[str],
    unresolved_regs: set[str],
) -> tuple[set[str], set[str]]:
    local_db_path = _resolve_local_db_path()
    if local_db_path is None:
        return unresolved_icaos, unresolved_regs

    if local_db_path.suffix == ".gz":
        csv_stream = gzip.open(local_db_path, "rt", encoding="utf-8", errors="ignore", newline="")
    else:
        csv_stream = local_db_path.open("r", encoding="utf-8", errors="ignore", newline="")

    with csv_stream as csv_file:
        reader = csv.DictReader(csv_file, quotechar="'", skipinitialspace=False)
        for row in reader:
            icao = _normalize_icao(row.get("icao24", "N/A"))
            hint = _local_hint_from_row(row)
            reg_key = _normalize_reg(hint.get("reg"))

            if icao in unresolved_icaos:
                local_db_cache_by_icao[icao] = hint
                unresolved_icaos.remove(icao)

            if reg_key and reg_key in unresolved_regs:
                local_db_cache_by_reg[reg_key] = hint
                unresolved_regs.remove(reg_key)

            if not unresolved_icaos and not unresolved_regs:
                break

    return unresolved_icaos, unresolved_regs


def _lookup_local_db_for_icaos(icaos: set[str]) -> None:
    global local_db_disabled

    with local_db_lock:
        if local_db_disabled:
            return

        unresolved_icaos = {
            icao
            for icao in icaos
            if icao != "N/A" and icao not in local_db_cache_by_icao and icao not in local_db_missing
        }
        if not unresolved_icaos or _resolve_local_db_path() is None:
            return

        try:
            _ensure_local_db_field_limit()
            unresolved_icaos, _ = _scan_local_db(unresolved_icaos, set())
        except csv.Error as e:
            local_db_disabled = True
            console.print(f"[yellow]本地 CSV 讀取失敗，略過離線補值: {e}[/yellow]")
            return
        except OSError:
            return

        local_db_missing.update(unresolved_icaos)


def _lookup_local_db_for_regs(regs: set[str]) -> None:
    global local_db_disabled

    normalized_regs = {_normalize_reg(reg) for reg in regs}

    with local_db_lock:
        if local_db_disabled:
            return

        unresolved_regs = {
            reg
            for reg in normalized_regs
            if reg and reg not in local_db_cache_by_reg and reg not in local_db_reg_missing
        }
        if not unresolved_regs or _resolve_local_db_path() is None:
            return

        try:
            _ensure_local_db_field_limit()
            _, unresolved_regs = _scan_local_db(set(), unresolved_regs)
        except csv.Error as e:
            local_db_disabled = True
            console.print(f"[yellow]本地 CSV 讀取失敗，略過離線補值: {e}[/yellow]")
            return
        except OSError:
            return

        local_db_reg_missing.update(unresolved_regs)


def _init_traffic_db() -> Any | None:
    global traffic_import_attempted
    global traffic_import_error
    global traffic_aircraft
    global traffic_db_initialized
    global traffic_db_disabled
    global traffic_db_frame

    if traffic_db_disabled:
        return None

    if traffic_db_initialized:
        return traffic_db_frame

    traffic_db_initialized = True
    if not traffic_import_attempted:
        traffic_import_attempted = True
        try:
            traffic_data = importlib.import_module("traffic.data")
            traffic_aircraft = getattr(traffic_data, "aircraft", None)
            traffic_import_error = None
        except Exception as e:
            traffic_aircraft = None
            traffic_import_error = str(e)

    if traffic_aircraft is None:
        traffic_db_disabled = True
        detail = f" ({traffic_import_error})" if traffic_import_error else ""
        console.print(f"[yellow]無法載入 traffic，略過 traffic 離線補值。請確認已安裝相依套件: pip install traffic pandas{detail}[/yellow]")
        return None

    try:
        console.print("[dim]初始化 traffic aircraft 資料庫（首次可能會自動下載並快取）...[/dim]")
        traffic_db_frame = traffic_aircraft.data
        return traffic_db_frame
    except Exception as e:
        traffic_db_disabled = True
        console.print(f"[yellow]traffic 資料庫初始化失敗，略過離線補值: {e}[/yellow]")
        return None


def _traffic_hint_from_row(row: Any) -> dict[str, str]:
    reg = _clean_value(row.get("registration") or row.get("regid") or row.get("tailnumber") or "N/A")
    model = _clean_value(row.get("model") or row.get("typecode") or row.get("icaoAircraftType") or "N/A")
    owner = _clean_value(
        row.get("owner")
        or row.get("operator")
        or row.get("operatoricao")
        or row.get("operatorIcao")
        or "N/A"
    )
    return {"reg": reg, "model": model, "owner": owner}


def _lookup_traffic_db_for_icaos(icaos: set[str]) -> None:
    with traffic_db_lock:
        unresolved_icaos = {
            icao
            for icao in icaos
            if icao != "N/A" and icao not in traffic_db_cache_by_icao and icao not in traffic_db_missing
        }
        if not unresolved_icaos:
            return

        db = _init_traffic_db()
        if db is None:
            return

        if "icao24" not in db.columns:
            traffic_db_missing.update(unresolved_icaos)
            return

        try:
            filtered = db[db["icao24"].astype(str).str.strip().str.lower().isin(unresolved_icaos)]
            for _, row in filtered.iterrows():
                icao = _normalize_icao(row.get("icao24", "N/A"))
                if icao in unresolved_icaos:
                    hint = _traffic_hint_from_row(row)
                    traffic_db_cache_by_icao[icao] = hint
                    reg_key = _normalize_reg(hint.get("reg"))
                    if reg_key:
                        traffic_db_cache_by_reg.setdefault(reg_key, hint)
                    unresolved_icaos.remove(icao)
        except Exception:
            pass

        traffic_db_missing.update(unresolved_icaos)


def _lookup_traffic_db_for_regs(regs: set[str]) -> None:
    normalized_regs = {_normalize_reg(reg) for reg in regs}

    with traffic_db_lock:
        unresolved_regs = {
            reg
            for reg in normalized_regs
            if reg and reg not in traffic_db_cache_by_reg and reg not in traffic_db_reg_missing
        }
        if not unresolved_regs:
            return

        db = _init_traffic_db()
        if db is None:
            return

        if "registration" not in db.columns:
            traffic_db_reg_missing.update(unresolved_regs)
            return

        try:
            reg_series = db["registration"].astype(str).str.replace("*", "", regex=False).str.strip().str.upper()
            filtered = db[reg_series.isin(unresolved_regs)]
            for _, row in filtered.iterrows():
                hint = _traffic_hint_from_row(row)
                reg_key = _normalize_reg(hint.get("reg"))
                if reg_key and reg_key in unresolved_regs:
                    traffic_db_cache_by_reg[reg_key] = hint
                    unresolved_regs.remove(reg_key)
        except Exception:
            pass

        traffic_db_reg_missing.update(unresolved_regs)

def _empty_aircraft_info() -> dict:
    return {"reg": "N/A", "type": "N/A", "airline": "N/A", "mfr": "", "year": ""}

def get_live_aircraft_info(icao: str) -> dict:
    if icao in live_ac_cache:
        return live_ac_cache[icao]
    try:
        url = f"https://hexdb.io/api/v1/aircraft/{icao}"
        res = requests.get(url, timeout=3)
        if res.status_code == 200:
            data = res.json()
            info = {
                "reg": data.get("Registration", "N/A") or "N/A",
                "type": data.get("Type", "N/A") or "N/A",
                "airline": data.get("Operator", "N/A") or "N/A",
                "mfr": data.get("Manufacturer", "") or "",
                "year": data.get("YearBuilt", "") or ""
            }
            live_ac_cache[icao] = info
            return info
    except Exception:
        pass
    return _empty_aircraft_info()


def _enrich_candidate(flight: dict, batch_hints: dict[str, dict[str, str]]) -> dict:
    icao = _normalize_icao(flight.get("hex", "N/A"))
    callsign = str(flight.get("flight") or "N/A").strip()
    reg = str(flight.get("registration") or "N/A").strip()
    model = str(flight.get("typecode") or "N/A").strip()
    owner = str(flight.get("owner") or "N/A").strip()

    batch_hint = batch_hints.get(icao, {})
    callsign = _prefer_known(callsign, batch_hint.get("callsign"))
    reg, model, owner = _merge_hint_values(reg, model, owner, batch_hint)

    icao_hint = known_hints_by_icao.get(icao, {})
    callsign_hint = known_hints_by_callsign.get(callsign.upper(), {}) if not _is_unknown(callsign) else {}
    reg_hint = known_hints_by_reg.get(_normalize_reg(reg), {}) if not _is_unknown(reg) else {}
    for hint in (icao_hint, reg_hint, callsign_hint):
        reg, model, owner = _merge_hint_values(reg, model, owner, hint)

    db_hint = traffic_db_cache_by_icao.get(icao, {})
    reg, model, owner = _merge_hint_values(reg, model, owner, db_hint)

    local_hint = local_db_cache_by_icao.get(icao, {})
    reg, model, owner = _merge_hint_values(reg, model, owner, local_hint)

    reg_key = _normalize_reg(reg)
    if reg_key and (_is_unknown(owner) or _is_unknown(model)):
        _lookup_traffic_db_for_regs({reg_key})
        reg_db_hint = traffic_db_cache_by_reg.get(reg_key, {})
        reg, model, owner = _merge_hint_values(reg, model, owner, reg_db_hint)

        _lookup_local_db_for_regs({reg_key})
        local_reg_db_hint = local_db_cache_by_reg.get(reg_key, {})
        reg, model, owner = _merge_hint_values(reg, model, owner, local_reg_db_hint)

    if _is_unknown(reg) or _is_unknown(model):
        live = get_live_aircraft_info(icao)
        if live["reg"] != "N/A":
            reg = _prefer_known(reg, f"{live['reg']}*")
            owner = _prefer_known(owner, live["airline"])
            live_model = f"{live['mfr']} {live['type']}".strip()
            if live["year"]:
                live_model += f" ({live['year']})"
            model = _prefer_known(model, live_model)

    if not _is_unknown(model):
        model = _expand_model(model)

    owner = _infer_airline(callsign, owner)

    callsign = "N/A" if _is_unknown(callsign) else callsign
    reg = "N/A" if _is_unknown(reg) else reg
    model = "N/A" if _is_unknown(model) else model
    owner = "N/A" if _is_unknown(owner) else owner

    return {
        "icao": icao,
        "callsign": callsign,
        "reg": reg,
        "model": model,
        "owner": owner,
        "display": f"{callsign:<8} | Reg: {reg:<8} | Model: {model:<28} | Airline: {owner}",
    }

def query_nas_history(latitude: float, longitude: float, time_utc: datetime) -> list[dict]:
    delta_lat = 15.0 / 111.0
    delta_lon = 15.0 / (111.0 * math.cos(math.radians(latitude)))
    bbox = f"{longitude-delta_lon:.4f},{latitude-delta_lat:.4f},{longitude+delta_lon:.4f},{latitude+delta_lat:.4f}"
    
    start_time = (time_utc - timedelta(minutes=BUFFER_MINUTES)).strftime("%Y-%m-%dT%H:%M:%SZ")
    end_time = (time_utc + timedelta(minutes=BUFFER_MINUTES)).strftime("%Y-%m-%dT%H:%M:%SZ")

    try:
        resp = requests.get(NAS_API_URL, params={"bbox": bbox, "start_time": start_time, "end_time": end_time}, timeout=10)
        resp.raise_for_status()
        raw_results = resp.json().get("results", [])

        batch_hints = _build_batch_hints(raw_results)
        _lookup_traffic_db_for_icaos(set(batch_hints.keys()))
        _lookup_local_db_for_icaos(set(batch_hints.keys()))

        def enrich_with_hints(flight: dict) -> dict:
            return _enrich_candidate(flight, batch_hints)

        with concurrent.futures.ThreadPoolExecutor(max_workers=10) as executor:
            candidates = list(executor.map(enrich_with_hints, raw_results))

        candidates.sort(key=lambda x: (x['callsign'] == 'N/A', x['reg'] == 'N/A', x['callsign']))
        return candidates
    except Exception as e:
        console.print(f"[red]NAS 查詢失敗: {e}[/red]")
        return []

# EXIF parsing and metadata writing.

def _ratio_to_float(value: Any) -> float:
    return float(value.num) / float(value.den)


def _collect_image_paths(target: Path, recursive: bool) -> list[Path]:
    if target.is_file():
        return [target]

    paths = target.rglob("*") if recursive else target.iterdir()
    return sorted(path for path in paths if path.suffix in SUPPORTED_EXTENSIONS)


def _select_coordinates_from_map(timeout_seconds: int = 300) -> tuple[float, float]:
    TILE_PROXY_UA = "AeroSpotter-LocalTileProxy/1.0"
    tile_cache_dir = TILE_CACHE_ROOT
    tile_cache_dir.mkdir(parents=True, exist_ok=True)

    html = """<!doctype html>
<html lang="zh-Hant">
<head>
    <meta charset="utf-8" />
    <meta name="viewport" content="width=device-width, initial-scale=1" />
    <title>Select Coordinates</title>
    <link rel="preconnect" href="https://tile.openstreetmap.org" crossorigin />
    <link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/leaflet@1.9.4/dist/leaflet.css" />
    <style>
        html, body { margin: 0; padding: 0; font-family: -apple-system, BlinkMacSystemFont, sans-serif; background: #f5f7fb; }
        .container { max-width: 1100px; margin: 0 auto; padding: 14px; }
        .card { background: #fff; border: 1px solid #dde4ee; border-radius: 12px; padding: 12px; }
        .top { display: flex; flex-wrap: wrap; gap: 10px; align-items: end; margin-bottom: 10px; }
        .field { display: flex; flex-direction: column; gap: 6px; }
        input[type="number"] { width: 170px; padding: 8px; border: 1px solid #c9d5e3; border-radius: 8px; }
        button { border: 0; border-radius: 8px; padding: 9px 14px; cursor: pointer; font-size: 14px; }
        #sync { background: #0f766e; color: #fff; }
        #confirm { background: #1d4ed8; color: #fff; }
        #map { height: 560px; border-radius: 10px; border: 1px solid #d0dae8; }
        .hint { color: #475569; font-size: 13px; margin-top: 8px; white-space: pre-line; }
    </style>
</head>
<body>
    <div class="container">
        <div class="card">
            <div class="top">
                <div class="field">
                    <label for="lat">緯度 (Latitude)</label>
                    <input id="lat" type="number" step="0.000001" value="25.033000" />
                </div>
                <div class="field">
                    <label for="lng">經度 (Longitude)</label>
                    <input id="lng" type="number" step="0.000001" value="121.565400" />
                </div>
                <div class="field">
                    <label for="zoom">縮放 (1-19)</label>
                    <input id="zoom" type="number" min="1" max="19" step="1" value="7" />
                </div>
                <button id="sync">移動地圖</button>
                <button id="confirm">確認座標</button>
            </div>

            <div id="map"></div>
            <div class="hint" id="status">載入 OpenStreetMap 中... 使用本機快取圖磚，縮放會更穩定。</div>
            <div class="hint">備援：<a href="https://www.openstreetmap.org" target="_blank" rel="noopener">openstreetmap.org</a></div>
        </div>
    </div>

    <script src="https://cdn.jsdelivr.net/npm/leaflet@1.9.4/dist/leaflet.js"></script>
    <script>
        const latInput = document.getElementById('lat');
        const lngInput = document.getElementById('lng');
        const zoomInput = document.getElementById('zoom');
        const status = document.getElementById('status');
        const syncButton = document.getElementById('sync');
        const confirmButton = document.getElementById('confirm');

        function clamp(v, min, max) {
            return Math.max(min, Math.min(max, v));
        }

        function getInputState() {
            const lat = clamp(Number(latInput.value) || 0, -85, 85);
            const lng = clamp(Number(lngInput.value) || 0, -180, 180);
            const zoom = clamp(Math.round(Number(zoomInput.value) || 7), 1, 19);
            latInput.value = lat.toFixed(6);
            lngInput.value = lng.toFixed(6);
            zoomInput.value = zoom;
            return { lat, lng, zoom };
        }

        let map = null;
        let marker = null;

        function updateInputs(lat, lng, zoom) {
            latInput.value = lat.toFixed(6);
            lngInput.value = lng.toFixed(6);
            if (Number.isFinite(zoom)) {
                zoomInput.value = zoom;
            }
        }

        function ensureMarker(lat, lng) {
            if (!marker) {
                marker = L.marker([lat, lng]).addTo(map);
            } else {
                marker.setLatLng([lat, lng]);
            }
        }

        function initMap() {
            if (typeof L === 'undefined') {
                status.textContent = 'Leaflet 載入失敗，請手動輸入座標後按確認。';
                return;
            }

            const { lat, lng, zoom } = getInputState();
            map = L.map('map', {
                zoomControl: true,
                preferCanvas: true,
                fadeAnimation: false,
                zoomAnimation: false,
                markerZoomAnimation: false,
            }).setView([lat, lng], zoom);

            L.tileLayer('/tiles/{z}/{x}/{y}.png', {
                maxZoom: 19,
                maxNativeZoom: 17,
                detectRetina: false,
                attribution: '&copy; OpenStreetMap contributors',
                keepBuffer: 1,
                updateWhenIdle: true,
                updateWhenZooming: false,
            }).addTo(map);

            ensureMarker(lat, lng);
            status.textContent = 'OpenStreetMap 已載入，點地圖即可選座標。';

            map.on('click', (event) => {
                const selected = event.latlng;
                ensureMarker(selected.lat, selected.lng);
                updateInputs(selected.lat, selected.lng, map.getZoom());
                status.textContent = `已選擇: 緯度 ${latInput.value}, 經度 ${lngInput.value}`;
            });

            map.on('moveend', () => {
                const center = map.getCenter();
                updateInputs(center.lat, center.lng, map.getZoom());
            });
        }

        syncButton.addEventListener('click', () => {
            const { lat, lng, zoom } = getInputState();
            if (map) {
                map.setView([lat, lng], zoom, { animate: false });
                ensureMarker(lat, lng);
                status.textContent = '地圖已移動到輸入位置。';
            } else {
                status.textContent = '地圖尚未載入，仍可直接按確認送出。';
            }
        });

        async function submitSelection() {
            const { lat, lng } = getInputState();
            confirmButton.disabled = true;
            try {
                const response = await fetch('/select', {
                    method: 'POST',
                    headers: { 'Content-Type': 'application/json' },
                    body: JSON.stringify({ lat, lng })
                });
                if (!response.ok) {
                    throw new Error('Failed to submit coordinates');
                }
                status.textContent = '座標已送出，請回到 CLI。';
            } catch (error) {
                status.textContent = '送出失敗，請重試。';
                confirmButton.disabled = false;
            }
        }

        confirmButton.addEventListener('click', submitSelection);
        initMap();
    </script>
</body>
</html>
"""

    selected = threading.Event()
    coordinate: dict[str, float] = {}

    def _tile_cache_path(z: int, x: int, y: int) -> Path:
        return tile_cache_dir / str(z) / str(x) / f"{y}.png"

    def _read_cached_tile(z: int, x: int, y: int) -> bytes | None:
        path = _tile_cache_path(z, x, y)
        try:
            if path.exists():
                return path.read_bytes()
        except OSError:
            return None
        return None

    def _fetch_remote_tile(z: int, x: int, y: int) -> bytes | None:
        url = f"https://tile.openstreetmap.org/{z}/{x}/{y}.png"
        try:
            response = requests.get(url, timeout=10, headers={"User-Agent": TILE_PROXY_UA})
            if response.status_code != 200:
                return None
            tile_bytes = response.content
        except requests.RequestException:
            return None

        cache_path = _tile_cache_path(z, x, y)
        try:
            cache_path.parent.mkdir(parents=True, exist_ok=True)
            cache_path.write_bytes(tile_bytes)
        except OSError:
            pass
        return tile_bytes

    def _parse_tile_request(path: str) -> tuple[int, int, int] | None:
        tile_path = path.split("?", 1)[0]
        parts = tile_path.strip("/").split("/")
        if len(parts) != 4 or parts[0] != "tiles" or not parts[3].endswith(".png"):
            return None

        z_text, x_text = parts[1], parts[2]
        y_text = parts[3][:-4]

        if not (z_text.isdigit() and x_text.isdigit() and y_text.isdigit()):
            return None

        z, x, y = int(z_text), int(x_text), int(y_text)
        if z < 0 or z > 19:
            return None

        max_index = (1 << z) - 1
        if x < 0 or y < 0 or x > max_index or y > max_index:
            return None

        return z, x, y

    class MapHandler(BaseHTTPRequestHandler):
        def _send_bytes(self, body: bytes, content_type: str, cache_control: str | None = None) -> None:
            try:
                self.send_response(200)
                self.send_header("Content-Type", content_type)
                if cache_control:
                    self.send_header("Cache-Control", cache_control)
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)
            except (BrokenPipeError, ConnectionResetError):
                # Browser may cancel in-flight tile requests while zooming/panning.
                return

        def do_GET(self) -> None:
            if self.path == "/":
                encoded = html.encode("utf-8")
                self._send_bytes(encoded, "text/html; charset=utf-8")
                return

            tile_request = _parse_tile_request(self.path)
            if tile_request is None:
                self.send_error(404)
                return

            z, x, y = tile_request
            tile_bytes = _read_cached_tile(z, x, y)
            if tile_bytes is None:
                tile_bytes = _fetch_remote_tile(z, x, y)

            if tile_bytes is None:
                self.send_error(502, "Tile fetch failed")
                return

            self._send_bytes(tile_bytes, "image/png", cache_control="public, max-age=86400")

        def do_POST(self) -> None:
            if self.path != "/select":
                self.send_error(404)
                return

            content_length = int(self.headers.get("Content-Length", "0"))
            raw_body = self.rfile.read(content_length)
            try:
                payload = json.loads(raw_body.decode("utf-8"))
                coordinate["lat"] = float(payload["lat"])
                coordinate["lng"] = float(payload["lng"])
            except (ValueError, KeyError, json.JSONDecodeError):
                self.send_error(400, "Invalid coordinate payload")
                return

            selected.set()
            self._send_bytes(b'{"ok": true}', "application/json")

        def log_message(self, format: str, *args: object) -> None:
            return

    server = ThreadingHTTPServer(("127.0.0.1", 0), MapHandler)
    server_thread = threading.Thread(target=server.serve_forever, daemon=True)
    server_thread.start()

    url = f"http://127.0.0.1:{server.server_address[1]}"
    console.print(f"[cyan]請在地圖視窗點選座標，網址: {url}[/cyan]")
    webbrowser.open(url)

    try:
        if not selected.wait(timeout=timeout_seconds):
            raise TimeoutError("Timed out waiting for map coordinate selection")
        return coordinate["lat"], coordinate["lng"]
    finally:
        server.shutdown()
        server.server_close()
        server_thread.join(timeout=1)

def read_exif_metadata(image_path: Path) -> ExifMetadata:
    with image_path.open("rb") as f:
        tags = exifread.process_file(f, details=False)

    dt_tag = tags.get("EXIF DateTimeOriginal") or tags.get("Image DateTime")
    raw_dt = str(getattr(dt_tag, "values", "")).strip() if dt_tag else None
    cap_local = None
    if raw_dt:
        try: cap_local = datetime.strptime(raw_dt, "%Y:%m:%d %H:%M:%S")
        except: pass

    off_tag = tags.get("EXIF OffsetTimeOriginal") or tags.get("EXIF OffsetTime")
    offset_time = str(getattr(off_tag, "values", "")).strip() if off_tag else None

    lat_tag, lat_ref = tags.get("GPS GPSLatitude"), tags.get("GPS GPSLatitudeRef")
    lon_tag, lon_ref = tags.get("GPS GPSLongitude"), tags.get("GPS GPSLongitudeRef")
    
    lat, lon = None, None
    if all([lat_tag, lat_ref, lon_tag, lon_ref]):
        lat = _ratio_to_float(lat_tag.values[0]) + _ratio_to_float(lat_tag.values[1]) / 60 + _ratio_to_float(lat_tag.values[2]) / 3600
        if str(lat_ref.values).upper() == 'S': lat *= -1
        lon = _ratio_to_float(lon_tag.values[0]) + _ratio_to_float(lon_tag.values[1]) / 60 + _ratio_to_float(lon_tag.values[2]) / 3600
        if str(lon_ref.values).upper() == 'W': lon *= -1

    return ExifMetadata(image_path, cap_local, raw_dt, offset_time, lat, lon)

def write_metadata(image_path: Path, plane: dict):
    summary = f"AeroSpotter: {plane['display']}"
    if image_path.suffix.lower() in RAW_EXTENSIONS:
        xmp_path = image_path.with_suffix('.xmp')
        with open(xmp_path, 'w', encoding='utf-8') as f:
            f.write(f'<?xpacket begin="" id="W5M0MpCehiHzreSzNTczkc9d"?><x:xmpmeta xmlns:x="adobe:ns:meta/"><rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"><rdf:Description rdf:about="" xmlns:dc="http://purl.org/dc/elements/1.1/"><dc:description><rdf:Alt><rdf:li xml:lang="x-default">{summary}</rdf:li></rdf:Alt></dc:description></rdf:Description></rdf:RDF></x:xmpmeta><?xpacket end="w"?>')
    else:
        exif_dict = piexif.load(str(image_path))
        comment = piexif.helper.UserComment.dump(summary, encoding='unicode')
        exif_dict['Exif'][piexif.ExifIFD.UserComment] = comment
        exif_dict['0th'][piexif.ImageIFD.ImageDescription] = summary.encode('utf-8')
        piexif.insert(piexif.dump(exif_dict), str(image_path))


def _remember_selected_candidate(candidate: dict) -> None:
    _upsert_known_hint(
        _normalize_icao(candidate.get("icao", "N/A")),
        str(candidate.get("callsign") or "N/A"),
        str(candidate.get("reg") or "N/A"),
        str(candidate.get("model") or "N/A"),
        str(candidate.get("owner") or "N/A"),
    )

def _resolve_location_context(exif: ExifMetadata, cached_loc: LocationContext | None) -> LocationContext:
    if exif.has_gps:
        tz = _TIMEZONE_FINDER.timezone_at(lat=exif.latitude, lng=exif.longitude)
        return LocationContext(exif.latitude, exif.longitude, tz, "GPS")

    if cached_loc:
        return cached_loc

    lat, lon = _select_coordinates_from_map()
    tz = _TIMEZONE_FINDER.timezone_at(lat=lat, lng=lon)
    if not tz:
        raise ValueError("Unable to determine timezone from selected coordinates")
    return LocationContext(lat, lon, tz, "MapSelection")


def _to_utc(exif: ExifMetadata, timezone_name: str) -> datetime:
    if exif.captured_at_local is None:
        raise ValueError(f"Missing capture time in {exif.image_path.name}")

    return exif.captured_at_local.replace(tzinfo=ZoneInfo(timezone_name)).astimezone(timezone.utc)


def _prompt_candidate(candidates: list[dict], image_name: str) -> dict | None:
    selected = questionary.select(
        f"請為 {image_name} 選擇正確航班：",
        choices=[questionary.Choice(candidate['display'], value=candidate) for candidate in candidates] + [questionary.Separator(), questionary.Choice("跳過此照片", value="__SKIP__")],
        style=custom_style,
    ).ask()

    if isinstance(selected, dict):
        return selected
    return None


@app.command("refresh-aircraft-db")
def refresh_aircraft_db() -> None:
    """Force-download the latest traffic aircraft database into local cache."""
    global traffic_db_disabled
    global traffic_db_initialized
    global traffic_db_frame

    try:
        traffic_data = importlib.import_module("traffic.data")
        aircraft_obj = getattr(traffic_data, "aircraft", None)
    except Exception as e:
        console.print(f"[red]無法載入 traffic: {e}[/red]")
        aircraft_obj = None

    if aircraft_obj is None:
        console.print("[red]traffic 未安裝，請先執行: pip install traffic pandas[/red]")
        raise typer.Exit(code=1)

    try:
        console.print("[cyan]正在下載最新版 traffic aircraft 資料庫...[/cyan]")
        if hasattr(aircraft_obj, "download"):
            aircraft_obj.download()
        elif hasattr(aircraft_obj, "download_opensky"):
            aircraft_obj.download_opensky()
        else:
            raise RuntimeError("Installed traffic version does not provide a download API")
        traffic_db_frame = aircraft_obj.data
        traffic_db_disabled = False
        traffic_db_initialized = True
        traffic_db_cache_by_icao.clear()
        traffic_db_cache_by_reg.clear()
        traffic_db_missing.clear()
        traffic_db_reg_missing.clear()
        console.print(f"[green]完成。可用筆數: {len(traffic_db_frame)}[/green]")
    except Exception as e:
        console.print(f"[red]更新 traffic 資料庫失敗: {e}[/red]")
        raise typer.Exit(code=1)


@app.command()
def process(target: Path = typer.Argument(...), recursive: bool = False):
    """Process one file or a folder of images and write aircraft metadata."""
    files = _collect_image_paths(target, recursive)

    hint_root = target.parent if target.is_file() else target
    loaded_hints = _load_local_hints(hint_root, recursive)
    if loaded_hints:
        console.print(f"  [dim]已載入本地標註提示: {loaded_hints} 筆[/dim]")

    cached_loc = None
    for idx, img in enumerate(files, 1):
        console.rule(f"[bold blue]({idx}/{len(files)}) {img.name}")
        exif = read_exif_metadata(img)

        cached_loc = _resolve_location_context(exif, cached_loc)
        utc_time = _to_utc(exif, cached_loc.timezone_name)
        console.print(f"  [dim]時區: {cached_loc.timezone_name} | UTC: {utc_time.strftime('%Y-%m-%d %H:%M:%S')}[/dim]")

        candidates = query_nas_history(cached_loc.latitude, cached_loc.longitude, utc_time)

        if not candidates:
            console.print("  [yellow]查無航班，跳過。[/yellow]")
            continue

        selected = _prompt_candidate(candidates, img.name)

        if selected:
            _remember_selected_candidate(selected)
            write_metadata(img, selected)
            console.print(f"  [green]✅ 已標註: {selected['callsign']}[/green]")

if __name__ == "__main__":
    app()