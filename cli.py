from __future__ import annotations

import math
import requests
import airportsdata
import exifread
import piexif
import piexif.helper
import typer
import questionary
import concurrent.futures
from dataclasses import dataclass
from datetime import datetime, timedelta, timezone
from pathlib import Path
from re import compile
from typing import Any
from zoneinfo import ZoneInfo
from timezonefinder import TimezoneFinder
from rich.console import Console
from rich.prompt import Prompt
from questionary import Style

# ==========================================
# 1. 配置與全域變數
# ==========================================
app = typer.Typer(help="AeroSpotter CLI (Home Lab NAS Edition)")
console = Console()

# 💡 請修改為你 TrueNAS 伺服器的 IP
NAS_API_URL = "http://100.109.73.11:5000/api/adsb/bbox"

# 💡 設定最佳化時間視窗 (前後各 5 分鐘)
BUFFER_MINUTES = 5

# 💡 常見航空公司呼號對照表 (用於拯救 HexDB 也查不到的新飛機)
AIRLINE_PREFIXES = {
    "EVA": "Eva Air", "CAL": "China Airlines", "SJX": "Starlux Airlines",
    "TTW": "Tigerair Taiwan", "MDA": "Mandarin Airlines", "UIA": "UNI Air",
    "HKE": "HK Express", "CPA": "Cathay Pacific", "CRK": "Hong Kong Airlines",
    "JJA": "Jeju Air", "TWB": "T'way Air", "KAL": "Korean Air", "AAR": "Asiana Airlines",
    "MAS": "Malaysia Airlines", "MXD": "Malindo Air", "CSC": "Sichuan Airlines",
    "TLM": "Thai Lion Air", "CSN": "China Southern", "CES": "China Eastern"
}

_EXTS = [".jpg", ".jpeg", ".png", ".cr2", ".nef", ".arw", ".dng", ".raf"]
SUPPORTED_EXTENSIONS = {ext.lower() for ext in _EXTS} | {ext.upper() for ext in _EXTS}
RAW_EXTENSIONS = {ext for ext in SUPPORTED_EXTENSIONS if ext.lower() not in [".jpg", ".jpeg", ".png"]}
_TIMEZONE_FINDER = TimezoneFinder(in_memory=True)

live_ac_cache = {}

custom_style = Style([
    ('qmark', 'fg:#00ffff bold'),
    ('question', 'bold'),
    ('answer', 'fg:#00ff00 bold'),
    ('pointer', 'fg:#ff00ff bold'),
    ('highlighted', 'fg:#00ffff bold'),
    ('selected', 'fg:#cc5454'),
    ('instruction', 'fg:#888888 italic')
])

# ==========================================
# 2. 資料結構
# ==========================================
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

# ==========================================
# 3. 核心邏輯
# ==========================================

def get_live_aircraft_info(icao: str) -> dict:
    """從雲端 HexDB 抓取詳細身分證資訊 (由多執行緒呼叫)"""
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
    except: pass
    return {"reg": "N/A", "type": "N/A", "airline": "N/A", "mfr": "", "year": ""}

def query_nas_history(latitude: float, longitude: float, time_utc: datetime) -> list[dict]:
    """向 NAS 查詢並發動多執行緒補完資料"""
    delta_lat = 15.0 / 111.0
    delta_lon = 15.0 / (111.0 * math.cos(math.radians(latitude)))
    bbox = f"{longitude-delta_lon:.4f},{latitude-delta_lat:.4f},{longitude+delta_lon:.4f},{latitude+delta_lat:.4f}"
    
    start_time = (time_utc - timedelta(minutes=BUFFER_MINUTES)).strftime("%Y-%m-%dT%H:%M:%SZ")
    end_time = (time_utc + timedelta(minutes=BUFFER_MINUTES)).strftime("%Y-%m-%dT%H:%M:%SZ")

    try:
        resp = requests.get(NAS_API_URL, params={"bbox": bbox, "start_time": start_time, "end_time": end_time}, timeout=10)
        resp.raise_for_status()
        raw_results = resp.json().get("results", [])

        # 💡 資工系魔法：使用 ThreadPoolExecutor 同步發送網路請求，徹底消除卡頓
        def enrich_data(f):
            icao = f.get("hex", "N/A").lower()
            callsign = f.get("flight", "N/A").strip()
            reg = str(f.get('registration') or 'N/A').strip()
            model = str(f.get('typecode') or 'N/A').strip()
            owner = str(f.get('owner') or 'N/A').strip()

            if reg in ['N/A', ''] or model in ['N/A', '']:
                live = get_live_aircraft_info(icao)
                if live['reg'] != 'N/A':
                    reg = f"{live['reg']}*"
                    owner = live['airline']
                    model = f"{live['mfr']} {live['type']}"
                    if live['year']: model += f" ({live['year']})"

            if owner == "N/A" and callsign != "N/A":
                prefix = callsign[:3].upper()
                owner = f"{AIRLINE_PREFIXES.get(prefix, 'N/A')} (?)"

            return {
                "icao": icao, "callsign": callsign, "reg": reg,
                "display": f"{callsign:<8} | Reg: {reg:<8} | Model: {model:<28} | Airline: {owner}"
            }

        with concurrent.futures.ThreadPoolExecutor(max_workers=10) as executor:
            candidates = list(executor.map(enrich_data, raw_results))

        candidates.sort(key=lambda x: (x['callsign'] == 'N/A', x['reg'] == 'N/A', x['callsign']))
        return candidates
    except Exception as e:
        console.print(f"[red]NAS 查詢失敗: {e}[/red]")
        return []

# ==========================================
# 4. EXIF 處理與寫入
# ==========================================

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
        def to_f(v): return float(v.num)/float(v.den)
        lat = to_f(lat_tag.values[0]) + to_f(lat_tag.values[1])/60 + to_f(lat_tag.values[2])/3600
        if str(lat_ref.values).upper() == 'S': lat *= -1
        lon = to_f(lon_tag.values[0]) + to_f(lon_tag.values[1])/60 + to_f(lon_tag.values[2])/3600
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

# ==========================================
# 5. CLI 主程式
# ==========================================
@app.command()
def process(target: Path = typer.Argument(...), recursive: bool = False):
    """資工系專屬 AeroSpotter：自動時區、併發補完、精準標註"""
    files = [target] if target.is_file() else sorted([p for p in (target.rglob("*") if recursive else target.iterdir()) if p.suffix in SUPPORTED_EXTENSIONS])
    
    cached_loc = None
    for idx, img in enumerate(files, 1):
        console.rule(f"[bold blue]({idx}/{len(files)}) {img.name}")
        exif = read_exif_metadata(img)
        
        # 💡 自動時區判定邏輯
        if exif.has_gps:
            tz = _TIMEZONE_FINDER.timezone_at(lat=exif.latitude, lng=exif.longitude)
            cached_loc = LocationContext(exif.latitude, exif.longitude, tz, "GPS")
        elif not cached_loc:
            code = Prompt.ask("[yellow]無 GPS，請輸入機場代碼 (如 TPE)[/yellow]")
            db = airportsdata.load('IATA')
            airport = db.get(code.upper())
            tz = _TIMEZONE_FINDER.timezone_at(lat=airport['lat'], lng=airport['lon'])
            cached_loc = LocationContext(airport['lat'], airport['lon'], tz, f"Airport:{code}")

        # 時間處理
        utc_time = exif.captured_at_local.replace(tzinfo=ZoneInfo(cached_loc.timezone_name)).astimezone(timezone.utc)
        console.print(f"  [dim]時區: {cached_loc.timezone_name} | UTC: {utc_time.strftime('%Y-%m-%d %H:%M:%S')}[/dim]")

        candidates = query_nas_history(cached_loc.latitude, cached_loc.longitude, utc_time)
        
        if not candidates:
            console.print("  [yellow]查無航班，跳過。[/yellow]")
            continue

        selected = questionary.select(
            "請選擇正確航班：",
            choices=[questionary.Choice(c['display'], value=c) for c in candidates] + [questionary.Separator(), questionary.Choice("跳過此照片", value=None)],
            style=custom_style
        ).ask()

        if selected:
            write_metadata(img, selected)
            console.print(f"  [green]✅ 已標註: {selected['callsign']}[/green]")

if __name__ == "__main__":
    app()