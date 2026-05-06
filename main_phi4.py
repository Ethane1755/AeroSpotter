from __future__ import annotations

import json
import os
from pathlib import Path
from typing import Any

import requests

import main as core

ORIGINAL_SELECT_BY_VLM = core._select_candidate_by_vlm

# Local phi-4 (OpenAI-compatible endpoint, e.g. Ollama)
PHI4_BASE_URL = os.environ.get("PHI4_BASE_URL", "http://localhost:11434/v1").rstrip("/")
PHI4_MODEL = os.environ.get("PHI4_MODEL", "phi4:latest")
PHI4_TIMEOUT_SECONDS = int(os.environ.get("PHI4_TIMEOUT_SECONDS", "45"))
PHI4_MAX_CANDIDATES = int(os.environ.get("PHI4_MAX_CANDIDATES", "25"))
PHI4_ALLOW_GEMINI_FALLBACK = os.environ.get("PHI4_ALLOW_GEMINI_FALLBACK", "0") == "1"
PHI4_USE_VLM_HINT = os.environ.get("PHI4_USE_VLM_HINT", "1") == "1"


def _extract_json_block(text: str) -> dict[str, Any] | None:
    raw = (text or "").strip()
    if not raw:
        return None

    # 1) direct json parse
    try:
        parsed = json.loads(raw)
        if isinstance(parsed, dict):
            return parsed
    except json.JSONDecodeError:
        pass

    # 2) fenced JSON
    cleaned = raw.replace("```json", "").replace("```", "").strip()
    try:
        parsed = json.loads(cleaned)
        if isinstance(parsed, dict):
            return parsed
    except json.JSONDecodeError:
        pass

    # 3) greedy object extraction
    start = cleaned.find("{")
    end = cleaned.rfind("}")
    if start >= 0 and end > start:
        snippet = cleaned[start : end + 1]
        try:
            parsed = json.loads(snippet)
            if isinstance(parsed, dict):
                return parsed
        except json.JSONDecodeError:
            return None

    return None


def _call_local_phi4(messages: list[dict[str, str]]) -> dict[str, Any] | None:
    url = f"{PHI4_BASE_URL}/chat/completions"
    payload = {
        "model": PHI4_MODEL,
        "messages": messages,
        "temperature": 0.1,
        "response_format": {"type": "json_object"},
    }

    response = requests.post(url, json=payload, timeout=PHI4_TIMEOUT_SECONDS)
    response.raise_for_status()

    data = response.json()
    choices = data.get("choices") or []
    if not choices:
        return None

    content = (((choices[0] or {}).get("message") or {}).get("content") or "").strip()
    return _extract_json_block(content)


def _trim_candidates(candidates: list[dict]) -> list[dict]:
    if len(candidates) <= PHI4_MAX_CANDIDATES:
        return candidates
    return candidates[:PHI4_MAX_CANDIDATES]


def _select_candidate_by_phi4(candidates: list[dict], image_path: Path) -> dict | None:
    if not candidates:
        return None

    active_candidates = _trim_candidates(candidates)

    # In main.py flow, this selector is entered only after multi-candidate OCR step
    # already failed to auto-match, so we avoid rerunning heavy OCR here.
    ocr_marks: list[str] = []

    # Use Gemini/MCP hint by default so phi-4 gets visual cues when OCR has no hit.
    vlm_result: dict[str, str] | None = None
    if PHI4_USE_VLM_HINT:
        vlm_result = core._safe_call_mcp_vlm(image_path, active_candidates)

    candidate_payload = [
        {
            "idx": idx,
            "icao": c.get("icao"),
            "callsign": c.get("callsign"),
            "registration": c.get("reg"),
            "aircraft_type": c.get("model"),
            "airline": c.get("owner"),
        }
        for idx, c in enumerate(active_candidates)
    ]

    system_prompt = (
        "You are an aviation identity resolver. "
        "Pick the best candidate from the provided list using evidence only. "
        "Return strict JSON with keys: selected_idx, confidence, reason. "
        "If uncertain, set selected_idx to -1."
    )

    user_prompt = json.dumps(
        {
            "image": str(image_path),
            "vlm_hint": vlm_result,
            "ocr_marks": ocr_marks,
            "candidates": candidate_payload,
            "constraints": {
                "prefer_exact_registration_match": True,
                "prefer_callsign_and_airline_consistency": True,
                "prefer_aircraft_type_consistency": True,
            },
        },
        ensure_ascii=False,
    )

    try:
        decision = _call_local_phi4(
            [
                {"role": "system", "content": system_prompt},
                {"role": "user", "content": user_prompt},
            ]
        )
    except Exception as exc:
        core._decision_log(f"phi-4 decision call failed: {exc}", image_path, level="WARN")
        if PHI4_ALLOW_GEMINI_FALLBACK:
            return ORIGINAL_SELECT_BY_VLM(candidates, image_path)
        return None

    if not decision:
        core._decision_log("phi-4 returned empty decision", image_path, level="WARN")
        if PHI4_ALLOW_GEMINI_FALLBACK:
            return ORIGINAL_SELECT_BY_VLM(candidates, image_path)
        return None

    try:
        selected_idx = int(decision.get("selected_idx", -1))
    except Exception:
        selected_idx = -1

    confidence = decision.get("confidence")
    reason = str(decision.get("reason") or "")
    core._decision_log(
        f"phi-4 decision selected_idx={selected_idx} confidence={confidence} reason={reason[:180]}",
        image_path,
    )

    if 0 <= selected_idx < len(active_candidates):
        selected = active_candidates[selected_idx]
        core._decision_log(
            f"phi-4 selected callsign={selected.get('callsign')} reg={selected.get('reg')}",
            image_path,
        )
        return selected

    if PHI4_ALLOW_GEMINI_FALLBACK:
        return ORIGINAL_SELECT_BY_VLM(candidates, image_path)

    return None


# Monkey-patch core selection path so `process` keeps same behavior/CLI surface.
core._select_candidate_by_vlm = _select_candidate_by_phi4


if __name__ == "__main__":
    core.app()
