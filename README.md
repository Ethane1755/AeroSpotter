# Aircraft Identifier

This project annotates aircraft photos by combining:
- Radar history candidates (NAS API)
- Static/local aircraft database hints
- VLM fallback through MCP (Gemini)
- EXIF/XMP metadata writing

Main entrypoint is cli.py.

## Project Structure

- database/
  - Static reference data
  - Recommended large DB file: aircraft-database-complete-2025-08.csv.gz
- server/
  - api.py: NAS-side query API used by cli.py
  - ingest.sh: ingest ADS-B history into NAS SQLite DB
- test/
  - Sample images
- cli.py
  - Main process workflow (Radar -> VLM -> Metadata)
- Airplane_MCP.py
  - MCP server exposing analyze_airplane_image tool
- VLM.py
  - Standalone batch VLM test script

## Environment Setup

Recommended Python version: 3.12.x (stable and widely compatible with pandas/traffic).

If you use pyenv:

pyenv install 3.12.3
pyenv local 3.12.3

0. Create and use a project venv (recommended):

python3 -m venv .venv
.venv/bin/python -m pip install -U pip
.venv/bin/python -m pip install -r requirements.txt

1. Create or update .env (either key name works):

GEMINI_API_KEY=your_api_key

or

GOOGLE_API_KEY=your_api_key

2. CLI/MCP/VLM now auto-load .env from project root.

3. Make sure NAS API is reachable from your machine.

Important:

- Always run with .venv/bin/python.
- Using system python3 may miss packages (for example mcp, google-genai) and trigger fallback/manual flow.
- On Python 3.13+ (including dev/beta builds such as 3.14), traffic offline enrichment is automatically disabled by CLI for stability.

Optional VLM tuning:

VLM_MIN_SCORE=4
VLM_SCORE_MARGIN=2
VLM_MCP_TIMEOUT_SECONDS=20
VLM_DIRECT_TIMEOUT_SECONDS=25
VLM_DISABLE_AFTER_QUOTA=1
VLM_DISABLE_AFTER_TIMEOUT=1
VLM_ALLOW_LOW_CONF_AIRLINE_EXACT=1

- Lower VLM_MIN_SCORE to allow more aggressive auto-selection.
- Lower VLM_SCORE_MARGIN to reduce fallback to manual prompt when top scores are close.
- Lower VLM_MCP_TIMEOUT_SECONDS / VLM_DIRECT_TIMEOUT_SECONDS to avoid long hangs per image.
- Set VLM_DISABLE_AFTER_QUOTA=1 to stop further VLM calls in current run once 429 occurs.
- Set VLM_DISABLE_AFTER_TIMEOUT=1 to stop further VLM calls in current run once timeout occurs.
- Set VLM_ALLOW_LOW_CONF_AIRLINE_EXACT=1 to auto-select when airline exact match is unique and clearly dominant, even if score is one point below threshold.

## CLI Usage

Single image:

.venv/bin/python cli.py process test/294A9723.jpg

Process one folder:

.venv/bin/python cli.py process test

Process folder recursively:

.venv/bin/python cli.py process test --recursive

Refresh traffic local cache (optional):

.venv/bin/python cli.py refresh-aircraft-db

## Decision Flow in cli.py

For each image, cli.py does:

1. Read EXIF capture time and GPS.
2. Resolve timezone and convert local capture time to UTC.
3. Query NAS radar history candidates by bbox + time window.
4. Decision branch:
   - No candidate:
     - Call MCP tool analyze_airplane_image.
     - If VLM returns usable fields, create a VLM-only candidate and write metadata.
   - Exactly one candidate:
     - Auto-select directly.
   - Multiple candidates:
     - Call VLM and score each candidate by registration/airline/type matching.
     - If score is clear enough, auto-select.
     - Otherwise fallback to manual selection prompt.
5. Write metadata:
   - JPG/PNG: write EXIF comment/description.
   - RAW formats: write sidecar XMP.

## MCP / VLM Commands

Run VLM batch test only:

.venv/bin/python VLM.py

Run MCP server standalone:

.venv/bin/python Airplane_MCP.py

Run full integrated CLI flow:

.venv/bin/python cli.py process test

## Notes

- If GEMINI_API_KEY/GOOGLE_API_KEY is missing, VLM branch is skipped.
- If MCP client package is not installed, cli.py falls back to direct Gemini VLM call.
- If NAS returns no result and VLM also fails, image is skipped.
- If Gemini returns 429 RESOURCE_EXHAUSTED, VLM branch cannot decide until quota resets.
- Successful VLM results are cached at logs/vlm_cache.json to avoid repeated API calls for the same image.

## Decision Logs

- cli.py now writes decision traces to:
  - logs/vlm_decision.log
- Log includes:
  - VLM call start/fail reason
  - MCP raw response (truncated)
  - Candidate scores and reasons
  - Why it fell back to manual selection
  - Final selected result and metadata write status

Quick check during debugging:

tail -n 100 logs/vlm_decision.log

## Sidecar JSON Output

- cli.py now always writes a JSON sidecar next to each image.
- Example:
  - test/294A9723.jpg -> test/294A9723.json
- JSON is written for both selected and skipped cases.
- Common fields include:
  - status (selected/skipped)
  - image
  - captured_at_local
  - utc_time
  - location (lat/lon/timezone)
  - candidate_count
  - branch
  - selected (when status=selected)
