#!/bin/bash

DATE_INPUT=$1
if [ -z "$DATE_INPUT" ]; then
    echo "use ./ingest.sh 2026-04-17"
    exit 1
fi

YYYY=$(echo $DATE_INPUT | cut -d'-' -f1)
MM=$(echo $DATE_INPUT | cut -d'-' -f2)
DD=$(echo $DATE_INPUT | cut -d'-' -f3)
TAG="v${YYYY}.${MM}.${DD}-planes-readsb-prod-0"
BASE_URL="https://github.com/adsblol/globe_history_${YYYY}/releases/download/${TAG}"
FILE_AA="${BASE_URL}/${TAG}.tar.aa"
FILE_AB="${BASE_URL}/${TAG}.tar.ab"

if ! command -v pv &> /dev/null; then
    MONITOR="cat"
else
    MONITOR="pv"
fi

wget -qO- "$FILE_AA" "$FILE_AB" | $MONITOR | docker exec -i adsb_api_server python api.py "$DATE_INPUT"

if [ $? -eq 0 ]; then
    echo "------------------------------------------------"
    echo "$DATE_INPUT data processing done"
    echo "Database location: ./data/${DATE_INPUT}.db"
else
    echo "------------------------------------------------"
    echo "Error, please check connection"
fi
