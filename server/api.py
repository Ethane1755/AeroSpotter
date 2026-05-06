import os, sqlite3, sys, csv, gzip, urllib.request
import ujson as json
from datetime import datetime, timezone
from flask import Flask, request, jsonify

app = Flask(__name__)
DB_ROOT = "/data"

def ingest_from_stream(date_str, stream):
    db_path = f"{DB_ROOT}/{date_str}.db"
    if os.path.exists(db_path): os.remove(db_path)
    
    conn = sqlite3.connect(db_path)
    conn.execute("PRAGMA journal_mode=WAL")
    conn.execute("PRAGMA synchronous=OFF")
    cursor = conn.cursor()
    cursor.execute('CREATE TABLE IF NOT EXISTS traces (icao TEXT, flight TEXT, point_time REAL, lat REAL, lon REAL)')
    cursor.execute('CREATE TABLE IF NOT EXISTS aircraft_info (icao TEXT PRIMARY KEY, reg TEXT, type TEXT, owner TEXT)')

    import tarfile
    print(f"start {date_str}")
    
    try:
        with tarfile.open(fileobj=stream, mode="r|*") as tar:
            batch = []
            count = 0
            for member in tar:
                if member.isfile() and member.name.endswith(".json"):
                    f = tar.extractfile(member)
                    if f:
                        try:
                            compressed_data = f.read()
                            try:
                                raw_json = gzip.decompress(compressed_data)
                            except:
                                raw_json = compressed_data
                            
                            data = json.loads(raw_json)
                            icao = data.get("icao", "").lower()
                            base_ts = data.get("timestamp", 0)
                            
                            flight = "N/A"
                            for t in data.get("trace", []):
                                if len(t) > 8 and isinstance(t[8], dict) and "flight" in t[8]:
                                    f_val = t[8]["flight"].strip()
                                    if f_val:
                                        flight = f_val
                                        break  
                            for t in data.get("trace", []):
                                batch.append((icao, flight, base_ts + t[0], t[1], t[2]))
                        except:
                            continue
                
                if len(batch) >= 50000:
                    cursor.executemany('INSERT INTO traces VALUES (?,?,?,?,?)', batch)
                    conn.commit()
                    count += len(batch)
                    batch = []
                    print(f"  >  {count}")

            if batch:
                cursor.executemany('INSERT INTO traces VALUES (?,?,?,?,?)', batch)
                count += len(batch)

        print(f"Done. Processed {count} lines of data")
        
        print("Downloading VRS Database...")
        try:
            req = urllib.request.Request("https://raw.githubusercontent.com/vradarserver/standing-data/main/aircraft.csv", headers={'User-Agent': 'Mozilla/5.0'})
            with urllib.request.urlopen(req) as response:
                lines = [l.decode('utf-8') for l in response.readlines()]
                reader = csv.reader(lines)
                next(reader, None) 
                
                ac_batch = []
                for r in reader:
                    if len(r) > 8:
                        ac_batch.append((r[0].lower(), r[1], r[5], r[8]))
                
                cursor.executemany('INSERT OR REPLACE INTO aircraft_info VALUES (?,?,?,?)', ac_batch)
                print(f"  > Imported {len(ac_batch)} lines of data")
        except Exception as e:
            print(f"{e}")

        cursor.execute('CREATE INDEX idx_query ON traces(point_time, lat, lon)')
        conn.commit()
        print(f"✅ {date_str}.db is finished")
        
    except Exception as e:
        print(f"{e}")
    finally:
        conn.close()

@app.route('/api/adsb/bbox')
def get_bbox():
    bbox_str = request.args.get('bbox')
    start_str = request.args.get('start_time')
    end_str = request.args.get('end_time')
    if not all([bbox_str, start_str, end_str]): return jsonify({"error": "Missing params"}), 400

    target_date = start_str.split('T')[0]
    db_path = f"{DB_ROOT}/{target_date}.db"
    if not os.path.exists(db_path): return jsonify({"error": "No DB"}), 404

    min_lon, min_lat, max_lon, max_lat = map(float, bbox_str.split(','))
    start_ts = datetime.strptime(start_str, "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=timezone.utc).timestamp()
    end_ts = datetime.strptime(end_str, "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=timezone.utc).timestamp()

    conn = sqlite3.connect(db_path)
    cursor = conn.cursor()
    
    query = '''
        SELECT t.icao, t.flight, COALESCE(i.reg, 'N/A'), COALESCE(i.type, 'N/A'), COALESCE(i.owner, 'N/A')
        FROM traces t LEFT JOIN aircraft_info i ON t.icao = i.icao
        WHERE t.point_time BETWEEN ? AND ? AND t.lat BETWEEN ? AND ? AND t.lon BETWEEN ? AND ?
    '''
    cursor.execute(query, (start_ts, end_ts, min_lat, max_lat, min_lon, max_lon))
    
    results = []
    seen = set()
    for r in cursor.fetchall():
        if r[0] not in seen:
            results.append({"hex": r[0], "flight": r[1], "registration": r[2], "typecode": r[3], "owner": r[4]})
            seen.add(r[0])
    conn.close()
    return jsonify({"results": results})

if __name__ == '__main__':
    if len(sys.argv) > 1:
        ingest_from_stream(sys.argv[1], sys.stdin.buffer)
    else:
        app.run(host='0.0.0.0', port=5000)
