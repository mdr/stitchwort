import json,sys,statistics as s
for r in json.load(open(sys.argv[1]))['results']:
    t=[m['time_wall_clock']['value'] for m in r['measurements']]
    print(f"{r['name']:12} median {s.median(t)*1000:6.0f} ms  min {min(t)*1000:6.0f}  max {max(t)*1000:6.0f}")
