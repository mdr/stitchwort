import json,sys,os,glob,re
P=sys.argv[1]; out=[]
for f in glob.glob(P+'/agent-*.jsonl'):
    if os.path.getmtime(f) < 1795109400: continue  # 19 Nov 2026 17:30 UTC
    meta={}
    try: meta=json.load(open(f[:-6]+'.meta.json'))
    except Exception: pass
    seen={}; first=None; last=None; prompt=''
    for l in open(f):
        try: d=json.loads(l)
        except Exception: continue
        ts=d.get('timestamp')
        if ts:
            first=first or ts; last=ts
        m=d.get('message')
        if not isinstance(m,dict): continue
        if not prompt and m.get('role')=='user':
            c=m.get('content'); prompt=c if isinstance(c,str) else json.dumps(c)
            prompt=prompt[:300]
        u=m.get('usage')
        if u and m.get('id'):
            seen[m['id']]=(u.get('output_tokens',0), u.get('input_tokens',0)+u.get('cache_creation_input_tokens',0), u.get('cache_read_input_tokens',0), m.get('model'))
    if not first or first < '2026-11-19T17:30': continue
    out.append(dict(desc=meta.get('description',''), type=meta.get('agentType',''), first=first,last=last,
        out=sum(v[0] for v in seen.values()), inp=sum(v[1] for v in seen.values()), cache=sum(v[2] for v in seen.values()),
        model=next((v[3] for v in seen.values()),''), prompt=prompt))
json.dump(out,open(sys.argv[2],'w'))
print(len(out))
