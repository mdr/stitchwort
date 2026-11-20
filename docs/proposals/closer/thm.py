import sys, re, os, random, json
ROOT=os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..', '..'))
def theorems(path):
    out=[]; lines=open(path).read().split('\n'); i=0
    while i<len(lines):
        m=re.match(r'\s*theorem\s+([A-Za-z0-9_.]+)', lines[i])
        if m:
            j=i
            while j<len(lines) and lines[j].strip()!='': j+=1
            out.append((m.group(1), i+1, lines[i:j]))
            i=j
        else: i+=1
    return out
def allfiles(dirs):
    for d in dirs:
        for r,_,fs in os.walk(os.path.join(ROOT,d)):
            if '/Tests' in r: continue
            for f in fs:
                if f.endswith('.sw'): yield os.path.join(r,f)
if __name__=='__main__':
    cmd=sys.argv[1]
    if cmd=='show':
        names=set(sys.argv[3:]); 
        for p in allfiles([sys.argv[2]]):
            for n,l,b in theorems(p):
                if n in names:
                    print(f'### {os.path.relpath(p,ROOT)}:{l} {n} ({len(b)} lines)'); print('\n'.join(b)); print()
    if cmd=='stats':
        tot=0; n=0
        for p in allfiles(sys.argv[2:]):
            for nm,l,b in theorems(p): tot+=len(b); n+=1
        print(n,tot)
