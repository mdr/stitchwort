import sys,re
for f in sys.argv[1:]:
    L=open(f,errors="replace").read().split("\n")
    out={}
    i=next(i for i,l in enumerate(L) if l.startswith("unit "))
    proj=[0,0];lib=None;core=None
    for l in L[i+1:]:
        if l.startswith("---"): continue
        if not l.strip(): break
        p=l.rsplit(None,4)
        if len(p)<5 or not re.match(r"^[\d.]+$",p[1]): break
        name=p[0].strip(); e,k=float(p[1]),float(p[2])
        if name.startswith("Aoc"): proj[0]+=e;proj[1]+=k
        if name=="library files": lib=(e,k)
        if name=="core": core=(e,k)
    w=next(l for l in L if l.startswith("wall"))
    m=re.match(r"wall ([\d.]+) ms; outside the units.*?([\d.]+) ms",w)
    d=next(i for i,l in enumerate(L) if l.startswith("declaration "))
    agg={}
    for l in L[d+1:]:
        if not l.strip(): break
        p=l.rsplit(None,7)
        key="Aoc" if p[0].startswith("Aoc") else ("Std" if p[0].startswith("Std") else "other")
        a=agg.setdefault(key,[0,0,0,0.0]); a[0]+=1; a[1]+=float(p[1]); a[2]+=float(p[2]); a[3]+=float(p[4])
    print(f.split("/")[-1], f"wall {m.group(1)} outside {m.group(2)} core {core} lib {lib} proj elab {proj[0]:.1f} kern {proj[1]:.1f}", {k:(v[0],round(v[1],1),round(v[2],1),f"{v[3]:.3g}") for k,v in agg.items()})
