import sys
log,only=sys.argv[1],set(open(sys.argv[2]).read().strip().split(","))
L=open(log,errors="replace").read().split("\n")
d=next(i for i,l in enumerate(L) if l.startswith("declaration "))
rows=[]
for l in L[d+1:]:
    if not l.strip(): break
    p=l.rsplit(None,7); rows.append((p[0].strip(),*map(float,p[1:])))
p=next(i for i,l in enumerate(L) if l.startswith("steps by phase"))
ph={}
for l in L[p+1:]:
    if not l.strip(): break
    q=l.rsplit(None,6); ph[q[0].strip()]=list(map(float,q[1:]))
def kind(n):
    if n in only: return "ported theorem"
    if n.startswith("Aoc"): return "other own decl"
    return "std/core"
agg={}
for r in rows:
    k=kind(r[0]); a=agg.setdefault(k,[0,0,0,0,0,0,0,0])
    a[0]+=1;a[1]+=r[1];a[2]+=r[2];a[3]+=r[4];a[4]+=r[5]
    if r[0] in ph:
        a[5]+=ph[r[0]][4]; a[6]+=ph[r[0]][2]; a[7]+=ph[r[0]][5]
for k,a in agg.items(): print(f"{k:16} n={a[0]:4d} elab {a[1]:7.1f} kern {a[2]:6.1f} steps {a[3]:.3g} nodes {a[4]:.3g} readback-steps {a[5]/max(a[3],1):.0%} unify {a[6]/max(a[3],1):.0%} other {a[7]/max(a[3],1):.0%}")
own=[r for r in rows if r[0].startswith("Aoc")]
own.sort(key=lambda r:-r[3])
tot=sum(r[3] for r in own)
print(f"own total {tot:.1f} ms; per-decl median {sorted(r[3] for r in own)[len(own)//2]:.2f} ms; under 1 ms: {sum(1 for r in own if r[3]<1)} decls = {sum(r[3] for r in own if r[3]<1):.1f} ms")
for r in own[:int(sys.argv[3]) if len(sys.argv)>3 else 12]:
    print(f"  {'T' if r[0] in only else ' '} {r[0][:62]:62} elab {r[1]:6.1f} kern {r[2]:5.1f} tot {r[3]:6.1f} steps {r[4]:9.0f} nodes {r[5]:7.0f} rb {r[6]:5.0f}")
