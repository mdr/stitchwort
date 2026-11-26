"""Parse `check --timings=all` stderr into CSVs and a summary.

The "steps by phase" table is optional: it is printed only when
STITCHWORT_STEP_PHASES=1. Without it the units and declarations are parsed as
usual, phases.csv gets only its header, and the summary says so.
"""
import csv, sys
from pathlib import Path
src, out = Path(sys.argv[1]), Path(sys.argv[2])
out.mkdir(parents=True, exist_ok=True)
L = src.read_text(errors="replace").split("\n")
def find(prefix, start=0, optional=False):
    for i in range(start, len(L)):
        if L[i].startswith(prefix): return i
    if optional: return None
    raise SystemExit(f"no {prefix}")
def rows(start, ncols):
    res = []
    for l in L[start:]:
        if not l.strip(): break
        parts = l.rstrip().rsplit(None, ncols)
        if len(parts) != ncols + 1: break
        try: nums = [float(x) for x in parts[1:]]
        except ValueError: break
        res.append([parts[0].strip()] + nums)
    return res
u = find("unit "); units = rows(u + 1, 4)
d = find("declaration "); decls = rows(d + 1, 7)
p = find("steps by phase", optional=True)
phases = rows(p + 1, 6) if p is not None else []
for name, hdr, data in [("units", "unit,elab_ms,kernel_ms,nodes,decls", units),
                        ("decls", "decl,elab_ms,kernel_ms,total_ms,steps,nodes,readback_nodes,frames", decls),
                        ("phases", "decl,steps,walk,unify,apply,readback,other", phases)]:
    with open(out / f"{name}.csv", "w", newline="") as f:
        w = csv.writer(f); w.writerow(hdr.split(",")); w.writerows(data)
print("units", len(units), "decls", len(decls), "phases", len(phases))
if not phases:
    print("no steps-by-phase table: STITCHWORT_STEP_PHASES was not set; phases.csv has only its header")
tot = sum(r[3] for r in decls); el = sum(r[1] for r in decls); ke = sum(r[2] for r in decls)
print(f"decl total {tot/1000:.1f}s elab {el/1000:.1f}s kernel {ke/1000:.1f}s")
s = sorted(decls, key=lambda r: -r[3])
n = len(s); acc = 0
for k, r in enumerate(s, 1):
    acc += r[3]
    for frac in (0.5, 0.8, 0.9):
        if acc - r[3] < frac * tot <= acc: print(f"{frac:.0%} of time in top {k} decls ({k/n:.2%})")
for cut in (1, 5, 10, 20, 50, 100):
    print(f"top {cut}: {sum(r[3] for r in s[:cut])/tot:.1%}")
print(f"top 1% ({n//100}): {sum(r[3] for r in s[:n//100])/tot:.1%}; top 5%: {sum(r[3] for r in s[:n//20])/tot:.1%}")
under = [r for r in decls if r[3] < 10]
print(f"decls under 10 ms: {len(under)} = {sum(r[3] for r in under)/1000:.1f}s")
if phases:
    ph = [sum(r[i] for r in phases) for i in range(1, 7)]
    print("steps total %.3g; walk %.1f%% unify %.1f%% apply %.1f%% readback %.1f%% other %.1f%%" % (ph[0], *[100*x/ph[0] for x in ph[1:]]))
else:
    print("steps by phase not recorded (STITCHWORT_STEP_PHASES was not set)")
print("top 20:")
for r in s[:20]: print(f"  {r[0][:70]:70} elab {r[1]:9.0f} kern {r[2]:8.0f} tot {r[3]:9.0f} steps {r[4]:.3g} rb {r[6]:.3g}")
