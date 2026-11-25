"""Summarise samply profiles of short `stitchwort check` runs.

Input: one or more samply profiles in Firefox's profiler JSON format, either
`PROFILE.json.gz` or `PROFILE.json`, optionally each with a
`PROFILE.json.syms.json` sidecar that maps addresses in system libraries to
symbol names. Every thread of every file given is summed.

Run it with:

    nix shell nixpkgs#python3 -c python3 -I dev/prof-summary.py --top 10 PROFILE.json.gz...

Options: --top N, --under FRAME, --children FRAME, --phases, --rate SAMPLES_PER_SECOND.
"""
import bisect, gzip, json, sys, argparse
from collections import Counter

ap = argparse.ArgumentParser()
ap.add_argument("paths", nargs="+")
ap.add_argument("--top", type=int, default=40)
ap.add_argument("--under", default=None, help="only samples with this frame substring on the stack")
ap.add_argument("--children", default=None, help="inclusive time of the direct callees of the first frame matching")
ap.add_argument("--phases", action="store_true")
ap.add_argument("--rate", type=float, default=4000.0)
o = ap.parse_args()


def load(path):
    prof = json.load(gzip.open(path) if path.endswith(".gz") else open(path))
    try:
        syms = json.load(open(path.removesuffix(".gz") + ".syms.json"))
    except OSError:
        syms = None
    lookup = {}
    if syms:
        strings = syms["string_table"]
        for d in syms["data"]:
            entries = sorted((e["rva"], strings[e["symbol"]]) for e in d["symbol_table"])
            lookup[d["debug_name"]] = ([e[0] for e in entries], entries)
    return prof, lookup


def short(n):
    if "::h" in n and len(n.rsplit("::h", 1)[1]) == 16:
        n = n.rsplit("::h", 1)[0]
    return n


stacks = []  # (list of frame names leaf-first, weight)
for path in o.paths:
    prof, lookup = load(path)
    libs = prof.get("libs", [])
    gstrings = prof.get("shared", {}).get("stringArray")
    for th in prof["threads"]:
        strings = th.get("stringArray", gstrings)
        ft, fr, st = th["funcTable"], th["frameTable"], th["stackTable"]
        res = th.get("resourceTable")

        def name_of(f):
            fn = fr["func"][f]
            n = strings[ft["name"][fn]]
            if n.startswith("0x") and res is not None:
                r = ft["resource"][fn]
                if r is not None and r >= 0:
                    lib = libs[res["lib"][r]]["debugName"]
                    t = lookup.get(lib)
                    addr = fr["address"][f] if fr.get("address") else int(n, 16)
                    if t:
                        i = bisect.bisect_right(t[0], addr) - 1
                        if i >= 0:
                            return short(t[1][i][1])
            return short(n)

        cache = {}

        def chain(s):
            if s in cache:
                return cache[s]
            out, k = [], s
            while k is not None:
                out.append(name_of(st["frame"][k]))
                k = st["prefix"][k]
            cache[s] = out
            return out

        samples = th["samples"]["stack"]
        weights = th["samples"].get("weight") or [1] * len(samples)
        for s, w in zip(samples, weights):
            if s is not None:
                stacks.append((chain(s), w))

stacks = [(c, w) for c, w in stacks if c[0] not in ("__sigwait", "__ulock_wait", "__workq_kernreturn", "__psynch_cvwait", "mach_msg2_trap")]
if o.under:
    stacks = [(c, w) for c, w in stacks if any(o.under in f for f in c)]
tot = sum(w for _, w in stacks)
ms = 1000.0 / o.rate / len(o.paths)
print(f"samples {tot}, {tot*ms:.1f} ms per run (over {len(o.paths)} runs)")

if o.phases:
    PH = [
        ("std index (cached read)", ["LibraryIndex", "index_cache", "IndexCache"]),
        ("project analyse / scan", ["project::analyse", "analyse_parsed", "ReadOnce", "scan"]),
        ("plan skips (entry heads)", ["plan_skips", "plan_namespace", "plan_entry"]),
        ("library entry load", ["load_needs"]),
        ("project namespace replay", ["check_project_namespace"]),
        ("core prelude", ["Session::start", "start_in", "elaborate_module"]),
        ("exit / drop", ["drop_in_place", "discard"]),
    ]
    pc = Counter()
    for c, w in stacks:
        j = "\n".join(c)
        g = "other"
        for name, ks in PH:
            if any(k in j for k in ks):
                g = name
                break
        pc[g] += w
    for g, v in pc.most_common():
        print(f"{100*v/tot:5.1f}%  {v*ms:7.1f} ms  {g}")

if o.children:
    kids = Counter()
    for c, w in stacks:
        rev = c[::-1]
        for i, f in enumerate(rev):
            if o.children in f:
                kids[rev[i + 1] if i + 1 < len(rev) else "(self)"] += w
                break
    sub = sum(kids.values())
    print(f"== under {o.children}: {sub*ms:.1f} ms")
    for k, v in kids.most_common(o.top):
        print(f"{v*ms:7.1f} ms  {k[:160]}")
else:
    incl, selfc = Counter(), Counter()
    for c, w in stacks:
        selfc[c[0]] += w
        for f in set(c):
            incl[f] += w
    print("== inclusive")
    for k, v in incl.most_common(o.top):
        print(f"{100*v/tot:5.1f}% {v*ms:7.1f} ms  {k[:150]}")
    print("== self")
    for k, v in selfc.most_common(o.top):
        print(f"{100*v/tot:5.1f}% {v*ms:7.1f} ms  {k[:150]}")
