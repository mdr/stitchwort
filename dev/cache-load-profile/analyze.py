#!/usr/bin/env python3
"""Summarise a samply profile (`samply record --save-only
--unstable-presymbolicate -o P.json.gz`): CPU per function, self and
inclusive, weighted by each sample's CPU delta.

analyze.py P.json.gz [--top N] [--under REGEX] [--match REGEX]...
  --under REGEX   only samples with a frame matching REGEX on the stack
  --match REGEX   print the inclusive share of samples matching each REGEX
"""
import bisect, gzip, json, re, sys
from collections import defaultdict

def load(path):
    p = json.load(gzip.open(path))
    syms = json.load(open(path[: -len(".json.gz")] + ".json.syms.json"))
    strings = syms["string_table"]
    tables = {}
    for lib in syms["data"]:
        known = {a: i for a, i in lib["known_addresses"]}
        tables[lib["debug_name"]] = (known, lib["symbol_table"])
    return p, strings, tables

def main():
    a = sys.argv[1:]
    path = a.pop(0)
    top, under, matches = 40, None, []
    while a:
        f = a.pop(0)
        if f == "--top": top = int(a.pop(0))
        elif f == "--under": under = re.compile(a.pop(0))
        elif f == "--match": matches.append(a.pop(0))
    p, strings, tables = load(path)
    libs = [l["debugName"] if "debugName" in l else l["name"] for l in p["libs"]]
    self_t, incl = defaultdict(float), defaultdict(float)
    mt = defaultdict(float)
    total = 0.0
    for t in p["threads"]:
        st, ft, fn, rt, sa = t["stackTable"], t["frameTable"], t["funcTable"], t["resourceTable"], t["stringArray"]
        def fname(fr):
            func = ft["func"][fr]
            res = fn["resource"][func]
            addr = ft["address"][fr]
            if res is not None and res >= 0:
                lib = sa[rt["name"][res]]
                if lib in tables and addr >= 0:
                    known, symtab = tables[lib]
                    if addr in known:
                        return strings[symtab[known[addr]]["symbol"]]
            return sa[fn["name"][func]]
        names = [fname(i) for i in range(ft["length"])]
        cache = {}
        def chain(s):
            if s in cache: return cache[s]
            out = []
            while s is not None:
                out.append(names[st["frame"][s]]); s = st["prefix"][s]
            cache[s] = out
            return out
        sm = t["samples"]
        w = sm.get("threadCPUDelta") or sm.get("weight") or [1] * sm["length"]
        for s, cpu in zip(sm["stack"], w):
            if s is None or cpu is None: continue
            c = chain(s)
            if under and not any(under.search(n) for n in c): continue
            total += cpu
            self_t[c[0]] += cpu
            for n in set(c): incl[n] += cpu
            for m in matches:
                if any(re.search(m, n) for n in c): mt[m] += cpu
    print(f"total {total/1e6:.3f} s CPU (threadCPUDelta in us)")
    for m in matches:
        print(f"  {mt[m]/1e6:7.3f} s {100*mt[m]/total:5.1f}%  {m}")
    print("\n-- inclusive --")
    for n, v in sorted(incl.items(), key=lambda kv: -kv[1])[:top]:
        print(f"{v/1e6:7.3f} {100*v/total:5.1f}%  {n[:160]}")
    print("\n-- self --")
    for n, v in sorted(self_t.items(), key=lambda kv: -kv[1])[:top]:
        print(f"{v/1e6:7.3f} {100*v/total:5.1f}%  {n[:160]}")

main()
