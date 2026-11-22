"""Summarise a samply profile (Firefox processed format + .syms.json sidecar):
self time and inclusive time by function, for the busiest thread."""
import bisect, gzip, json, sys
from collections import Counter

path = sys.argv[1]
top = int(sys.argv[2]) if len(sys.argv) > 2 else 40
prof = json.load(gzip.open(path) if path.endswith(".gz") else open(path))
syms_path = path.removesuffix(".gz") + ".syms.json"
try:
    syms = json.load(open(syms_path))
except OSError:
    syms = None

# Address -> name lookup per library, from the sidecar.
lookup = {}
if syms:
    strings = syms["string_table"]
    for d in syms["data"]:
        entries = sorted((e["rva"], e["size"], strings[e["symbol"]]) for e in d["symbol_table"])
        lookup[d["debug_name"]] = ([e[0] for e in entries], entries)

def name_of(lib, addr):
    t = lookup.get(lib)
    if not t:
        return f"{lib}+{addr:#x}"
    starts, entries = t
    i = bisect.bisect_right(starts, addr) - 1
    if i >= 0:
        return entries[i][2]
    return f"{lib}+{addr:#x}"

libs = prof.get("libs", [])
shared = prof.get("shared", {})
gstrings = shared.get("stringArray")
threads = prof["threads"]
th = max(threads, key=lambda t: t["samples"]["length"])
strings = th.get("stringArray", gstrings)
ft, fr, st = th["funcTable"], th["frameTable"], th["stackTable"]
res = th.get("resourceTable")

func_names = []
for i in range(ft["length"]):
    n = strings[ft["name"][i]]
    if n.startswith("0x") and res is not None and ft["resource"][i] is not None and ft["resource"][i] >= 0:
        lib = libs[res["lib"][ft["resource"][i]]]
        n = name_of(lib["debugName"], int(n, 16))
    func_names.append(n)

frame_func = fr["func"]
frame_addr = fr.get("address")
def frame_name(f):
    fn = frame_func[f]
    n = func_names[fn]
    if n.startswith("0x") or "+0x" in n:
        pass
    # Frames whose function is an unresolved address: resolve by frame address.
    if (n.startswith("0x")) and frame_addr is not None and res is not None:
        r = ft["resource"][fn]
        if r is not None and r >= 0:
            lib = libs[res["lib"][r]]
            return name_of(lib["debugName"], frame_addr[f])
    return n

cache = {}
def short(n):
    if n in cache:
        return cache[n]
    s = n
    # demangled Rust names: drop the hash suffix
    if "::h" in s and len(s.rsplit("::h", 1)[1]) == 16:
        s = s.rsplit("::h", 1)[0]
    cache[n] = s
    return s

prefix = st["prefix"]; sframe = st["frame"]
samples = th["samples"]["stack"]
weights = th["samples"].get("weight") or [1] * len(samples)
self_c, incl_c = Counter(), Counter()
stack_cache = {}
def chain(s):
    if s in stack_cache:
        return stack_cache[s]
    out, k = [], s
    while k is not None:
        out.append(short(frame_name(sframe[k])))
        k = prefix[k]
    stack_cache[s] = out
    return out
total = 0
for s, w in zip(samples, weights):
    if s is None:
        continue
    c = chain(s)
    total += w
    self_c[c[0]] += w
    for n in set(c):
        incl_c[n] += w
print(f"thread {th.get('name')} samples {total}")
print("== self")
for n, c in self_c.most_common(top):
    print(f"{100*c/total:5.1f}%  {n[:150]}")
print("== inclusive")
for n, c in incl_c.most_common(top * 2):
    print(f"{100*c/total:5.1f}%  {n[:150]}")

# Callers: python3 prof.py PROFILE N TARGET -> who calls TARGET (2 levels up), by samples
if len(sys.argv) > 3:
    target = sys.argv[3]
    up = Counter()
    for s, w in zip(samples, weights):
        if s is None:
            continue
        c = chain(s)
        for i, n in enumerate(c):
            if target in n:
                up[" <- ".join(x[:90] for x in c[i:i + 5])] += w
                break
    print("== callers of", target)
    for n, c in up.most_common(15):
        print(f"{100*c/total:5.1f}%  {n}")
