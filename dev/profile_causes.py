"""Splits the allocation, freeing and cloning time of a samply profile by cause (SW-2422).

    python3 dev/profile_causes.py PROFILE.json.gz [TOP] [shape]

PROFILE is one `task profile:native` wrote (target/profile/NAME.json.gz, with its
.syms.json beside it). Prints the share of all samples spent in memory work
(mimalloc, drop glue, the free walk, `Value::clone`), by operation, by
allocation site, by the kind of object freed (the innermost typed drop frame),
and by trigger (the caller outside all memory frames). With `shape`, the free
time by whether the object was the root of a free or a child reached by the
walk, and whether it had children to free. Read shares, not times.
Reuses the loader of profile_top.py; docs/reviews/SW-2422-allocation-by-cause.md.
"""
import sys, re, json, gzip, bisect
from pathlib import Path
from collections import Counter
import importlib.util
spec = importlib.util.spec_from_file_location("pt", str(Path(__file__).with_name("profile_top.py")))
pt = importlib.util.module_from_spec(spec); spec.loader.exec_module(pt)

def load(path):
    prof = json.load(gzip.open(path))
    syms = json.load(open(re.sub(r"\.json(\.gz)?$", ".json.syms.json", path)))
    strings = syms["string_table"]; tables = {}
    for lib in syms["data"]:
        entries = sorted((e["rva"], e["size"], strings[e["symbol"]]) for e in lib["symbol_table"])
        tables[lib["debug_name"]] = ([e[0] for e in entries], entries)
    th = max(prof["threads"], key=lambda t: t["samples"]["length"])
    libs = prof["libs"]; ft, st = th["frameTable"], th["stackTable"]; rt, fu = th["resourceTable"], th["funcTable"]
    def fname(f):
        res = fu["resource"][ft["func"][f]]
        lib = libs[rt["lib"][res]]["debugName"] if res is not None and res >= 0 else "?"
        addr = ft["address"][f]
        if lib in tables and addr is not None and addr >= 0:
            starts, entries = tables[lib]
            i = bisect.bisect_right(starts, addr) - 1
            if i >= 0 and addr < entries[i][0] + max(entries[i][1], 1):
                return pt.demangle(entries[i][2])
        return f"{lib}@{addr:#x}"
    names = [fname(f) for f in range(ft["length"])]
    cache = {}; out = []
    ws = th["samples"]["weight"] or [1]*th["samples"]["length"]
    for s, w in zip(th["samples"]["stack"], ws):
        if s is None: continue
        if s not in cache:
            fr, at = [], s
            while at is not None:
                fr.append(names[st["frame"][at]]); at = st["prefix"][at]
            cache[s] = fr
        out.append((cache[s], w))
    return out

MEM = re.compile(r"^(_?mi_|__rust|__rustc|_platform_mem|madvise|sw_drop_words|sw_drop_deferred|sw_inc$|.*drop_glue|.*::free$|.*::free_emptied|.*free_block|.*take_children|.*drop_slow|.*as core::ops::drop::Drop>::drop|.*RawVec|.*into_boxed_slice|.*Value as core::clone::Clone>::clone|.*Rc<.*>>::clone|.*CellCache|.*alloc::alloc|.*Vec<.*>>::push|.*value::take_from|.*Vec<stitchwort_rt::value::Value>>)")
def is_mem(n): return bool(MEM.match(n))

def work_kind(frames):
    """what the sample's memory work is: by the innermost matching frames"""
    s = " ".join(frames[:6])
    leaf = frames[0]
    if "mi_malloc" in leaf or "_mi_malloc" in leaf or "__rust_alloc" in leaf or "mi_page_free_list_extend" in leaf or "mi_heap" in leaf: return "malloc"
    if re.search(r"mi_free|_mi_free|mi_page_|mi_segment|_mi_|__rust_dealloc|madvise", leaf): return "free(mi)"
    return "other"



ALLOC_LEAF = re.compile(r"^(mi_malloc|_mi_malloc|mi_realloc|_mi_theap_realloc|mi_page_free_list_extend|mi_arena|mi_bin|mi_page_queue|mi_heap|mi_theap_collect|_mi_page|mi_free_try|mi_bbitmap|mi_bchunk|madvise|__rustc::__rust_no_alloc|__rustc::__rust_alloc|.*finish_grow|.*try_allocate_in|.*grow_one|.*into_boxed_slice|.*do_reserve|.*CellCache>::full)")
FREE_LEAF = re.compile(r"^(mi_free|__rustc::__rust_dealloc|_mi_page_retire)")
CLONE_LEAF = re.compile(r".*(Value as core::clone::Clone>::clone|Rc<.*>>::clone)")
SKIP = re.compile(r"^(_?mi_|__rust|.*RawVec|.*alloc::alloc|.*Vec<.*>>::(into_boxed_slice|push|grow)|madvise|.*finish_grow|_platform_mem|.*CellCache>::full$|.*boxed::box_new)")

def op_of(fr):
    leaf = fr[0]
    if FREE_LEAF.match(leaf): return "mi_free"
    if CLONE_LEAF.match(leaf): return "clone"
    if ALLOC_LEAF.match(leaf): return "alloc"
    return "walk"          # drop glue, value::free, take_children, Fields::drop, drop_slow...

def object_of(fr):
    """innermost typed frame = the object whose memory is being walked or freed"""
    for n in fr:
        if "Handler>::drop_slow" in n: return "Handler"
        if "Resume>::drop_slow" in n or "Resume>::take_children" in n or "Resume::take_children" in n: return "Resume"
        if "StateRun" in n: return "StateRun"
        if "Fun>::take_children" in n or "Rc<stitchwort_rt::value::Fun>>::drop_slow" in n: return "Fun (closure/pap/cont.)"
        if "Fields as core::ops::drop::Drop>::drop" in n or "Rc<[stitchwort_rt::value::Value]>>::drop_slow" in n: return "cell (Fields)"
        if "Delay" in n and "drop" in n: return "Delay"
    return "untyped (drop glue / value::free)"

def site_of(fr):
    """for allocations: what is being made"""
    chain = [n for n in fr]
    for i, n in enumerate(chain):
        if n.endswith("Fun>::take_children") or "Resume>::take_children" in n or "Fields as core::ops::drop::Drop>::drop" in n or n.endswith("value::free"):
            if i > 0 and ("grow" in " ".join(chain[:i]) or "finish_grow" in " ".join(chain[:i])):
                return "drop worklist Vec"
    for i, n in enumerate(chain):
        if SKIP.match(n) or n.startswith("<alloc::") and "RawVec" in n: continue
        if i == 0: continue
        nx = chain[i+1] if i+1 < len(chain) else ""
        if "sw_closure" in n: return "closure (sw_closure)"
        if "sw_pap" in n: return "pap (sw_pap)"
        if "sw_cell_new" in n or "sw_ctor" in n or "cell_cache" in n: return "cell (generated code)"
        if "sw_bind" in n: return "Bind node (sw_bind)"
        if "Value>::data" in n:
            if "sw_bind" in nx: return "Bind node (sw_bind)"
            if "prims" in nx: return "cell/text (prims)"
            if "effect::" in nx or "sw_eff" in nx: return "cell (effect machinery)"
            return "cell (runtime, other: %s)" % re.sub(r"stitchwort_rt::","",nx)[:30]
        if "sw_resume" in n or "Resume" in n: return "Resume"
        if "sw_state" in n or "state_step" in n or "StateRun" in n: return "StateRun/state step"
        if "sw_eff" in n or "handler_for" in n or n.startswith("stitchwort_rt::effect"): return "Handler/eff machinery"
        if "sw_apply_prepare" in n: return "apply (sw_apply_prepare)"
        if "prims::" in n or "sw_prim" in n: return "prims (texts/arrays/numbers)"
        if re.match(r".*(#\d+|/value)$", n) or n.startswith("apply") or n.startswith("rt_"): return "generated/loop (unlabelled)"
        return "other: " + re.sub(r"stitchwort_rt::|alloc::","",n)[:40]
    return "other"

def trig_group(fr, idx):
    o = max(idx); t = fr[o+1] if o+1 < len(fr) else "(root)"
    if re.match(r"sw_(eff|resume|state|bind)|stitchwort_rt::effect|rt_loop|rt_resume|.*handler", t) or t.startswith("sw_eff"): return "effect/bind/resume machinery (" + ("rt_loop/resume" if t.startswith("rt_") else re.sub(r"stitchwort_rt::","",t)[:22]) + ")"
    if t.startswith("sw_apply") or re.match(r"apply\d", t): return "apply (" + t + ")"
    if t.startswith("sw_closure") or t.startswith("sw_pap") or t.startswith("sw_cell") or t.startswith("sw_prim"): return t
    if re.match(r".*(#\d+|/value)$", t): return "generated code body"
    return re.sub(r"stitchwort_rt::|alloc::","",t)[:40]

def main(path, top=14):
    samples = load(path); total = sum(w for _, w in samples)
    mem = 0; ops = Counter(); objs = Counter(); sites = Counter(); trig = Counter(); trig_raw = Counter()
    for fr, w in samples:
        idx = [i for i, n in enumerate(fr) if is_mem(n) and not n.startswith("_platform_mem")]
        if not idx: continue
        mem += w
        op = op_of(fr); ops[op] += w
        if op == "alloc": sites[site_of(fr)] += w
        elif op == "clone": sites["clone: " + trig_group(fr, idx)[:30]] += w
        else: objs[(op, object_of(fr))] += w
        g = trig_group(fr, idx)
        trig[g.split(" (")[0]] += w; trig_raw[g] += w
    P = lambda c: f"{100*c/total:5.1f}%"
    print(f"{path.split('/')[-1]}: allocation/free/clone work = {P(mem)} of {total} samples")
    print("\nBy operation:"); [print(f"  {P(c)} {k}") for k, c in ops.most_common()]
    print("\nAllocation sites (malloc side) and clone triggers:"); [print(f"  {P(c)} {k}") for k, c in sites.most_common(top)]
    print("\nFreed objects (free + walk), innermost typed frame:")
    byobj = Counter()
    for (op, o), c in objs.items(): byobj[o] += c
    for o, c in byobj.most_common():
        parts = {op: objs[(op, o)] for op in ("mi_free", "walk") if objs[(op, o)]}
        print(f"  {P(c)} {o}   " + ", ".join(f"{k} {P(v)}" for k, v in parts.items()))
    print("\nBy trigger (the caller outside all memory frames):"); [print(f"  {P(c)} {k}") for k, c in trig_raw.most_common(top)]
if __name__ == "__main__":
    main(sys.argv[1], int(sys.argv[2]) if len(sys.argv) > 2 else 14)

def walkshape(path):
    samples = load(path); total = sum(w for _, w in samples)
    TYPED = re.compile(r"(Fields as core::ops::drop::Drop>::drop|Rc<stitchwort_rt::value::Fun>>::drop_slow|Rc<\[stitchwort_rt::value::Value\]>>::drop_slow|Handler>::drop_slow|Resume>::drop_slow)")
    c = Counter()
    for fr, w in samples:
        if not any(is_mem(n) for n in fr): continue
        op = op_of(fr)
        if op in ("alloc", "clone"): continue
        kinds = [(i, n) for i, n in enumerate(fr) if TYPED.search(n)]
        if not kinds: c[("untyped", "-")] += w; continue
        i0, n0 = kinds[0]
        obj = "cell" if ("Fields" in n0 or "[stitchwort_rt::value::Value]" in n0) else "fun/other"
        outer = [n for n in fr[i0+1:] if TYPED.search(n) or n.endswith("value::free")]
        inner_free = any(n.endswith("value::free") for n in fr[:i0])
        pos = "root" if not outer else "nested"
        c[(obj, pos + (", frees children" if inner_free else ", no child walk below"))] += w
    print(path.split("/")[-1], "free+walk shapes (share of total):")
    for k, v in sorted(c.items()): print(f"  {100*v/total:5.1f}% {k[0]:10s} {k[1]}")
if __name__ == "__main__" and len(sys.argv) > 3 and sys.argv[3] == "shape":
    walkshape(sys.argv[1])
