"""Summarise a samply profile (Firefox processed format + .syms.json sidecar):
self time and inclusive time by function, for the busiest thread."""
import bisect, gzip, json, sys
from collections import Counter

path = sys.argv[1]
top = 40
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
import re
PH=[("std index build (parse all std)",["LibraryIndex>::build"]),
    ("project analyse (parse project files)",["project::analyse"]),
    ("other parsing",["parse_module","syntax::parser","syntax::lexer"]),
    ("cache load (library entries)",["elaborate_namespace_cached","admit_replayed","cache::"]),
    ("kernel (admit/check)",["stitchwort_core::check::","kernel::admit"]),
    ("elaboration",["stitchwort_elab::"]),
]
LEAF=[("parse/lex",["syntax::parser","syntax::lexer","syntax::tree","syntax::lower","syntax::ast","match_brackets","Tok as"]),
      ("read-back/quote",["quote","detach","read_back","readback"]),
      ("unify",["unify::"]),
      ("conversion",["conv"]),
      ("eval/force",["value::run","run_on","value::eval","value::resume","force","whnf","value::apply","value::visit","machine::"]),
      ("hashing",["blake3","Hasher","hash","RawTable","HashMap","shape_"]),
      ("cache I/O",["cache::","codec","__open","__read","read_nodes","mmap","fstat","__stat"]),
      ("diagnostics/names",["diagnostic","explain","names_and_proofs","StrSearcher","Diagnostic","names::"]),
      ("allocation/copy",["mi_","malloc","free","drop_glue","clone","from_iter","finish_grow","realloc","memmove","memcpy","Rc<","Vec<","RawVec","BTreeMap"]),
     ]
def cls(name,table):
    for g,ks in table:
        if any(k in name for k in ks): return g
    return "other"
phase_c=Counter(); grid=Counter(); leafc=Counter(); tot=0
incl_marks={"read-back (quote_as_until)":"quote_as_until","eval (value::run*)":"stitchwort_core::value::run","unify (unify::run)":"unify::run","conversion (conv_with)":"conv_with","kernel check (core::check::check)":"stitchwort_core::check::check","matching::blocker":"matching::blocker","generalised_now":"generalised_now","LibraryIndex::build":"LibraryIndex>::build","project::analyse":"project::analyse","parse_module_and_tree":"parse_module_and_tree","elaborate_namespace_cached":"elaborate_namespace_cached","admit_replayed":"admit_replayed","validate_marks":"validate_marks","warn_unreachable":"warn_unreachable","names_and_proofs":"names_and_proofs","elaborate_module":"elaborate_module"}
inc=Counter()
for s,w in zip(samples,weights):
    if s is None: continue
    c=chain(s); tot+=w
    joined="\n".join(c)
    ph="other"
    for g,ks in PH:
        if any(k in joined for k in ks): ph=g; break
    lf=cls(c[0],LEAF)
    phase_c[ph]+=w; grid[(ph,lf)]+=w; leafc[lf]+=w
    for k,m in incl_marks.items():
        if m in joined: inc[k]+=w
import sys
marker=sys.argv[3]; depth=int(sys.argv[4]) if len(sys.argv)>4 else 1
ch=Counter(); mt=0
for s,w in zip(samples,weights):
    if s is None: continue
    c=chain(s)  # leaf first
    idx=[i for i,n in enumerate(c) if marker in n]
    if not idx: continue
    i=idx[-1]  # outermost occurrence
    mt+=w
    path=c[max(i-depth,0):i][::-1]
    ch[" > ".join(x[:70] for x in path) if path else "(self)"]+=w
print(f"{marker}: {100*mt/tot:.1f}% of samples ({mt}/{tot})")
for k,v in ch.most_common(int(sys.argv[2])): print(f"{100*v/tot:5.1f}%  {k}")
