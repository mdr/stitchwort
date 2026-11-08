"""The top functions of a samply profile saved with --unstable-presymbolicate.

    python3 -I dev/profile_top.py PROFILE.json.gz [--top N] [--focus NAME ...]
        [--group PREFIX ...]

Prints, for the thread with the most samples: the share of self time by kind
(generated code, the runtime's entry points, the rest of the runtime, the
allocator, system libraries), the top functions by self and by inclusive
time, and for each --focus function its callers and direct callees. In a
native executable, `stitchwort build --native` names each compiled body after
its Stitchwort definition (`Std.List.get#67`; a lambda is
`Owner/lambda12#340`; a global's function-value adapter `Name/value`), so
these are definition names. A tail call replaces its caller's frame, so
inclusive time follows the stack as it is, not the source's calls.

Each --group PREFIX adds a line, before the usual tables, for the samples with
a frame whose name starts with PREFIX (`--group Std.Parse.`): inclusive, and
self (the samples whose innermost frame matches). Code run by the effect
runtime loses its caller, so a group can undercount what a definition
started; read it as the time spent in or below those definitions' frames.
"""

import argparse
import bisect
import gzip
import json
import re
from collections import Counter


def demangle(name):
    """A legacy Rust symbol (`_ZN...E`) as `a::b::c`; others unchanged."""
    s = name.lstrip("_")
    if not s.startswith("ZN"):
        return name
    s, parts = s[2:], []
    while s and s[0].isdigit():
        m = re.match(r"\d+", s)
        k = int(m.group())
        s = s[m.end():]
        parts.append(s[:k])
        s = s[k:]
    if parts and re.fullmatch(r"h[0-9a-f]{16}", parts[-1]):
        parts.pop()
    out = "::".join(parts)
    for code, text in [("$LT$", "<"), ("$GT$", ">"), ("$u20$", " "), ("$RF$", "&"), ("$C$", ","), ("..", "::")]:
        out = out.replace(code, text)
    return out


GENERATED = re.compile(r".*(#\d+|/value)|apply\d+|rt_loop|rt_resume|rt_text_fold|(sw_)?cross_\w+")


def kind(name, lib, exe):
    if lib != exe:
        return f"system: {lib}"
    if GENERATED.fullmatch(name):
        return "generated code"
    if name.startswith("sw_"):
        return "runtime entry points (sw_*)"
    if name.startswith("mi_") or name.startswith("_mi_") or "alloc" in name.lower():
        return "allocator"
    return "runtime (Rust)"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("profile")
    parser.add_argument("--top", type=int, default=25)
    parser.add_argument("--focus", action="append", default=[])
    parser.add_argument("--group", action="append", default=[], metavar="PREFIX")
    opts = parser.parse_args()

    prof = json.load(gzip.open(opts.profile))
    syms = json.load(open(re.sub(r"\.json(\.gz)?$", ".json.syms.json", opts.profile)))
    strings = syms["string_table"]
    tables = {}
    for lib in syms["data"]:
        entries = sorted((e["rva"], e["size"], strings[e["symbol"]]) for e in lib["symbol_table"])
        tables[lib["debug_name"]] = ([e[0] for e in entries], entries)

    thread = max(prof["threads"], key=lambda t: t["samples"]["length"])
    exe = thread["processName"]
    libs = prof["libs"]
    ft, st = thread["frameTable"], thread["stackTable"]
    rt, fu = thread["resourceTable"], thread["funcTable"]

    def frame_name(f):
        res = fu["resource"][ft["func"][f]]
        lib = libs[rt["lib"][res]]["debugName"] if res is not None and res >= 0 else "?"
        addr = ft["address"][f]
        if lib in tables and addr is not None and addr >= 0:
            starts, entries = tables[lib]
            i = bisect.bisect_right(starts, addr) - 1
            if i >= 0 and addr < entries[i][0] + max(entries[i][1], 1):
                return demangle(entries[i][2]), lib
        return f"{lib}@{addr:#x}", lib

    names = [frame_name(f) for f in range(ft["length"])]
    stacks = {}
    samples = []
    weights = thread["samples"]["weight"] or [1] * thread["samples"]["length"]
    for s, w in zip(thread["samples"]["stack"], weights):
        if s is None:
            continue
        if s not in stacks:
            frames, at = [], s
            while at is not None:
                frames.append(st["frame"][at])
                at = st["prefix"][at]
            stacks[s] = [names[f] for f in frames]
        samples.append((stacks[s], w))
    total = sum(w for _, w in samples) or 1

    self_c, incl_c, kinds = Counter(), Counter(), Counter()
    for frames, w in samples:
        self_c[frames[0][0]] += w
        kinds[kind(*frames[0], exe)] += w
        for name in {n for n, _ in frames}:
            incl_c[name] += w

    def pct(c):
        return f"{100 * c / total:5.1f}%"

    print(f"{opts.profile}: {total} samples (thread {thread['name']})")
    if opts.group:
        print("\nGroups (frame names starting with the prefix):")
        for prefix in opts.group:
            inclusive = sum(w for frames, w in samples if any(n.startswith(prefix) for n, _ in frames))
            own = sum(w for frames, w in samples if frames[0][0].startswith(prefix))
            print(f"  {pct(inclusive)} inclusive, {pct(own)} self  {prefix}*")
    print("\nSelf time by kind:")
    for k, c in kinds.most_common():
        print(f"  {pct(c)}  {k}")
    print(f"\nTop {opts.top} by self time:")
    for name, c in self_c.most_common(opts.top):
        print(f"  {pct(c)}  {name}")
    print(f"\nTop {opts.top} by inclusive time:")
    for name, c in incl_c.most_common(opts.top):
        print(f"  {pct(c)}  {name}")
    for target in opts.focus:
        callers, callees = Counter(), Counter()
        for frames, w in samples:
            fr = [n for n, _ in frames]
            if target in fr:
                i = fr.index(target)
                if i + 1 < len(fr):
                    callers[fr[i + 1]] += w
                callees[fr[i - 1] if i > 0 else "(self)"] += w
        print(f"\n{target}, {pct(incl_c[target])} inclusive. Callers:")
        for name, c in callers.most_common(12):
            print(f"  {pct(c)}  {name}")
        print("Direct callees, inclusive:")
        for name, c in callees.most_common(12):
            print(f"  {pct(c)}  {name}")


main()
