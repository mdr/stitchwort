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
these are definition names. Inclusive entries marked `*` have the runtime's loop beneath them in at least a tenth
of their samples: the function installed an effect handler, and the rest of
the program ran as its continuation, so the figure includes that. A tail call replaces its caller's frame, so
inclusive time follows the stack as it is, not the source's calls.

With --pc-map FILE (the `OUT.pcmap.json` of `stitchwort build --native
--pc-map`), the top --bodies compiled bodies by self time are each split by
the address of the sample's instruction: by part (the bytecode instruction's
own work, checks of steps, frames and errors, reference counts taken and
given up, calls, returns with their epilogue, the prologue, error exits) and
by bytecode instruction. A sample can land on the instruction after a slow
one (skid), so one instruction's count is fuzzy; parts summed over a body
are reliable enough. `untagged` is code Cranelift's optimiser made or moved
with no instruction of its own (constants, shared values).

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
from collections import Counter, defaultdict


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


# Frames of the effect runtime's loop. A handler's continuation runs from
# one, beneath the frame of the definition that installed the handler.
LOOP_FRAMES = {"rt_loop", "rt_resume"}


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


def under_loop_names(frames, exe):
    """The generated functions in one sample's stack (innermost first) that
    have a runtime loop frame beneath them: they started a handler or
    continuation, so their inclusive time includes what ran after them."""
    names, seen_loop = set(), False
    for name, lib in frames:
        if name in LOOP_FRAMES:
            seen_loop = True
        elif seen_loop and lib == exe and re.fullmatch(r".*(#\d+|/value)", name):
            names.add(name)
    return names


def load_pc_map(path):
    """The `--pc-map` file's bodies, by symbol: (size, instrs, stretches
    as sorted lists of starts and of (end, pc, part))."""
    bodies = {}
    for body in json.load(open(path))["bodies"]:
        stretches = body["stretches"]
        bodies[body["symbol"]] = (body["size"], body["instrs"], [s[0] for s in stretches],
                                  [tuple(s[1:]) for s in stretches])
    return bodies


def fold(offsets, body):
    """Counters by part and by pc (with each pc's parts) of the weighted
    `(offset, weight)` samples in one body of `load_pc_map`."""
    size, _, starts, rest = body
    parts, pcs, pc_parts = Counter(), Counter(), defaultdict(Counter)
    for offset, w in offsets:
        i = bisect.bisect_right(starts, offset) - 1
        if i < 0 or offset >= rest[i][0]:
            parts["outside the map"] += w
            continue
        _, pc, part = rest[i]
        parts[part] += w
        if pc is not None:
            pcs[pc] += w
            pc_parts[pc][part] += w
    return parts, pcs, pc_parts


def print_pc_split(name, offsets, body, total, lines=15):
    """`fold`'s split of one body, as shares of its self time (and, in
    brackets, of the profile's)."""
    own = sum(w for _, w in offsets) or 1
    parts, pcs, pc_parts = fold(offsets, body)
    instrs = body[1]

    def share(c):
        return f"{100 * c / own:5.1f}% ({100 * c / total:4.1f}%)"

    print(f"\n{name}: self time by part (share of its self time, and of the profile's):")
    for part, c in parts.most_common():
        print(f"  {share(c)}  {part}")
    print(f"By bytecode instruction (top {lines}):")
    for pc, c in pcs.most_common(lines):
        split = ", ".join(f"{p} {100 * n / c:.0f}%" for p, n in pc_parts[pc].most_common())
        text = instrs[pc] if len(instrs[pc]) <= 60 else instrs[pc][:57] + "..."
        print(f"  {share(c)}  {pc:4}  {text}  [{split}]")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("profile")
    parser.add_argument("--top", type=int, default=25)
    parser.add_argument("--focus", action="append", default=[])
    parser.add_argument("--group", action="append", default=[], metavar="PREFIX")
    parser.add_argument("--pc-map", help="the executable's OUT.pcmap.json (build --native --pc-map)")
    parser.add_argument("--bodies", type=int, default=3, help="with --pc-map, how many bodies to split")
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

    # Each frame's offset from the start of its symbol, for --pc-map.
    offsets = [None] * ft["length"]

    def frame_name(f):
        res = fu["resource"][ft["func"][f]]
        lib = libs[rt["lib"][res]]["debugName"] if res is not None and res >= 0 else "?"
        addr = ft["address"][f]
        if lib in tables and addr is not None and addr >= 0:
            starts, entries = tables[lib]
            i = bisect.bisect_right(starts, addr) - 1
            if i >= 0 and addr < entries[i][0] + max(entries[i][1], 1):
                offsets[f] = addr - entries[i][0]
                return demangle(entries[i][2]), lib
        return f"{lib}@{addr:#x}", lib

    names = [frame_name(f) for f in range(ft["length"])]
    stacks = {}
    samples = []
    # Per symbol, the (offset, weight) of each sample whose innermost frame
    # it is.
    leaves = defaultdict(list)
    weights = thread["samples"]["weight"] or [1] * thread["samples"]["length"]
    for s, w in zip(thread["samples"]["stack"], weights):
        if s is None:
            continue
        if s not in stacks:
            frames, at = [], s
            while at is not None:
                frames.append(st["frame"][at])
                at = st["prefix"][at]
            stacks[s] = ([names[f] for f in frames], offsets[frames[0]] if frames else None)
        frames, leaf = stacks[s]
        samples.append((frames, w))
        if leaf is not None:
            leaves[frames[0][0]].append((leaf, w))
    total = sum(w for _, w in samples) or 1

    self_c, incl_c, kinds = Counter(), Counter(), Counter()
    # Per generated function, the samples where a runtime loop frame lies
    # beneath its own frame.
    under_loop = Counter()
    for frames, w in samples:
        self_c[frames[0][0]] += w
        kinds[kind(*frames[0], exe)] += w
        for name in {n for n, _ in frames}:
            incl_c[name] += w
        for name in under_loop_names(frames, exe):
            under_loop[name] += w

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
    marked = False
    for name, c in incl_c.most_common(opts.top):
        # Only a mark when the continuation is a real part of the figure.
        flag = under_loop[name] * 10 >= c
        marked |= flag
        print(f"  {pct(c)}{' *' if flag else '  '} {name}")
    if marked:
        print("  * runs a handler: inclusive time includes the continuation after it"
              " (runtime loop frames beneath), so it overstates the definition's own work;"
              " read it with the stage cuts or self time.")
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
    if opts.pc_map:
        bodies = load_pc_map(opts.pc_map)
        mapped = [(name, c) for name, c in self_c.most_common() if name in bodies]
        if not mapped:
            print(f"\nNo compiled body of {opts.pc_map} has samples.")
        for name, _ in mapped[:opts.bodies]:
            print_pc_split(name, leaves[name], bodies[name], total)


if __name__ == "__main__":
    main()
