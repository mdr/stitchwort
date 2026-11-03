#!/usr/bin/env python3
"""Module coupling inside one crate (docs/research/architecture-review.md).

  modgraph.py CRATE_SRC [--state STRUCT@FILE] [--json OUT]

Approximate, from the text (no type information):

- A module is a file under src/ (a directory's mod.rs is the directory).
- Path edges: `crate::m`, `super::m` (resolved), `use m::`, and `m::x` where m
  is a sibling module name.
- Method edges: every `fn name` inside an `impl STRUCT` block belongs to its
  module; `.name(` elsewhere is an edge to the defining module when the name
  is defined in exactly one module.
- Field access: with --state, the struct's fields are read from FILE; each
  `.field` occurrence counts as a use, and `.field.borrow_mut()`, `.set(`,
  `.field =`, `.field.push(`/`insert`/`clear`/... as a write.

Prints module sizes, strongly connected components, the most coupled
modules, and the fields of the state struct by how many modules touch them.
"""
import argparse, json, re, sys
from collections import defaultdict
from pathlib import Path


def modules(src):
    mods = {}
    for p in sorted(src.rglob("*.rs")):
        rel = p.relative_to(src).with_suffix("")
        parts = list(rel.parts)
        if parts[-1] == "mod":
            parts = parts[:-1]
        if parts in (["lib"], ["main"]):
            name = "lib"
        else:
            name = "::".join(parts)
        mods[name] = p
    return mods


TOKEN = re.compile(
    r"""(?P<line>//[^\n]*)|(?P<block>/\*.*?\*/)|(?P<raw>r(?P<h>\#*)".*?"(?P=h))|(?P<str>b?"(?:\\.|[^"\\])*")|(?P<chr>b?'(?:\\.|[^'\\])')""",
    re.S,
)


def strip(text):
    """Remove comments, string and char literals (lifetimes are kept)."""
    def rep(m):
        if m.group("line") or m.group("block"):
            return " "
        return '""'
    text = TOKEN.sub(rep, text)
    # drop inline unit-test modules: they are not part of the library's structure
    while (m := re.search(r"#\[cfg\(test\)\]\s*(?:pub(?:\([\w:]+\))?\s+)?mod\s+\w+\s*\{", text)):
        i, depth = m.end(), 1
        while i < len(text) and depth:
            depth += text[i] == "{"
            depth -= text[i] == "}"
            i += 1
        text = text[:m.start()] + text[i:]
    return text


def impl_blocks(text, struct):
    """Yield the bodies of `impl STRUCT {` / `impl Trait for STRUCT {` blocks."""
    for m in re.finditer(r"\bimpl(?:<[^>]*>)?\s+(?:[\w:<>']+\s+for\s+)?(?:crate::)?" + struct + r"\b[^{;]*\{", text):
        i, depth = m.end(), 1
        while i < len(text) and depth:
            c = text[i]
            depth += c == "{"
            depth -= c == "}"
            i += 1
        yield text[m.end():i]


def tarjan(nodes, edges):
    index, low, stack, on, out = {}, {}, [], set(), []
    counter = [0]
    sys.setrecursionlimit(10000)

    def visit(v):
        index[v] = low[v] = counter[0]
        counter[0] += 1
        stack.append(v)
        on.add(v)
        for w in edges.get(v, ()):
            if w not in index:
                visit(w)
                low[v] = min(low[v], low[w])
            elif w in on:
                low[v] = min(low[v], index[w])
        if low[v] == index[v]:
            comp = []
            while True:
                w = stack.pop()
                on.discard(w)
                comp.append(w)
                if w == v:
                    break
            out.append(comp)

    for v in nodes:
        if v not in index:
            visit(v)
    return out


WRITE = r"(?:\s*\.\s*(?:borrow_mut|set|replace|take|push|insert|remove|clear|truncate|extend|retain|drain|pop|entry|get_mut|get_or_init|swap)\b|\s*(?:=[^=]|\+=|-=))"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("src")
    ap.add_argument("--state", help="STRUCT@FILE, e.g. Elaborator@lib.rs")
    ap.add_argument("--json")
    a = ap.parse_args()
    src = Path(a.src)
    mods = modules(src)
    texts = {m: strip(p.read_text()) for m, p in mods.items()}
    sizes = {m: len(p.read_text().splitlines()) for m, p in mods.items()}
    leaf = defaultdict(set)
    for m in mods:
        leaf[m.split("::")[-1]].add(m)
        leaf[m].add(m)

    edges = defaultdict(set)
    def add(a_, b_):
        if a_ != b_ and b_ in mods:
            edges[a_].add(b_)

    for m, t in texts.items():
        for pm in re.finditer(r"\bcrate::((?:\w+::)*\w+)", t):
            parts = pm.group(1).split("::")
            for k in range(len(parts), 0, -1):
                cand = "::".join(parts[:k])
                if cand in mods:
                    add(m, cand)
                    break
        for pm in re.finditer(r"\bsuper::(\w+)", t):
            parent = m.split("::")[:-2] if m != "lib" else []
            cand = "::".join(parent + [pm.group(1)]) if parent else pm.group(1)
            add(m, cand if cand in mods else "lib")
        for pm in re.finditer(r"(?<![\w:])(\w+)::", t):
            name = pm.group(1)
            if name in ("crate", "super", "self", "std", "core") or name not in leaf:
                continue
            cands = leaf[name]
            # prefer a child of m, then a sibling, then a top-level module
            pick = None
            for c in cands:
                if c == f"{m}::{name}":
                    pick = c
            if not pick:
                for c in cands:
                    if c == name:
                        pick = c
            if pick:
                add(m, pick)

    method_owner = defaultdict(set)
    struct = None
    if a.state:
        struct, sfile = a.state.split("@")
        for m, t in texts.items():
            for body in impl_blocks(t, struct):
                for fm in re.finditer(r"\bfn\s+(\w+)", body):
                    method_owner[fm.group(1)].add(m)
    path_edges = {k: set(v) for k, v in edges.items()}
    method_edges = defaultdict(set)
    for m, t in texts.items():
        for cm in re.finditer(r"\.\s*(\w+)\s*(?:::<[^>]*>)?\s*\(", t):
            owners = method_owner.get(cm.group(1))
            if owners and len(owners) == 1:
                o = next(iter(owners))
                if o != m:
                    method_edges[m].add(o)
                    edges[m].add(o)

    fields = []
    field_use = {}
    if a.state:
        stext = strip((src / sfile).read_text())
        sm = re.search(r"pub struct " + struct + r"\s*\{", stext)
        i, depth = sm.end(), 1
        while depth:
            depth += stext[i] == "{"
            depth -= stext[i] == "}"
            i += 1
        body = stext[sm.end():i - 1]
        depth = 0
        for line in body.splitlines():
            if depth == 0:
                fm = re.match(r"\s*(?:#\[[^\]]*\]\s*)?(?:pub(?:\([\w:]+\))?\s+)?(\w+)\s*:", line)
                if fm:
                    fields.append(fm.group(1))
            depth += line.count("<") - line.count(">") + line.count("(") - line.count(")")
            depth = max(depth, 0)
        for f in fields:
            uses, writes = set(), set()
            for m, t in texts.items():
                if re.search(r"\.\s*" + f + r"\b(?!\s*\()", t):
                    uses.add(m)
                if re.search(r"\.\s*" + f + r"\b" + WRITE, t):
                    writes.add(m)
            field_use[f] = (sorted(uses), sorted(writes))

    psccs = [c for c in tarjan(sorted(mods), path_edges) if len(c) > 1]
    for c in sorted(psccs, key=len, reverse=True):
        print(f"path-only SCC of {len(c)} modules, {sum(sizes[x] for x in c)} lines: {' '.join(sorted(c)) if len(c) < 15 else ''}")
    sccs = tarjan(sorted(mods), edges)
    big = sorted((c for c in sccs if len(c) > 1), key=len, reverse=True)
    total = sum(sizes.values())
    print(f"modules: {len(mods)}, lines: {total}, path+method edges: {sum(len(v) for v in edges.values())}")
    for c in big:
        print(f"SCC of {len(c)} modules, {sum(sizes[x] for x in c)} lines")
    outside = [m for m in mods if not any(m in c for c in big)]
    print(f"outside the SCCs ({len(outside)}): {', '.join(sorted(outside))}")
    fan_in = defaultdict(int)
    for v, ws in edges.items():
        for w in ws:
            fan_in[w] += 1
    print("\nmodule  lines  fan-out  fan-in")
    for m in sorted(mods, key=lambda x: -sizes[x])[:40]:
        print(f"{m:28} {sizes[m]:6} {len(edges.get(m, ())):5} {fan_in[m]:5}")
    if fields:
        print(f"\n{struct}: {len(fields)} fields; modules touching each (reads+writes / writes)")
        rows = sorted(field_use.items(), key=lambda kv: -len(kv[1][0]))
        for f, (u, w) in rows:
            print(f"{f:28} {len(u):3} {len(w):3}  {' '.join(u) if len(u) <= 6 else ''}")
        per_mod = defaultdict(int)
        for f, (u, w) in field_use.items():
            for m in u:
                per_mod[m] += 1
        print(f"\nmodules by number of {struct} fields touched")
        for m, n in sorted(per_mod.items(), key=lambda kv: -kv[1])[:25]:
            print(f"{m:28} {n}")
    if a.json:
        Path(a.json).write_text(json.dumps({
            "sizes": sizes,
            "edges": {k: sorted(v) for k, v in edges.items()},
            "sccs": big,
            "fields": field_use,
        }, indent=1))


if __name__ == "__main__":
    main()
