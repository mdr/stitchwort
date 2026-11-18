#!/usr/bin/env python3
"""Check the K3a predicate (docs/proposals/self-hosted-fmt-s1-sketch.md,
section 1.4) on the twin's outputs in folders `probe.py` wrote: a line
that starts with a token is right of the block column in force, a closer
that starts a line is left of the column its bracket's item started at,
no comma starts a line, nor the token after `->`, and a `:` that starts
one is right of column 0. `Fmt.hangs` (src/Fmt/Predicates1.sw) is the
same rule, and `Fmt.Twin --stage hangs` evaluates it. Slice 1 files only.

  tools/fmt/dev/hangs.py OUT [OUT ...]
"""
import re, sys
from pathlib import Path
TOKEN = re.compile(r"--.*|[()\[\],]|:=|[^\s()\[\],]+")
def check(text):
    bad = []
    stack = []      # per open bracket: column of the current item's first token if it started a line
    top = None      # the same for the type or body at depth 0
    start = True    # next token starts an item / the type / the body
    first_line = True
    after_arrow = False
    for n, line in enumerate(text.split("\n"), 1):
        linestart = True
        for m in TOKEN.finditer(line):
            t, c = m.group(), m.start()
            if t.startswith("--"): break
            if t == "def" and c == 0 and linestart:
                stack, top, start, first_line = [], None, False, True
            force = next((b for b in reversed(stack) if b is not None), top if top is not None else 0)
            ls = linestart and not first_line
            if after_arrow and ls: bad.append(("arrow-operand-starts-line", n, c, force))
            after_arrow = t in ("->", "→")
            if t in ")]":
                block = stack.pop() if stack else None
                if ls and block is not None and c >= block: bad.append(("closer-at-block", n, c, block))
                start = False
            elif t == ",":
                if ls: bad.append(("comma-starts-line", n, c, force))
                stack[-1] = None; start = True
            elif t in (":", ":=") and not stack:
                if t == ":" and ls and c <= force: bad.append(("colon-left", n, c, force))
                top = None; start = True
            else:
                if ls and c <= force: bad.append(("item-left" if start else "continuation-left", n, c, force))
                if start and ls:
                    if stack: stack[-1] = c
                    else: top = c
                if t in "([":
                    stack.append(None); start = True
                else: start = False
            linestart = False
        if line.strip() and not line.strip().startswith("--"): first_line = False
    return bad
total = files = 0; kinds = {}
for folder in sys.argv[1:]:
    for q in sorted(Path(folder).glob("*.out.sw")):
        files += 1
        for b in check(q.read_text()):
            kinds.setdefault(b[0], []).append((q.name, ) + b[1:])
print(files, "outputs;", {k: len(v) for k, v in kinds.items()})
for k, v in kinds.items(): print(k, v[:6])
