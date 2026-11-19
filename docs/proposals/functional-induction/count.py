"""SW-4229: how many proofs hand-build an induction along a function.

Usage: python3 -I count.py ROOT [ROOT...]   (each ROOT a folder of .sw files)

Heuristics, per project root (tools/fmt/src, crates/elab/src/std):
  recursive def   a `def` whose body (after its header) names it again
  guarded         a recursive def with a guarded arm (`| pat if cond =>`) and an arm after it
  rec theorem     a `theorem` whose body names it again (a proof by recursion)
  along f         a rec theorem whose statement names a recursive def f
                  and whose body splits (`match`) at least once
  step lemma      a theorem whose conclusion is `f … = f …` with f a recursive def
                  (a hand-written unfolding step, like withoutRNop)
  named split     `match NAME: e with` inside an along-f proof (a guard or branch
                  condition split by hand so the proof can rewrite with it)
  uses induct     a proof that names `f.induct` or `match induct`
"""
import os
import re
import sys
from collections import Counter

DECL = re.compile(r"^(theorem|def|test|type|ability|import|namespace|instance|class|alias|opaque|--|#|@)")
HEAD = re.compile(r"^(theorem|def)\s+([A-Za-z_][\w.']*)")


def blocks(path):
    lines = open(path, encoding="utf-8").read().split("\n")
    cur = None
    for i, line in enumerate(lines):
        if line and not line[0].isspace() and not line.startswith("--|"):
            if cur:
                yield cur
                cur = None
            m = HEAD.match(line)
            if m:
                cur = (m.group(1), m.group(2), i + 1, [line])
        elif cur:
            cur[3].append(line)
    if cur:
        yield cur


def strip_comments(text):
    return "\n".join(l.split("--")[0] if "--" in l else l for l in text.split("\n"))


def split_header(text):
    """The header (up to the declaration's own `:=`) and the body."""
    depth = 0
    for i, ch in enumerate(text):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif ch == ":" and text[i + 1 : i + 2] == "=" and depth == 0:
            return text[:i], text[i + 2 :]
    # arms without `:=` (`def f: A → B` then `| … =>`)
    m = re.search(r"\n\s*\|", text)
    if m:
        return text[: m.start()], text[m.start() :]
    return text, ""


def conclusion(header):
    """Text after the binders' closing colon, at bracket depth 0."""
    depth = 0
    last = None
    for i, ch in enumerate(header):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif ch == ":" and depth == 0:
            last = i
            break
    return header[last + 1 :] if last is not None else ""


def short(name):
    return name.split(".")[-1]


def word(name):
    return re.compile(r"(?<![\w.])(?:[\w]+\.)*" + re.escape(short(name)) + r"(?![\w'])")


def main(root):
    defs, thms = [], []
    for dp, _, fs in os.walk(root):
        if "/Tests" in dp:
            continue
        for f in fs:
            if f.endswith(".sw"):
                p = os.path.join(dp, f)
                for kind, name, line, ls in blocks(p):
                    text = strip_comments("\n".join(ls))
                    header, body = split_header(text)
                    rec = bool(word(name).search(body))
                    item = dict(kind=kind, name=name, file=p, line=line, header=header, body=body, rec=rec)
                    (defs if kind == "def" else thms).append(item)
    recdefs = [d for d in defs if d["rec"]]
    names = {short(d["name"]) for d in recdefs}
    guarded = [d for d in recdefs if re.search(r"\n\s*\|[^\n]*\sif\s[^\n]*=>[\s\S]*\n\s*\|", d["body"])]
    recthms = [t for t in thms if t["rec"]]
    along, steps, named, induct = [], [], Counter(), []
    namecall = re.compile(r"(?<![\w.'])([A-Za-z_][\w]*)(?![\w'])")
    for t in thms:
        concl = conclusion(t["header"])
        mentioned = {m for m in namecall.findall(t["header"]) if m in names}
        if re.search(r"\.induct\b|match induct", t["body"]):
            induct.append(t)
        sides = re.split(r"\s=\s", concl.strip(), maxsplit=1)
        if len(sides) == 2:
            l, r = (s.strip() for s in sides)
            hl = re.match(r"\(?([A-Za-z_][\w.]*)", l)
            hr = re.match(r"\(?([A-Za-z_][\w.]*)", r)
            if hl and hr and short(hl.group(1)) == short(hr.group(1)) and short(hl.group(1)) in names:
                if l != r:
                    steps.append(t)
        if t["rec"] and mentioned and "match" in t["body"]:
            along.append(t)
            named[t["name"]] = len(re.findall(r"match\s+[A-Za-z_]\w*\s*:", t["body"]))
    lines = sum(len((t["header"] + t["body"]).strip().split("\n")) for t in along)
    print(f"== {root}")
    print(f"definitions {len(defs)}, recursive {len(recdefs)}, with a guarded arm before another {len(guarded)}")
    print(f"theorems {len(thms)}, by recursion {len(recthms)}")
    print(f"along a recursive def (recursive, splits, statement names one): {len(along)}, {lines} lines")
    print(f"  of which with a named split (`match h: e with`): {sum(1 for v in named.values() if v)}, splits {sum(named.values())}")
    print(f"step lemmas `f … = f …`: {len(steps)}")
    def hyps(t):
        c = conclusion(t["header"])
        return t["header"][: len(t["header"]) - len(c)] if c else ""
    gsteps = [t for t in steps if re.search(r"= (True|False)\)|≠|¬", hyps(t))]
    print(f"  of which take a condition (a `= True`/`= False`/`≠`/`¬` hypothesis): {len(gsteps)}")
    stepnames = {short(t["name"]) for t in gsteps}
    users = [t for t in along if any(re.search(r"(?<![\w.])(?:\w+\.)*" + re.escape(n) + r"\b", t["body"]) for n in stepnames)]
    print(f"  along-f proofs that use one of those: {len(users)}")
    if os.environ.get("LIST"):
        for t in gsteps:
            print("  gstep", t["name"], t["file"] + ":" + str(t["line"]))
        for t in along:
            if named[t["name"]]:
                print("  namedsplit", t["name"], t["file"] + ":" + str(t["line"]), named[t["name"]])
    print(f"proofs naming f.induct or match induct: {len(induct)}")
    if os.environ.get("LIST"):
        for t in steps:
            print("  step", t["name"], t["file"] + ":" + str(t["line"]))
        for d in guarded:
            print("  guarded", d["name"], d["file"] + ":" + str(d["line"]))
        for t in along[: int(os.environ.get("LIST"))]:
            print("  along", t["name"], t["file"] + ":" + str(t["line"]), named[t["name"]])


for r in sys.argv[1:]:
    main(r)
