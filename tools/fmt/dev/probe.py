#!/usr/bin/env python3
"""A counterexample search for the self-hosted formatter's slice 1 (SW-3955).

Makes COUNT random slice 1 files (one to three `def`s from random trees,
in six mixes of comments, line breaks, odd closer and comma columns, glued
and spaced tokens, trailing commas and long lists), writes them to OUT,
and runs each through the twin (`Fmt.Twin.main`, `--stage NAME --batch
LIST`). For each file X the twin formats (out = text X):

  idem:      text out == out
  tree:      tidied X == tidied out == tree out
  comments:  comment texts in order, X against out
  long:      a code line over 120 columns
  rust:      `stitchwort fmt -` on X == out (with --rust: slow, so the
             first --rust files only)

With --sketch, also the checks that need SW-3955's sketch stages
(`words`, `calmwords`, `sketch`), which the repo's twin doesn't have:
words, blanks, calm, nothang, unsettled, srcunsettled (see
docs/proposals/self-hosted-fmt-s1-sketch.md, section 3).

The generated files and the twin's outputs (`*.out.sw`) stay in OUT;
`hangs.py OUT` then checks the outputs' line starts (K3a) and
`classify.py OUT` sorts the outputs that differ from Rust's.

  tools/fmt/dev/probe.py --twin TWIN --out OUT --seed 1 --count 1000
"""
import argparse, random, subprocess, re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]

ATOMS = ["a", "b", "f", "g", "xs", "Foo", "A.b", "1", "2", "3.5", "veryLongNameNumberOne", "anotherQuiteLongName"]
OPS = ["+", "-", "*", "/", "%", "++", "==", "!=", "<", "<=", ">", ">=", "&&", "||", "=", "≤", "∧", "∨", "≠"]


def gen(r, depth, big):
    k = r.random()
    if depth <= 0 or k < 0.22:
        return ("atom", r.choice(ATOMS))
    if k < 0.34:
        return ("paren", gen(r, depth - 1, big))
    if k < 0.44:
        return ("tuple", [gen(r, depth - 1, big) for _ in range(r.randint(2, 4))], r.random() < 0.3)
    if k < 0.56:
        n = r.choice([0, 1, 2, 3, big])
        return ("list", [gen(r, depth - 1 if n < 5 else 0, big) for _ in range(n)], n > 0 and r.random() < 0.3)
    if k < 0.74:
        return ("app", gen(r, depth - 1, big), [gen(r, depth - 1, big) for _ in range(r.randint(1, 3))])
    if k < 0.90:
        return ("bin", gen(r, depth - 1, big), r.choice(OPS), gen(r, depth - 1, big))
    if k < 0.96:
        return ("pre", r.choice(["-", "-", "!"]), gen(r, depth - 1, big))
    return ("arrow", gen(r, depth - 1, big), r.choice(["->", "→"]), gen(r, depth - 1, big))


class Out:
    """Tokens with layout: each is (text, glue) where glue is '', ' ' or a break."""

    def __init__(self, r, comments, breaks, glue):
        self.r, self.comments, self.breaks, self.glue = r, comments, breaks, glue
        self.parts = []
        self.depth = 0
        self.n = 0
        self.first = True  # next token starts an item
        self.pending = False  # a trailing comment was written: must break

    def tok(self, text, tight=False, closer=False, comma=False):
        r = self.r
        if closer:
            self.depth -= 1
        d = self.depth
        start = 2 if d == 0 else 4 * d + 2
        cont = start + 2
        col = start if self.first else cont
        if closer or comma:
            col = r.choice([0, start, cont, max(0, start - 4)])
        if self.parts:
            brk = self.pending or r.random() < self.breaks
            if brk:
                gap = "\n"
                if r.random() < self.comments * 0.5:
                    gap += "\n"
                while r.random() < self.comments * 0.6:
                    self.n += 1
                    gap += " " * r.choice([col, 0, col + 3]) + f"-- o{self.n}" + r.choice(["", " "]) + "\n"
                    if r.random() < 0.3:
                        gap += "\n"
                gap += " " * col
            elif tight and r.random() < self.glue:
                gap = ""
            elif (closer or comma) and r.random() < 0.8:
                gap = ""
            else:
                gap = " " if not self.after_open or r.random() < 0.2 else ""
            self.parts.append(gap)
        self.parts.append(text)
        self.pending = False
        if r.random() < self.comments:
            self.n += 1
            self.parts.append(f" -- t{self.n}" + r.choice(["", "  "]))
            self.pending = True
        self.first = False
        self.after_open = False

    after_open = False

    def open(self, text, tight=False):
        self.tok(text, tight)
        self.depth += 1
        self.first = True
        self.after_open = True

    def comma(self):
        self.tok(",", comma=True)
        self.first = True


def emit(o, e, tight=False):
    r = o.r
    kind = e[0]
    if kind == "atom":
        o.tok(e[1], tight)
    elif kind == "paren":
        o.open("(", tight)
        emit(o, e[1])
        o.tok(")", closer=True)
    elif kind in ("tuple", "list"):
        o.open("(" if kind == "tuple" else "[", tight)
        for i, item in enumerate(e[1]):
            if i:
                o.comma()
            emit(o, item)
        if e[2]:
            o.comma()
        o.tok(")" if kind == "tuple" else "]", closer=True)
    elif kind == "app":
        emit(o, e[1], tight)
        for a in e[2]:
            emit(o, a, tight=True)
    elif kind in ("bin", "arrow"):
        emit(o, e[1], tight)
        o.tok(e[2], tight=True)
        emit(o, e[3], tight=True)
    elif kind == "pre":
        o.tok(e[1], tight)
        o.glue, keep = (0.7 if o.glue else 0.0), o.glue
        emit(o, e[2], tight=True)
        o.glue = keep


def source(r, ndefs, depth, comments, breaks, glue, big):
    text = ""
    n = 0
    for i in range(ndefs):
        o = Out(r, comments, breaks, glue)
        o.n = n
        o.tok("def")
        o.tok(f"d{i}")
        o.tok(":")
        emit(o, gen(r, max(0, depth - 2), 3))
        o.first = False
        o.tok(":=")
        o.first = True
        emit(o, gen(r, depth, big))
        n = o.n
        text += "".join(o.parts) + "\n"
        if r.random() < comments:
            text += "\n"
        while r.random() < comments * 0.5:
            n += 1
            text += f"-- e{n}\n"
    return text


def batch(twin, folder, stage, paths):
    lst = folder / "list.txt"
    lst.write_text("".join(f"{p}\n" for p in paths))
    done = subprocess.run([*twin, "--stage", stage, "--batch", str(lst)], capture_output=True)
    out = done.stdout.decode()
    res = {}
    for block in out.split("\x1e")[1:]:
        path, rest = block.split("\n", 1)
        meta, body = rest.split("\n", 1)
        _, status, length, message = meta.split("\x1f", 3)
        res[path] = (int(status), body, message)
    if len(res) != len(paths):
        print("batch incomplete", stage, len(res), len(paths), done.stderr.decode()[-400:])
    return res


def comments_of(text):
    return [m.rstrip() for m in re.findall(r"--.*", text)]


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--twin", required=True, help="the twin: a command taking `--stage NAME --batch LIST`")
    ap.add_argument("--out", required=True, help="the folder for the generated files and outputs")
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--count", type=int, default=200, help="how many files to generate")
    ap.add_argument("--bin", default=str(ROOT / "target/release/stitchwort"), help="the Rust side's stitchwort")
    ap.add_argument("--rust", type=int, default=0, help="compare the first N files with `stitchwort fmt -`")
    ap.add_argument("--sketch", action="store_true", help="the twin has SW-3955's sketch stages")
    args = ap.parse_args()
    twin = args.twin.split()
    folder = Path(args.out).resolve()
    folder.mkdir(parents=True, exist_ok=True)
    r = random.Random(args.seed)
    paths = []
    for i in range(args.count):
        mode = i % 6
        comments = [0.0, 0.08, 0.25, 0.5, 0.15, 0.9][mode]
        breaks = [0.0, 0.1, 0.3, 0.1, 0.6, 0.2][mode]
        glue = [0.5, 0.3, 0.3, 0.0, 0.5, 0.2][mode]
        big = [40, 5, 5, 3, 3, 2][mode]
        p = folder / f"x{i}.sw"
        p.write_text(source(r, r.randint(1, 3), r.randint(1, 5), comments, breaks, glue, big))
        paths.append(str(p))
    run = lambda stage, files: batch(twin, folder, stage, files)
    first = run("text", paths)
    ok = [p for p in paths if p in first and first[p][0] == 0]
    stats = {"inputs": len(paths), "formatted": len(ok)}
    refusals = {}
    for p in paths:
        if p in first and first[p][0] != 0:
            key = first[p][2][:60]
            refusals[key] = refusals.get(key, 0) + 1
    outs = []
    for p in ok:
        q = p[:-3] + ".out.sw"
        Path(q).write_text(first[p][1])
        outs.append(q)
    second = run("text", outs)
    tidied_in = run("tidied", ok)
    tidied_out = run("tidied", outs)
    tree_out = run("tree", outs)
    checks = ["idem", "tree", "comments", "long", "rust"]
    if args.sketch:
        words_in, words_out = run("words", ok), run("words", outs)
        calm_in, calm_out = run("calmwords", ok), run("calmwords", outs)
        sketch_in, sketch_out = run("sketch", ok), run("sketch", outs)
        checks += ["words", "blanks", "calm", "nothang", "unsettled", "srcunsettled"]
    unflag = lambda t: re.sub(r"^(  above )?[B-] ", r"\1", t, flags=re.M)
    bad = {k: [] for k in checks}
    for n, (p, q) in enumerate(zip(ok, outs)):
        out = first[p][1]
        if q not in second or second[q][0] != 0 or second[q][1] != out:
            bad["idem"].append(p)
        if (q not in tidied_out or tidied_out[q][0] != 0 or tidied_in[p][1] != tidied_out[q][1]
                or tree_out.get(q, (0, ""))[1] != tidied_out[q][1]):
            bad["tree"].append(p)
        if comments_of(Path(p).read_text()) != comments_of(out):
            bad["comments"].append(p)
        if any(len(line) > 120 and "--" not in line for line in out.split("\n")):
            bad["long"].append(p)
        if n < args.rust:
            rust = subprocess.run([args.bin, "fmt", "-"], input=Path(p).read_bytes(), capture_output=True)
            if rust.stdout.decode() != out:
                bad["rust"].append(p)
        if args.sketch:
            if unflag(words_in[p][1]) != unflag(words_out[q][1]):
                bad["words"].append(p)
            elif words_in[p][1] != words_out[q][1]:
                bad["blanks"].append(p)
            if calm_in[p][1] != calm_out[q][1]:
                bad["calm"].append(p)
            if "hangs True" not in sketch_out[q][1]:
                bad["nothang"].append(p)
            if "settled1 True" not in sketch_out[q][1]:
                bad["unsettled"].append(p)
            if "settled1 True" not in sketch_in[p][1]:
                bad["srcunsettled"].append(p)
    print(stats, {k: len(v) for k, v in bad.items()})
    print("refusals:", sorted(refusals.items(), key=lambda kv: -kv[1])[:8])
    for k, v in bad.items():
        for p in v[:6]:
            print(k, p)


main()
