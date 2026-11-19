#!/usr/bin/env python3
"""Delete the spelled arguments (`[p := …]`, `[j := …]`) a proof step does
not need, and keep the ones it does. A "step" is a run of consecutive
lines that each open a spelled group (a line starting `[p := `, `[q := `,
`[j := ` or `[k := ` and running to its closing bracket), under one head
line (`givesThen`, `followsThen`, …). The tool

  1. deletes every step's spelled groups and checks the file's namespace;
  2. for each error it reports, puts back the nearest step above the
     error's line (preferring the step whose head is the function the
     error names) and checks again, until the namespace is clean;
  3. tries dropping each put-back step on its own (unless --no-prune)
     and keeps the drop when the namespace still checks.

Statements and programs are untouched: only spelled arguments go, so what
is proved is the same. The file is rewritten in place after every check;
rerun after an interruption and it continues from the saved state
(`$TMPDIR/spellings/<file>.json`). Run it from anywhere inside the repo,
in the background for big files (a check of a namespace takes 10 to 60 s
and a file may need dozens).

  tools/fmt/dev/spellings.py [--sw PATH] [--no-prune] FILE.sw
  task fmt:unspell -- FILE.sw

`--sw` is the release CLI (default `target/release/stitchwort` in the
repo). Format the file afterwards (`stitchwort fmt FILE.sw`).
"""
import json, os, re, subprocess, sys, tempfile
from pathlib import Path

SPELLED = re.compile(r"^\s*\[(p|q|j|k) := ")


def groups(lines):
    out, i = [], 0
    while i < len(lines):
        if SPELLED.match(lines[i]):
            s, depth = i, 0
            while i < len(lines):
                depth += lines[i].count("[") - lines[i].count("]")
                if depth <= 0:
                    break
                i += 1
            out.append([s, i])
        i += 1
    return out


def steps(lines):
    """[(first line, last line, head function name)] of each step."""
    out = []
    for s, e in groups(lines):
        if out and out[-1][1] + 1 == s:
            out[-1][1] = e
        else:
            h = lines[s - 1].strip().lstrip("(") if s else ""
            out.append([s, e, h.split()[0] if h else "?"])
    return out


def main():
    args = sys.argv[1:]
    prune = "--no-prune" not in args
    args = [a for a in args if a != "--no-prune"]
    sw = None
    if "--sw" in args:
        k = args.index("--sw")
        sw = args[k + 1]
        del args[k : k + 2]
    if len(args) != 1:
        sys.exit(__doc__)
    path = Path(args[0]).resolve()
    root = next(p for p in path.parents if (p / "stitchwort.yaml").exists())
    sw = sw or str(root.parent.parent / "target/release/stitchwort")
    text = path.read_text()
    ns = re.search(r"^namespace (\S+)", text, re.M).group(1)
    state_dir = Path(os.environ.get("TMPDIR", tempfile.gettempdir())) / "spellings"
    state_dir.mkdir(exist_ok=True)
    state = state_dir / (path.name + ".json")
    if state.exists():
        saved = json.loads(state.read_text())
        orig, keep = saved["orig"].split("\n"), set(saved["keep"])
    else:
        orig, keep = text.split("\n"), set()
        state.write_text(json.dumps({"orig": text, "keep": []}))
    st = steps(orig)
    print(f"{path.name}: {len(st)} steps, namespace {ns}", flush=True)

    def write(keep):
        rm = set()
        for k, (s, e, _) in enumerate(st):
            if k not in keep:
                rm.update(range(s, e + 1))
        kept = [i for i in range(len(orig)) if i not in rm]
        path.write_text("\n".join(orig[i] for i in kept))
        state.write_text(json.dumps({"orig": "\n".join(orig), "keep": sorted(keep)}))
        return kept

    def check():
        r = subprocess.run(["nice", "-n", "15", sw, "check", ns], cwd=root, capture_output=True, text=True)
        return r.returncode, r.stdout + r.stderr

    for rnd in range(200):
        kept = write(keep)
        rc, out = check()
        if rc == 0:
            break
        blocks = re.split(r"^\[E-", out, flags=re.M)[1:]
        added = 0
        for blk in blocks:
            m = re.search(rf"{re.escape(path.name)}:(\d+):\d+ \]", blk)
            if not m or int(m.group(1)) - 1 >= len(kept):
                continue
            oi = kept[int(m.group(1)) - 1]
            fn = re.search(r"is `([\w.]+)`'s implicit", blk)
            cands = [k for k, (s, e, h) in enumerate(st) if k not in keep and s <= oi]
            if not cands:
                continue
            pick = cands[-1]
            if fn:
                short = fn.group(1).split(".")[-1]
                pick = next((k for k in reversed(cands) if st[k][2].split(".")[-1] == short), pick)
            keep.add(pick)
            added += 1
        print(f"round {rnd}: kept {len(keep)} of {len(st)}", flush=True)
        if not added:
            sys.exit("stuck: errors not at any spelled step:\n" + out[:2000])
    if prune:
        for k in sorted(keep):
            t = keep - {k}
            write(t)
            if check()[0] == 0:
                keep = t
                print(f"dropped step {k}", flush=True)
    write(keep)
    state.unlink()
    lines = sum(e - s + 1 for s, e, _ in st)
    kl = sum(st[k][1] - st[k][0] + 1 for k in keep)
    print(f"{path.name}: deleted {len(st) - len(keep)} of {len(st)} steps, kept {len(keep)}; lines saved {lines - kl}")


main()
