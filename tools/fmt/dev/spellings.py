#!/usr/bin/env python3
"""Delete the spelled arguments (`[p := …]`, `[alike := …]`, …) a proof
step does not need, and keep the ones it does. A "unit" is a run of
spelled groups with only whitespace between them (a group may start a
line or sit in the middle of one, and may span lines), such as the
`[p := …]` / `[j := …]` lines under a `givesThen`, or `[p := …] [q := …]`
after `followsThen`. The tool

  1. deletes every unit and checks the file's namespace;
  2. for each error it reports, puts back the nearest unit before the
     error (preferring the unit whose head, the function it follows, is the
     one the error names) and checks again, until the namespace is clean;
  3. tries dropping each put-back unit whole (unless --no-prune); if the
     whole unit does not check, it tries each of its groups on its own and
     keeps the drops that check (so `[p := …] [q := …]` can keep one and
     drop the other).

Statements and programs are untouched: only spelled arguments go, so what
is proved is the same. Groups are skipped on `--` comment lines and on the
lines of a `theorem`/`def`/`lemma`/`fn` header (a statement's argument can't
be told apart from a proof's by name alone); review the diff for statements
that continue past a header line. The file is rewritten in place after every
check; rerun after an interruption and it continues from the saved state
(`$TMPDIR/spellings/<file>.json`). Run it in the background for big files
(a check of a namespace takes 10 to 60 s and a file may need dozens).

  tools/fmt/dev/spellings.py [--sw PATH] [--names a,b,…|all] [--no-prune] FILE.sw
  tools/fmt/dev/spellings.py --list [--names …] FILE.sw
  task fmt:unspell -- FILE.sw

  --names   which spelled names to try (default: p,q,j,k,alike,g2,spec,
            weaker,holds,inv,x,first,second,self,selfTwin,item,start,
            later,goals; `all` is every name, which includes the type
            arguments `a`, `b` of statements)
  --list    only count the groups per name, change nothing
  --no-prune  skip step 3
  --sw      the release CLI (default `target/release/stitchwort` in the repo)

Format the file afterwards (`stitchwort fmt FILE.sw`). At the end it prints
the deleted/kept group counts per name and the lines saved.
"""
import json, os, re, subprocess, sys, tempfile
from collections import Counter
from pathlib import Path

DEFAULT_NAMES = "p,q,j,k,alike,g2,spec,weaker,holds,inv,x,first,second,self,selfTwin,item,start,later,goals"
OPEN = re.compile(r"\[(\w+) := ")
HEADER = re.compile(r"^\s*(theorem|def|lemma|fn|pub|private)\b")


def spans(text, names):
    """[(start, end, name)] of each top-level spelled group (end exclusive)."""
    out, i = [], 0
    for m in OPEN.finditer(text):
        s = m.start()
        if s < i or (names and m.group(1) not in names):
            continue
        ls = text.rfind("\n", 0, s) + 1
        line = text[ls : text.find("\n", s) if "\n" in text[s:] else len(text)]
        if line.lstrip().startswith("--") or HEADER.match(line):
            continue
        depth, j = 0, s
        while j < len(text):
            c = text[j]
            depth += (c == "[") - (c == "]")
            j += 1
            if depth == 0:
                break
        if depth != 0:
            continue
        out.append((s, j, m.group(1)))
        i = j
    return out


def parse(text, names):
    """(groups, units): groups are [(start, end, name)]; a unit is
    [start, end, head, [names], [group indices]], a run of groups split only
    by whitespace."""
    gs = spans(text, names)
    out = []
    for gi, (s, e, n) in enumerate(gs):
        if out and not text[out[-1][1] : s].strip():
            out[-1][1] = e
            out[-1][3].append(n)
            out[-1][4].append(gi)
            continue
        ls = text.rfind("\n", 0, s) + 1
        before = text[ls:s]
        if before.strip():
            tok = before.split()[-1]
        else:
            prev = text[:ls].rstrip().split("\n")[-1].split() if text[:ls].strip() else []
            tok = prev[0] if prev else "?"
        out.append([s, e, tok.lstrip("(") or "?", [n], [gi]])
    return gs, out


def render(orig, gs, keep):
    """The text with the groups not in `keep` deleted, and the kept segments
    [(out_start, orig_start, length)] to map error positions back."""
    pieces, segs, pos, outlen = [], [], 0, 0
    for k, (s, e, _) in enumerate(gs):
        if k in keep:
            continue
        a = s
        while a > pos and orig[a - 1] in " \t\n":
            a -= 1
        ws = orig[a:s]
        if ws and a > 0 and "--" in orig[orig.rfind("\n", 0, a) + 1 : a]:
            a += ws.rfind("\n") + 1 if "\n" in ws else 0
        pieces.append(orig[pos:a])
        segs.append((outlen, pos, a - pos))
        outlen += a - pos
        pos = e
    pieces.append(orig[pos:])
    segs.append((outlen, pos, len(orig) - pos))
    return "".join(pieces), segs


def to_orig(segs, off):
    for o, s, n in reversed(segs):
        if off >= o:
            return s + min(off - o, n)
    return 0


def prune(keep, us, write, check):
    """Drop each kept unit whole if it checks, else try its groups one at a
    time. Returns the new set of kept group indices."""
    for k, u in enumerate(us):
        groups = u[4]
        if not any(g in keep for g in groups):
            continue
        t = keep - set(groups)
        write(t)
        if check()[0] == 0:
            keep = t
            print(f"dropped unit {k}", flush=True)
            continue
        for g in groups:
            if g not in keep:
                continue
            t = keep - {g}
            write(t)
            if check()[0] == 0:
                keep = t
                print(f"dropped group {g}", flush=True)
    return keep


def main():
    args = sys.argv[1:]
    do_prune = "--no-prune" not in args
    args = [a for a in args if a != "--no-prune"]
    list_only = "--list" in args
    args = [a for a in args if a != "--list"]
    sw = None
    names = DEFAULT_NAMES
    for flag in ("--sw", "--names"):
        if flag in args:
            k = args.index(flag)
            val = args[k + 1]
            del args[k : k + 2]
            if flag == "--sw":
                sw = val
            else:
                names = val
    names = None if names == "all" else set(names.split(","))
    if len(args) != 1:
        sys.exit(__doc__)
    path = Path(args[0]).resolve()
    text = path.read_text()
    if list_only:
        c = Counter(n for _, _, n in spans(text, names))
        print(path.name, dict(c))
        return
    root = next(p for p in path.parents if (p / "stitchwort.yaml").exists())
    sw = sw or str(root.parent.parent / "target/release/stitchwort")
    ns = re.search(r"^namespace (\S+)", text, re.M).group(1)
    state_dir = Path(os.environ.get("TMPDIR", tempfile.gettempdir())) / "spellings"
    state_dir.mkdir(exist_ok=True)
    state = state_dir / (path.name + ".json")
    if state.exists():
        saved = json.loads(state.read_text())
        orig = saved["orig"]
        gs, us = parse(orig, names)
        if saved.get("v") == 2:
            keep = set(saved["keep"])
        else:
            # Old state held unit indices; keep every group of those units.
            keep = {g for k in saved.get("keep", []) if 0 <= k < len(us) for g in us[k][4]}
    else:
        orig, keep = text, set()
        gs, us = parse(orig, names)
        state.write_text(json.dumps({"v": 2, "orig": text, "keep": []}))
    print(f"{path.name}: {len(us)} units, namespace {ns}", flush=True)

    def write(keep):
        out, segs = render(orig, gs, keep)
        path.write_text(out)
        state.write_text(json.dumps({"v": 2, "orig": orig, "keep": sorted(keep)}))
        return out, segs

    def check():
        r = subprocess.run(["nice", "-n", "15", sw, "check", ns], cwd=root, capture_output=True, text=True)
        return r.returncode, r.stdout + r.stderr

    for rnd in range(300):
        out, segs = write(keep)
        rc, msg = check()
        if rc == 0:
            break
        starts = [0]
        for m in re.finditer("\n", out):
            starts.append(m.end())
        added = 0
        for blk in re.split(r"^\[E-", msg, flags=re.M)[1:]:
            m = re.search(rf"{re.escape(path.name)}:(\d+):(\d+) \]", blk)
            if not m or int(m.group(1)) > len(starts):
                continue
            off = starts[int(m.group(1)) - 1] + int(m.group(2)) - 1
            oi = to_orig(segs, off)
            fn = re.search(r"is `([\w.]+)`'s implicit", blk)
            shown = [int(n) for n in re.findall(r"^\s*(\d+) │", blk, flags=re.M) if 0 < int(n) <= len(starts)]
            end = to_orig(segs, starts[max(shown)] if shown else off)
            unit_kept = [bool(set(u[4]) & keep) for u in us]
            inside = [k for k, u in enumerate(us) if not unit_kept[k] and oi <= u[0] <= end]
            cands = [k for k, u in enumerate(us) if not unit_kept[k] and u[0] <= oi]
            if inside:
                cands = inside
            if not cands:
                continue
            pick = cands[-1] if not inside else cands[0]
            if fn:
                short = fn.group(1).split(".")[-1]
                pick = next((k for k in reversed(cands) if us[k][2].split(".")[-1] == short), pick)
            keep.update(us[pick][4])
            added += 1
        print(f"round {rnd}: kept {len(keep)} of {len(us)}", flush=True)
        if not added:
            sys.exit("stuck: errors not at any spelled unit:\n" + msg[:2000])
    if do_prune:
        keep = prune(keep, us, write, check)
    write(keep)
    state.unlink()
    deleted, kept = Counter(), Counter()
    for g, (_, _, n) in enumerate(gs):
        (kept if g in keep else deleted)[n] += 1
    print(f"{path.name}: deleted {sum(deleted.values())} groups {dict(deleted)}, kept {sum(kept.values())} {dict(kept)}")
    print("run `stitchwort fmt` on the file; lines saved: see git diff --stat")


if __name__ == "__main__":
    main()
