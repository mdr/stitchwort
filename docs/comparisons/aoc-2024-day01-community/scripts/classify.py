"""Tabulate the fetched proof-language day 1 files.

Usage: python3 -I classify.py FILES_DIR > table.tsv

For each .lean .idr .agda .dfy .v .kk .roc file: code lines (non-blank,
non-comment), part 2's method by regex (map: a hash/RB map, dict or multiset;
count: count/filter per left id; merge: a walk over both sorted lists),
how bad input is handled (crash: `!`, unwrap, crash, panic, get!, head!;
drop: filterMap, mapMaybe, getD, a default; typed: Except, Result, Maybe
returned to main), whether the input is pasted into the source, theorem-like
declarations, `sorry`/`admit`/`assume`, and tests (#guard, example, #eval
with a recorded answer, expect, Refl). The regexes are rough; the note's
table was checked against the files by hand.
"""
import os
import re
import sys

d = sys.argv[1]
EXTS = (".lean", ".idr", ".agda", ".dfy", ".v", ".kk", ".roc")
COMMENT = re.compile(r"^\s*(--|//|\(\*|/-|\*|#(?!guard|eval|check))")
print("file\tlines\tpart2\tbad input\tpasted\ttheorems\tholes\ttests")
for f in sorted(os.listdir(d)):
    if not f.endswith(EXTS):
        continue
    src = open(os.path.join(d, f), errors="replace").read()
    lines = [l for l in src.splitlines() if l.strip() and not COMMENT.match(l)]
    code = "\n".join(lines)
    if re.search(r"HashMap|RBMap|Dict\.|TreeMap|SortedMap|multiset|AssocList|insertWith|fromListWith|frequenc|Std\.HashMap", code):
        p2 = "map"
    elif re.search(r"count|filter|countIf|count_occ|countOccurrences", code):
        p2 = "count"
    elif re.search(r"span|dropWhile|takeWhile|binSearch", code):
        p2 = "merge"
    else:
        p2 = "?"
    if re.search(r"toNat!|toInt!|get!|head!|\[\d\]!|unwrap|crash|panic!|fromJust|believe_me|!\s*$|\.get!|!\)", code):
        bad = "crash"
    elif re.search(r"Except|Result|Either|Maybe .*main|Option .*main", code):
        bad = "typed"
    elif re.search(r"filterMap|mapMaybe|getD|withDefault|toNat\?|parseInteger|readMaybe|Option", code):
        bad = "drop"
    else:
        bad = "?"
    pasted = "yes" if len(re.findall(r"\b\d{5}\b", code)) > 500 else ""
    thms = len(re.findall(r"^\s*(private\s+)?(theorem|lemma|Lemma|Theorem)\b", code, re.M))
    holes = len(re.findall(r"\bsorry\b|\badmit\b|Admitted|assume\s*\{:axiom\}|postulate", code))
    tests = len(re.findall(r"#guard|^\s*example\b|^\s*expect\b|= Refl|#eval.*--\s*\d|info:", code, re.M))
    print(f"{f}\t{len(lines)}\t{p2}\t{bad}\t{pasted}\t{thms}\t{holes}\t{tests}")
