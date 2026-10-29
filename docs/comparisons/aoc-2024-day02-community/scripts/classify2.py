"""Tag each fetched day 2 file by its part 2 method and any proof content.

Usage: python3 -I classify2.py PICKED_TSV FILES_DIR OUT_TSV

Regex tags, to be read by hand where they matter (they are upper bounds):
  day2     the file looks like day 2 (mentions safe/levels/reports/dampen)
  brute    builds the report with each level removed (removeAt, eraseIdx,
           inits/tails, take ++ drop, patch, deleteAt, List.delete_at, ...)
  proof    theorem, lemma, ensures, Qed, proof terms, sorry, decide
  lines    non-blank, non-comment lines
Writes OWNER/REPO, language, path, the tags, and the line count.
"""
import os
import re
import sys

BRUTE = re.compile(r"removeAt|remove_at|eraseIdx|erase_idx|deleteAt|delete_at|removeNth|remove_nth|eraseAt|dropNth|"
                   r"inits|tails|\.patch\(|take\s*\(?\s*\w+\s*\)?\s*\+\+|take\s+i\b|List\.take|Enum\.take|"
                   r"splitAt|split_at|List\.delete|without|dampen|removeOne|remove_one|withoutIndex|exclud|"
                   r"filteri|filter_with_index|with_index|withIndex|zipWithIndex|mapi|indexed|combinations|"
                   r"\[\s*0\s*\.\.|range|seq\[|\bdrop\b", re.I)
PROOF = re.compile(r"\btheorem\b|\blemma\b|\bensures\b|\brequires\b|\bQed\b|\bDefined\.|\bsorry\b|\bdecide\b|"
                   r"\bProof\b|\bRefl\b|\bpostulate\b|\binvariant\b|\bdecreases\b|#guard|#eval|example\s*:", re.I)
DAY2 = re.compile(r"safe|level|report|dampen", re.I)
COMMENT = re.compile(r"^\s*(--|//|#|;|\(\*|\*|%)")

picked = [l.rstrip("\n").split("\t") for l in open(sys.argv[1]) if l.strip()]
seen = set()
with open(sys.argv[3], "w") as f:
    for repo, path, lang in picked:
        name = repo.replace("/", "_") + "__" + path.replace("/", "_")
        if name in seen:
            continue
        seen.add(name)
        fp = os.path.join(sys.argv[2], name)
        if not os.path.exists(fp):
            continue
        text = open(fp, errors="replace").read()
        lines = sum(1 for l in text.splitlines() if l.strip() and not COMMENT.match(l))
        tags = [t for t, rx in (("day2", DAY2), ("brute", BRUTE), ("proof", PROOF)) if rx.search(text)]
        proofs = sorted({m.group(0).lower() for m in PROOF.finditer(text)})
        f.write(f"{repo}\t{lang}\t{path}\t{','.join(tags)}\t{lines}\t{' '.join(proofs)}\n")
print(len(seen))
