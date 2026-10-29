"""Summarise the archived Day 9 megathread (Arctic Shift tree.json).

Usage: python3 -I langs9.py TREE_JSON OUT_DIR

Writes to OUT_DIR:
  langs.txt   language tag counts over live top-level comments
  words.txt   how many live top-level comments match each method regex
              (upper bounds: a word can match in a comment about something else)
  fp.txt      the full text of every comment in a functional, proof or niche
              language, with author, permalink and whether code is inline
Prints the headline counts.
"""
import collections
import json
import os
import re
import sys

tree = json.load(open(sys.argv[1]))["data"]
out = sys.argv[2]

top = [c["data"] if "data" in c and "body" in c.get("data", {}) else c for c in tree]
top = [c for c in top if "body" in c]
live = [c for c in top if c["body"] not in ("[deleted]", "[removed]") and c.get("author") != "[deleted]"]

TAG = re.compile(r"\[\s*language\s*:\s*([^\]]+)\]", re.I)
ALIAS = {"python3": "Python", "python 3": "Python", "py": "Python", "c#": "C#", "csharp": "C#",
         "f#": "F#", "fsharp": "F#", "js": "JavaScript", "javascript": "JavaScript",
         "typescript": "TypeScript", "ts": "TypeScript", "golang": "Go", "go": "Go",
         "c++": "C++", "cpp": "C++", "rust": "Rust", "lean": "Lean", "lean4": "Lean",
         "lean 4": "Lean", "haskell": "Haskell", "ocaml": "OCaml", "scala": "Scala",
         "scala 3": "Scala", "elixir": "Elixir", "clojure": "Clojure", "gleam": "Gleam",
         "common lisp": "Common Lisp", "commonlisp": "Common Lisp", "lisp": "Common Lisp",
         "racket": "Racket", "scheme": "Scheme", "guile": "Scheme", "guile scheme": "Scheme",
         "chez scheme": "Scheme", "dafny": "Dafny", "idris": "Idris", "idris2": "Idris",
         "agda": "Agda", "koka": "Koka", "roc": "Roc", "unison": "Unison", "elm": "Elm",
         "kotlin": "Kotlin", "java": "Java", "ruby": "Ruby", "julia": "Julia", "zig": "Zig",
         "swift": "Swift", "c": "C", "r": "R", "prolog": "Prolog", "erlang": "Erlang",
         "admiran": "Admiran", "effekt": "Effekt", "uiua": "Uiua", "janet": "Janet"}
FP = {"Haskell", "OCaml", "Scala", "F#", "Elixir", "Clojure", "Gleam", "Common Lisp", "Racket",
      "Scheme", "Dafny", "Idris", "Agda", "Koka", "Roc", "Unison", "Elm", "Lean", "Prolog",
      "Erlang", "Admiran", "Effekt", "Janet", "Coq", "Rocq", "F*", "Isabelle", "Purescript",
      "Smalltalk", "Lily", "Tailspin", "Kenpali", "Jactl", "SML", "Standard ML", "Emacs Lisp",
      "Factor", "Mercury", "Lua", "Uiua", "Dyalog APL", "APL", "BQN", "K", "Q", "Nix"}


def langs(body):
    body = body.replace("\\", "")
    res = []
    for m in TAG.finditer(body):
        for part in re.split(r"[,/+&]| and ", m.group(1)):
            p = part.strip().strip("*`").strip()
            if p:
                res.append(ALIAS.get(p.lower(), p[:1].upper() + p[1:]))
    return res


cnt = collections.Counter()
fp = []
for c in live:
    ls = set(langs(c["body"]))
    cnt.update(ls)
    if ls & FP:
        fp.append((sorted(ls & FP), c))

with open(os.path.join(out, "langs.txt"), "w") as f:
    for k, v in cnt.most_common():
        f.write(f"{v}\t{k}\n")

WORDS = {
    "compress": r"compress",
    "ray cast / crossing": r"ray[- ]?cast|crossing number|even[- ]odd|odd number of|parity",
    "point in polygon": r"point[- ]in[- ]polygon|inside the polygon|pip\b",
    "flood fill": r"flood",
    "prefix sum / summed-area": r"prefix[- ]?sum|summed[- ]area|integral image|2d prefix|cumulative",
    "edge intersects rectangle": r"intersect|crosses the rectangle|cross(es)? (the|any) (edge|line)",
    "AABB / bounding box": r"aabb|bounding box",
    "shapely / geometry lib": r"shapely|geo crate|\bgeo\b|jts|clipper|polygon library|turf",
    "shoelace": r"shoelace",
    "sort by area": r"sort(ed)? (the |all )?(pairs|rectangles|candidates)? ?by area|largest first|descending",
    "input shape (circle / spike / notch)": r"circle|pac-?man|notch|spike|the shape of the input|weird shape|visuali[sz]",
    "general solution doubt": r"not (a )?general|doesn'?t work for (all|every|general)|only works (because|for (my|this))|edge case|counterexample|concave",
    "z3 / SAT / LP": r"\bz3\b|\bsat\b solver|linear programming",
}
with open(os.path.join(out, "words.txt"), "w") as f:
    for name, rx in WORDS.items():
        n = sum(1 for c in live if re.search(rx, c["body"], re.I))
        f.write(f"{n}\t{name}\n")

with open(os.path.join(out, "fp.txt"), "w") as f:
    for ls, c in fp:
        code = "    " in c["body"] or "```" in c["body"]
        f.write(f"===== {','.join(ls)} | {c['author']} | code={code} | "
                f"https://www.reddit.com{c.get('permalink', '')}\n{c['body']}\n\n")

tagged = sum(1 for c in live if langs(c["body"]))
code = sum(1 for c in live if "    " in c["body"] or "```" in c["body"])
print(f"top-level {len(top)}, live {len(live)}, tagged {tagged}, with code {code}, fp {len(fp)}")
