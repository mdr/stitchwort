"""Summarise the archived Day 5 megathread (Arctic Shift tree.json).

Usage: python3 -I langs5.py TREE_JSON OUT_DIR

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
    "comparator sort (cmp_to_key, sortBy, sortWith, Comparator)": r"cmp_to_key|sortBy|sortWith|sort_by|Comparator|compareBy|\bcmp\b|sort\(\s*\(?\s*[a-z]\s*,\s*[a-z]|sort_unstable_by|Ordering::|instance Ord|IComparer|\.sort\(\s*\|",
    "topological sort / Kahn / graphlib": r"topolog|toposort|top_sort|tsort|kahn|graphlib|TopologicalSorter",
    "swap until fixed (bubble / repeated swaps)": r"bubble|swap",
    "insertion / build by placing": r"insertion sort|insert(ing)? (each|it|them|the page)",
    "mentions transitivity": r"transitiv",
    "mentions a cycle in the rules": r"cycl|loop in the (rules|graph)",
    "mentions total order / partial order": r"total order|totally ordered|partial order|strict weak|linear order",
    "says the shortcut works only because of the input": r"(lucky|happens to|happen to|input is (nice|kind|friendly)|assum)",
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
