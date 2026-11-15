# When the formatter joins lines the author broke

**Status:** paper, 15 November 2026 (SW-3298, for D3605). Nothing is built.
It builds on [formatter-style.md](formatter-style.md) (the house style, in
use since SW-3194) and [formatter-architecture.md](formatter-architecture.md).

Claims are marked **[measured]** (a script over the reformat commit
`39de3aa7d` or the tracked `.sw` files at `397c2da84`; pattern-based, so
the counts are approximate), **[source]** (read in the printer, or in a
tool's own docs), **[from memory]** (how another tool behaves; not
rechecked here) or **[estimated]**.

## In plain words

**The problem.** The tree printer puts a construct on one line whenever it
fits in 120 characters, and keeps none of the author's line breaks, only
blank lines (D3558, D3560a). The 14 November reformat therefore joined
about 2,100 multi-line constructs onto one line [measured]. Most joins are
what we wanted: a short body moving up after `:=`, a header that fits.
But three kinds read worse joined, and the guide shows them:

- an `else if` chain becomes one line of up to 120 characters, so the
  guide's `grade` example is a single 119-character line;
- a data type whose constructors carry fields becomes one line
  (`type Expr = | Num (value: Int) | Add (left: Expr) (right: Expr) | …`,
  116 characters, in the guide's chapter on data);
- a record type of four or five fields becomes one line.

The guide's prose was written for the old layouts. Chapter 2's "split a
long condition before an operator" example is now a one-line condition,
and chapter 3 says "the house style for a declaration over several lines
… as above" under a record that is now on one line.

**What I recommend.** Keep the one-layout principle (no author hints) but
add two structural rules, of the kind rustfmt and elm-format have: an `if`
with an `else if` always goes one clause a line; and a type declaration
(constructors or record fields) goes on one line only if it fits in 80
characters, not 120. The guide's leading-operator example uses a
condition long enough that the formatter splits it itself. That re-breaks
the constructs that read worst, keeps short enumerations and small records
on one line (D3566 (b)), and changes about 130 files [measured].

## 1. What the reformat joined

A "join" here is a run of two or more code lines whose tokens all ended up
on one new line, found by aligning the old and new token streams of each
of the 1,322 files [measured]. Re-breaks (a header broken differently) are
not counted. **2,087 joins in 747 files, from 4,987 old lines**; 836 of the
joined lines are over 100 characters [measured].

| Kind | Joins | Files | Joined line > 100 | Example |
|---|---|---|---|---|
| Body moved up after `:=` (143 are `:= match … with`, D3553) | 827 | 399 | 410 | `def solvePart1 (db: Database): Nat := db.available.count (…)` |
| Data type, constructors joined | 392 | 220 | 26 | `type Result (a: Type) (e: Type): Type = \| Ok (value: a) \| Err (error: e)` |
| Call arguments joined | 233 | 124 | 100 | `Eq.trans (Eq.sym (…)) (Eq.trans (…) (…))` |
| Arm or lambda body moved up after `=>` | 211 | 114 | 116 | `\| Zero => omega` |
| Header lines joined | 177 | 107 | 112 | `theorem … ∀ (key: k) (lo hi: Option k) (t: Map.Tree k v)` |
| One-arm `match` joined | 99 | 69 | 22 | `match h with \| Both py m => Witness y (Both m qy)` |
| `if` / `else if` chain | 32 | 24 | 16 | `values.sw` `grade` (119) |
| Record type or interface | 29 | 24 | 1 | `type Console = { inputIsTerminal: Bool, outputIsTerminal: Bool, columns: Nat, rows: Nat }` |
| Pipeline (D3560b) | 26 | 21 | 14 | `ranges \|> .sort \|> .foldLeft [] absorb \|> .reverse` |
| Proof steps (`calc`, `rewrite`) | 26 | 16 | 8 | `_ = … := rewrite collapse _ 2 rfl _ (…)` |
| Operator chain | 16 | 9 | 3 | `values.sw` `validScore` (78) |
| Lists and other brackets | 15 | 11 | 7 | |

By area: examples 851, aoc 544, std 456, the guides 72 (36 files), games
28, other 136 [measured]. Data types by constructor count: 102 had one,
208 two, 46 three, 36 four or more; 283 of the 392 have constructors with
fields [measured]. The joined `if` chains are long: median 105 characters,
16 of 32 over 100.

**Where it hurt.** I read about 60 samples across the kinds. Bodies,
headers, arm bodies and one-arm matches joined well: that is fit-or-break
doing its job, as the style sheet predicted (S21, S29, D3571). The joins
that read worse are the ones whose parts are *alternatives or fields*,
where a column of them is a table the eye scans down:

```text
type Parse.Problem = | Expected (what: Text) | Literal (text: Text) | Literals (texts: List Text) | Message (text: Text)
```

(`crates/elab/src/std/Parse/Parse.sw:37`, exactly 120 characters, four
lines before), and long `if` chains like
`def grade … := if score ≥ 90 then "A" else if score ≥ 75 then "B" else if …`.
Short ones are fine: `type Direction = | Up | Right | Down | Left`,
`type Person = { name: Text, age: Nat }`.

**In the repo now** [measured]: 37 one-line `else if` chains (32 files, 27
over 80 characters) against 186 `else if` lines in broken chains; 475
one-line data types (84 over 80 characters, in 65 files) against 56
broken; 612 one-line record types and interfaces (40 over 80, in 38
files). 8,900 code lines are 101–120 characters long, in 1,112 files.

**What the guide lost** [measured]: 72 joins in 36 guide files (docs/guide
and web/guide), of which 20 data types, 7 record types, 2 `if` chains, 2
pipelines and the leading-operator example; the rest are bodies and
headers that read fine.

## 2. What other formatters do

| Tool | Width | Keeps the author's breaks? | Alternatives and fields |
|---|---|---|---|
| gofmt | none | yes, nearly all; it only re-indents and aligns [from memory] | struct fields as written; blocks (`if`, `switch`) always open |
| rustfmt | 100, plus narrower widths per construct ("small heuristics") | no | enum variants and struct fields in a definition always one per line [from memory]; a struct literal on one line only up to 18 characters of body, a struct variant 35, call arguments 60, `if … else` 50 [source: rustfmt Configurations.md]; `else if` chains always break [from memory] |
| Prettier | 80 | one hint: an object written with a newline after `{` stays open ("short multi-line objects are never collapsed"); since 3.5 `objectWrap: "collapse"` turns it off [source: prettier.io rationale] | everything else fit-or-break |
| Black | 88 | one hint: a "magic trailing comma" keeps a bracket open [from memory] | fit-or-break |
| Dart (tall style, 3.7) | 80 | none at first; the formatter added and removed trailing commas itself. Users pushed back, and 3.8 added `trailing_commas: preserve`, where a trailing comma forces the split [source: dart_style changelog] | |
| zig fmt | none | the trailing comma is the switch: with it, one item per line; without, one line [from memory] | |
| Ormolu / Fourmolu | none | yes: each construct is one line or several, as the author had it [from memory] | |
| elm-format | none | for lists, records and calls, a newline anywhere opens the whole construct [from memory] | a custom type's constructors always one per line; `if … then … else` always open [from memory] |
| scalafmt | 80 | `newlines.source`: `classic` (default) keeps some breaks, `keep` keeps them, `fold` ignores them, `unfold` breaks all [from memory] | |
| gleam format | 80 | none [from memory] | a custom type's variants always one per line [from memory] |

Two patterns. **Hint formatters** (Prettier, Black, zig, Dart 3.8,
Ormolu, gofmt) let the author choose open or closed, so the same code has
two layouts; the more width-driven ones (Prettier, Dart) added the hint
after users complained that short open constructs collapsed. **No-hint
formatters** (rustfmt, elm-format, gleam) instead make the constructs
people want vertical *always* vertical, or give them a narrower width:
none of them puts an enum with fields or an `else if` chain on one line
just because it fits the page.

## 3. Options

**A. Keep author breaks for some constructs** (Prettier's object rule):
a data type, record type or `if` chain written over several lines stays
open. *Guide:* fixes new examples; the 14 Nov joins are already one line,
so the guide's examples must be re-broken by hand. *Repo:* no file changes
on its own; restoring the ~450 joined types and chains would need a
script over the pre-reformat text [estimated: 1–2 h]. *Cost:* reverses
D3560a; two layouts for the same code, which is what agents produce most
of; idempotent, since an open construct stays open. Printer: a
`BreakParent` when the source had a newline between the first two items
[source: `rules.rs` `data_type`, `if_` build one group each].

**B. Structural rules, no hints** (rustfmt, elm-format, gleam):

- **B1.** An `if` with at least one `else if` always goes one clause a
  line; a plain `if c then a else b` still fits or breaks. The style
  sheet's own reason for S19 ("it reads as a table of cases") is D3566's
  reason for arms. *Repo:* 37 chains in 32 files re-break.
- **B2.** A type declaration's constructors or record fields go on one
  line only within 80 characters, then one per line (a narrower width for
  this one group, as rustfmt does). Short enumerations and small records
  stay on one line, as D3566 (b) and S15 wanted; `Parse.Problem`, the
  guide's `Expr` (116) and `type Console` (89) open. *Repo:* 84 data types
  and 40 record types, in about 100 files.
- **B2′** (instead of B2). Constructors one per line whenever two or more
  carry fields. Simpler to state, but `type Result = | Ok (value: a) |
  Err (error: e)` (72) and 237 others break, in 160 files: most of D3566
  (b) undone.

*Guide:* `grade`, `Expr`, `Event`, two web/guide variant pages and three
records re-open. The leading-operator example still joins: no structural
rule should break a 78-character condition. *Cost:* small, one group
each in `rules.rs` plus tests [estimated: 1–2 h Sonnet], and one
reformat commit (B1+B2: about 130 files [measured]).

**C. A narrower width everywhere** (100 or 80). Breaks the long joined
lines too, but changes far more than the problem: 8,900 code lines are
101–120 characters [measured], so 100 alone touches over 1,000 files, and
80 most of the repo. It reverses D1014 for every construct to fix three.

**D. Leave the printer; rewrite the guide's examples.** An example can
only show a multi-line layout if it is too long for one line. A real
`grade` with longer branches, or a real five-condition validity check,
would do; padding examples to 121 characters would not. *Repo:* guide
only (about 10 snippets and their prose). *Cost:* leaves the repo's 84
long one-line data types and 37 `if` chains as they are; the guide then
teaches a layout the formatter only produces for long code.

## 4. Recommendation

**B1 + B2, and D for the leading-operator example only.**

- No author hints, so D3560a and the one-layout principle stand: the
  layout is still a function of the tree.
- The re-broken constructs are exactly the ones that read worst joined,
  and the rules restore them without a restoring script, since they don't
  depend on how the code was written.
- Short enumerations, small records and plain `if`s keep the one-line form
  Matt chose in D3566 (b) and S15.
- The leading-operator example becomes a condition long enough that the
  formatter splits it before `&&` (S27): the guide then shows the rule the
  formatter applies, not a layout it would undo. The prose in chapter 2
  ("can be laid out one per line, or kept on one line") and chapter 3
  ("as above" under a now one-line record) is updated with it.
- 80 for B2 is a judgement: 60 would open `type Shape = | Circle (radius:
  Nat) | Rect (width: Nat) (height: Nat) | Dot` (75) too, which reads fine
  on one line. I'd treat the exact number as mine to tune.

Work if yes: one Sonnet lane [estimated: 2–3 h]: B1 and B2 in
`crates/fmt/src/printer/rules.rs` with tests, S14/S15/S19 in the style
sheet, the reformat (about 130 files, in `.git-blame-ignore-revs`), and the
guide's examples and prose.

## Findings worth tickets

- `docs/guide/03-data.md:113` says "as above" under a record that is now
  on one line; fix with the guide pass whatever D3605's answer.
- S21 predicted "about 90 arms" would join their body onto the `=>` line;
  211 did [measured]. Not a problem (they read well), but the style
  sheet's figure is off.
- 102 one-constructor data types were joined (`type Box … = | MkBox (item:
  k)`); fine, but a single-constructor type with fields is usually a
  record in disguise. A lint, not a formatter rule.

---

**D3605: how should the formatter lay out `else if` chains and type
declarations?**
*The problem:* the tree printer puts anything that fits in 120 characters
on one line, so the 14 Nov reformat joined 32 `else if` chains (median 105
characters) and 421 data and record types onto single lines, including the
guide's `grade` and `Expr` examples (119 and 116 characters); a column of
cases or constructors became one long line that is hard to scan.
*The change:* two structural rules, no author hints: an `if` with an
`else if` always goes one clause a line, and a type declaration's
constructors or fields go on one line only within 80 characters, otherwise
one per line. The guide's leading-operator example becomes a condition
long enough that the formatter splits it.
*What it should do:* re-breaks 37 `if` chains, 84 data types and 40
record types, about 130 files in one reformat commit [measured]; short
enumerations (`type Direction = | Up | Right | Down | Left`) and small
records stay on one line; still one layout for each piece of code.
**[rec: yes]**
