# Hammer stage 0: does an SMT fact-finder pay here?

*SW-3586, Opus lane, 16 November 2026. A measured experiment (D3655, Matt, 16 Nov 2026: "yes,
run a hammer experiment"); no product code changed. Run against `main` at `67f20b28e` (after
SW-3564's proof vocabulary: `arithmetic`, `byComputing`, `rewrite … then`), with a frozen copy
of the release CLI built from it, and cvc5 1.4.0 from nixpkgs. The scripts are scratch files,
described in §7.*

The rule, fixed before the experiment (readable-proofs.md §3.3, R9, D-c): the solver's answer
is only a hint about which facts suffice; what goes in the file is ordinary Stitchwort source,
checked by the kernel as usual; no solver at check time; nothing added to the trusted base.

## 1. Summary

**The problem.** Agents spend attempts finding which facts close a goal. A hammer (Sledgehammer,
CoqHammer) sends the goal, its hypotheses and a few hundred library facts to an external solver,
and turns the solver's answer into a proof. readable-proofs.md R9 asked whether a thin one
(cvc5 for the facts, Stitchwort's own closers for the proof) would pay here before any solver
joins the toolchain.

**What was measured** (160 real leaf goals, 82 from AoC 2020 and 78 from the toy formatter):

| | goals | share |
|---|---|---|
| cvc5 proved the goal (unsat) | 45 of 160 | 28% |
| ... and Stitchwort's own closers, given exactly the core's facts, then closed it (kernel-checked) | 29 of 160 | 18% (64% of the 45) |
| Plain `arithmetic` or `cases`, with no hint at all, closed it | 64 of 153 checkable | 42% |
| **Closed by the hammer but not by plain `arithmetic`/`cases`** | **0** | **0%** |
| Closed by plain `arithmetic`/`cases` but not proved by cvc5 | 38 | |

Solver time is negligible (median 0.02 s, max 0.29 s); the cost is premise selection
(`stitchwort search`, median 5.2 s per query on AoC, 1.8 s on the toy) and the checks
(median 0.7 s per `check --only`).

**The answer is no, not now.** On this corpus the hammer found nothing that Stitchwort's own
closers didn't already find unaided, and missed 38 goals they close. The reason is structural,
not a tuning problem: Stitchwort's `arithmetic` and `cases` work *after computing*, so a
definition such as `breakColumn` or `Operator.level` unfolds by itself, while the solver sees
only an uninterpreted symbol and needs the definition's equations as facts. Every one of the
seven cores that used a library lemma was of this kind (five definition equations, two
spurious). The goals where premise selection really mattered (65 of 160 originals name a fact
from outside the hypotheses) need nonlinear lemmas, inductive predicates or recursion facts that
a first-order translation of `search` hits doesn't reach: cvc5 proved 9 of those 65.

**Recommendation (D candidate in §6):** no stage 1 `stitchwort prove --at` with a solver now.
Spend the effort Stitchwort-side instead: feed `search` hits, instantiated by unification, into
`arithmetic [...]` inside `search --at`, which needs no translation, keeps the same "facts as
hints" rule and reaches the nonlinear-lemma goals this experiment missed. Revisit an SMT hammer
only if a measured bar (§6) is met on goals that the Stitchwort-side closers fail on.

## 2. Method

**Corpus.** A script scanned AoC 2020 (`aoc/src/Aoc/Year2020`) and the toy formatter
(`tools/toyfmt/src`, deleted 22 Nov 2026 (D3715) and in git history before then) for closing steps: `arithmetic` (68 sampled), `rewrite` (52), an arm whose
body is a lemma application (20), `Void.impossible` (16) and `calc` (4), about 85 per project
with a fixed seed. At each it asked `stitchwort goal --at FILE:LINE:COL --json` for the goal
(hypotheses with types, target, and the source range of the term being proved). That is the
same goal a `?` there would show, without editing the file. 166 sites gave 160 proof goals
(the rest were program positions). Goal kinds, by the target's shape: arithmetic 91, list 21,
equational 18, impossible (target `Void` or a negation) 7, other 23. The baseline for each goal
is the original source in that range.

Std was left out: `goal --at` on a library file answers "nothing was checked there" (§8).

**Translation** (`smt.py`): a small parser of the goal display, then SMT-LIB with Nat and Int
as `Int` (Nat atoms `≥ 0`, Nat `-` truncated), `Bool` and propositions as `Bool`, `List` and
`Option` as datatypes per element sort with `length`, `++` and `∈` defined recursively
(`define-fun-rec`), every other type an uninterpreted sort, every other function uninterpreted
(sorts inferred from use, retried with hints on a clash), and whatever the parser can't read
(lambdas, `match`, record literals, tuples) an opaque constant keyed by its text. Hypotheses are
named assertions, the target is negated, and each lemma is a universally quantified named axiom,
monomorphised over the list element sorts in the goal.

**Premises.** For up to two function names in the target (or the hypotheses, if the target has
none), qualified by receiver where the sort says (`.length` on a list is `List.length`),
`stitchwort search --json --limit 20 --theorems NAME` in the project; the top 20 distinct hits
became axioms. A median of 4 of the 20 failed to translate (higher-order binders such as
`le: a → a → Bool`, instance binders, unknown sorts).

**Solver.** `cvc5 --tlimit=5000 --dump-instantiations`, unsat core over the named assertions,
and the quantifier instantiations, so a lemma in the core can be written applied
(`breakColumn.eq4 indent at`); premises of the lemma are filled with `(arithmetic)`.

**Reconstruction** (`reconstruct.py`): in the fixed order of the brief, each written in place of
the original step and checked with `stitchwort check NAMESPACE --only THEOREM`:
1. `arithmetic [lemma facts from the core]` (hypotheses in scope are used anyway);
2. `rewrite <core equations> then byComputing`;
3. `cases then arithmetic [facts]`, or `cases` if there are none;
4. the core's one lemma applied, or its one hypothesis.

Several goals of a file are checked at once (non-overlapping ranges), errors attributed by line,
and every file's accepted candidates checked again all together. Files are restored after every
check. The same harness ran a **baseline**: plain `(arithmetic)`, then `cases`, on every goal,
solver or not. Seven goals sit in declarations that `check --only` can't name; they are left out
of the baseline's denominator, and the one hammer success among them (a spurious one, §4) is
not counted.

## 3. Results

### 3.1 By goal kind

| kind | goals | unsat | sat | unknown | translation gap | encoder error | hammer reconstructed | plain `arithmetic`/`cases` |
|---|---|---|---|---|---|---|---|---|
| arithmetic | 91 | 23 | 7 | 41 | 13 | 7 | 18 | 43 of 87 |
| equational | 18 | 6 | 4 | 2 | 2 | 4 | 5 | 5 of 17 |
| impossible | 7 | 3 | 0 | 4 | 0 | 0 | 3 | 5 of 7 |
| list | 21 | 7 | 0 | 5 | 5 | 4 | 2 | 6 of 21 |
| other | 23 | 6 | 4 | 7 | 5 | 1 | 1 | 5 of 21 |
| **all** | **160** | **45** | **15** | **59** | **25** | **16** | **29** | **64 of 153** |

No goal timed out. "Unknown" is cvc5 giving up with quantified axioms in play; rerunning those
with enumerative instantiation (`--enum-inst`, 5 s) proved none, so they are facts missing from
the translation, not search effort. "Sat" means the abstraction has a countermodel: the goal
needs a definition the solver can't see (`route.waypointDistance = Spec.manhattan …`,
`(rows.map …).last.getOrElse …`). "Encoder error" is a sort bug in my translator (an argument of
the wrong sort reaching cvc5); a product would fix those, and they don't change the picture.

### 3.2 Cores and time

- **Core size** (hypotheses and lemmas, not the negated goal): 0 for 12 goals (the goal holds
  in the abstraction alone, `True = True` and the like), 1 for 16, 2 for 5, 3 for 6, 4-12 for 6;
  median 1.
- **Cores with a `search` lemma: 7 of 45.** Five are definition equations
  (`Toy.Fmt.Proofs.breakColumn.eq3`/`eq4` three times, all twelve `Toy.Syntax.Operator.level`
  equations once); two are `Aoc.Year2020.Day11.Proofs.compassDirections` turning up in a Day 18
  goal about `size`, a spurious member of the core caused by my translation identifying
  functions by short name. None was a lemma the original proof used.
- **Time per goal:** `goal --at` median 2.8 s (cached project), `search` median 5.2 s per name
  on AoC and 1.8 s on the toy (two names a goal), cvc5 median 0.02 s, a check 0.5-2 s.
  A stage 1 command would spend its time in premise selection and checking, not in the solver.

### 3.3 Reconstruction

Of the 45 goals cvc5 proved, 29 closed: 27 by `arithmetic` (6 of them listing lemma facts from
the core: five definition equations, and one irrelevant lemma that `arithmetic` ignores), 2 by
`cases`; none by the rewrite chain or the lemma-application template. The 16 that didn't:

| reason | goals | example |
|---|---|---|
| the solver used nonlinear arithmetic that `arithmetic` lacks; the original supplied a lemma instance | 2 | `shorter * bound + bound ≤ longer * bound` from `shorter + 1 ≤ longer`; original `arithmetic [Nat.leMulRight (shorter + 1) longer bound less, same]` |
| the goal reads from a hypothesis through Bool/Prop, a predicate's definition or an applied hypothesis, which the encoding flattens to the same atom | 5 | `closesBlock (Reserved keyword)` from `reserved`; `SlotWritten firstRead slots.head` from `isHead` |
| the original step proves a different goal than the range's text (an argument inside a bigger term), so the replacement doesn't fit | 5 | `True = True` at `List.getOrPast … (arithmetic)` |
| a `length`-of-`map` fact the encoding gave for free but `arithmetic` needs as a lemma (`List.lengthMap`) | 1 | `pass.column.length = 3` |
| other: a record equation, a `Text` test, and a core with a spurious lemma (in a declaration `check --only` can't name) | 3 | |

A second pass with templates outside the fixed order (`byComputing`, the hypothesis itself,
`Void.impossible (Bool.falseNotTrue h)` and its `Eq.flipped` form, one hypothesis applied to
another) closed none of the 16.

### 3.4 Side by side

The hammer's proofs read like the file's own; the interesting ones are where they differ from
the original. Three of the 29:

**Day 20, `rowCellsDistinct`** (hypothesis `same: [row, i] = [row, j]`, goal `i = j`):

```
original:  arithmetic [Eq.cong (xs => (xs.drop 1).headOr 0) same]
hammer:    cases
```

The core was `same` alone; `cases` takes the list equation apart. Shorter and clearer, but plain
`cases` finds it without the solver.

**Toy, `minusEnters`** (two Bool hypotheses that contradict, goal `standsBefore "-" "-"`):

```
original:  Void.impossible (Bool.falseNotTrue (Eq.trans plain.flipped minus))
hammer:    cases
```

**Toy, `innerLine`** (goal `column ≤ breakColumn indent (Held at)`):

```
original:  arithmetic
hammer:    arithmetic [Toy.Fmt.Proofs.breakColumn.eq4 indent at]
```

The solver needed `breakColumn`'s fourth equation because it can't compute; Stitchwort's
`arithmetic` computes `breakColumn indent (Held at)` itself, so the original is shorter and the
fact is noise. This is the typical "premise selection" success of the experiment, and it is
why the hammer adds nothing over the baseline here.

A fourth shows the hammer's one real by-product, unused facts: Toy `chainTree`'s
`arithmetic [leftLevel, range.left]` reconstructs as plain `(arithmetic)` (the hypotheses are in
scope anyway).

### 3.5 Did premise selection matter?

65 of the 160 originals name something beyond the goal's hypotheses (a lemma, a definition's
equation, a hypothesis's field such as `range.left`). Of those, cvc5 proved 9, the hammer
closed 3, plain `arithmetic`/`cases` closed 11. The ones that needed a library fact needed one
the translation can't use or `search` didn't rank: `Nat.leMulRight` for a product (the target
has no function names, so no query was made at all), `scaleStep` (a project lemma about fuel),
`List.lengthMap`, inductive predicates (`Parse.Each`, `List.All2`) and `Option.someInjective`.

## 4. Why it fails here, ranked

1. **Computation is invisible to the solver.** Stitchwort's closers normalise first:
   `(Some back).getOrElse 0` is `back`, `breakColumn indent (Held at)` unfolds,
   `[bit, ..rest].length` is `Succ rest.length`. An uninterpreted-function translation sees
   none of it; 38 goals that plain `arithmetic`/`cases` close were not proved by cvc5 (sat,
   unknown, or not translated).
   Translating definitions as equations (CoqHammer unfolds them too) would recover some, but
   that is a translation of most of the language, and the kernel already does it.
2. **Higher-order and inductive content.** 40 hypotheses had function types, 8 more
   higher-order binders, and lemmas over `le: a → a → Bool` failed to translate; lambdas,
   `match`, records and tuples became opaque (median 3 opaque atoms a goal). Inductive
   predicates (`Parse.Each`, `List.Sorted`, `Agrees`) stay uninterpreted, so their lemmas can be
   stated but their constructors can't be used.
3. **Premise selection by name finds the wrong things for arithmetic goals.** A target like
   `shorter * bound + bound ≤ longer * bound` mentions no function, so no search ran; with names,
   20 hits by name are mostly unrelated (`List.length` returns 20 lemmas, few relevant).
4. **Reconstruction is the easy part.** Two thirds of the solver's proofs became Stitchwort
   proofs with the first template. The misses were Bool/Prop readings and nonlinear steps,
   which are closer gaps, not hint gaps.

The corpus favours the baseline in one way: its goals are closing steps of finished proofs,
so many were written as `arithmetic` by an author who knew it would work. It also favours the
hammer in another: no goal needed a fact the author hadn't already got into scope or named,
whereas an agent's open `?` often does. Neither changes the headline: on the goals the solver
could see, Stitchwort's own closers saw at least as much.

## 5. What a stage 1 `stitchwort prove --at` would need

If this is revisited, a product would need, in rough order of size:

- **Definitions as equations**: the equation lemmas Stitchwort already generates
  (`breakColumn.eq4`, `Operator.level.eq3.or2`) for every function in the goal, not just those
  `search` happens to return, plus constructor injectivity and distinctness for every datatype
  in the goal. Without these the solver can't follow the computation the closers do for free.
- **A typed translation from elaborated terms**, not from the goal's display: the display loses
  sorts (the most common hypothesis failure, 78 times, was a function's result sort guessed
  wrong), and names must be full names
  (the spurious `compassDirections` came from short-name identification).
- **Higher-order encoding**: defunctionalisation of lambdas (crush, proof-automation.md C20) or
  monomorphised applications; otherwise most `map`/`filter`/`all` goals stay out of reach.
- **Premise selection by shape**, not by name: the operators of an arithmetic target
  (`*`, `-`, `/`), the head symbols of the hypotheses, and the declaration's own namespace.
- **Reconstruction templates** beyond the four: reading a hypothesis through Bool/Prop
  (`closes` for `closesBlock …`), nonlinear facts as lemma instances, and a `cases then …`
  that carries lemma instances.
- **Ranges from the elaborator**, not `goal --at`'s source range, so the proof replaces exactly
  the term whose goal was asked.
- **cvc5 as an optional tool** found on `PATH` (or `nix shell`), never needed by `check`.

That is a translation layer of several thousand lines plus a term-level API: proof-automation.md
§5.4's "not worth their translation and reconstruction layers" still holds for this corpus.

## 6. D candidate for Matt

**D-hammer: stop the SMT hammer at stage 0, and put premise selection into `search --at`
instead?**

*The problem:* agents spend attempts finding which facts close a goal; Stitchwort's closers use
only the facts in scope or listed.

*What the experiment showed (measured, 160 goals):* cvc5 proves 28% of goals in 0.02 s, and
Stitchwort's own closers turn 64% of those into checked proofs, but **none** of those proofs
were beyond plain `arithmetic` or `cases`, which close 42% of the goals with no hint; 38 goals
went the other way. The solver can't see computation, and the facts that really mattered
(nonlinear lemmas, recursion and inductive facts) are the ones a first-order translation of
`search` hits misses.

*The change (recommended):* no `stitchwort prove --at` with a solver now. Instead, a small
Stitchwort-side step: in `search --at`, after the simplest closers fail, try
`arithmetic [lemma args]` with the top-k `search` hits for the target's *operators and heads*,
their arguments found by unification against the goal and hypotheses, kernel-checked as
`search --at` already does. Same rule as D-c (hints, Stitchwort source, nothing trusted), no
external tool, and it reaches the `Nat.leMulRight`-style goals this experiment missed.

*Bar for reopening an SMT hammer:* on a set of at least 100 open `?` goals taken from lane
transcripts, on which `search --at --simplest-first` and the change above both fail, a stage 1
prototype closes at least 15% with kernel-checked Stitchwort proofs in a median under 5 s per
goal. Under that, the translation layer costs more than it returns.

**[rec: yes: stop at stage 0; file the `search --at` premise step as a ticket]**

## 7. Reproducing

Scratch scripts (not committed; under the lane's scratchpad,
`…/scratchpad/sw3586/`): `collect.py` (sites and `goal --at`), `smt.py` (parser and SMT-LIB
encoding), `hammer.py` (search, cvc5, core and instantiations), `reconstruct.py` (candidates,
baseline, extra templates, checks), `analyze.py` (the tables above). Raw data:
`corpus.jsonl`, `results-{aoc,toy}.jsonl`, `recon-*.jsonl`, `baseline-*.jsonl`,
`extra-*.jsonl`, and the SMT-LIB files in `smt/`. The whole pipeline took about 25 minutes of
machine time, most of it `goal --at` on the toy (up to 40 s for one goal) and `search`.

## 8. Findings outside the experiment

- **`goal --at` can't answer in std files.** `goal --at List/Lemmas.sw:143:38 --std-dir .`
  says "no goal … nothing was checked there", so std's proofs can't be queried or used as a
  corpus.
- **`check NAMESPACE --only NAME`** with a name that isn't a top-level theorem (a definition
  such as `Day08.Code.runFrom`, or `levelInner`) is `E-UNKNOWN-THEOREM`; in a batch it looked
  as if the other named theorems weren't checked either (a candidate passed that the retry
  without the bad name rejected). Worth confirming, and either checking the rest or saying so.
- **The main checkout's release binary** changed twice during this lane (merges at about
  14:00 and 14:18), and with it the surface syntax (SW-3564); a lane that runs it while a merge
  changes the language gets parse failures in std (`the library file core doesn't parse`).
  Lanes that use it for long runs should copy it first.
- **Unused facts in `arithmetic [..]`**: some originals list facts that plain `arithmetic`
  doesn't need (Toy `chainTree`'s `[leftLevel, range.left]`; `arithmetic [same]` in Day 18). Since the emitted proof already knows which
  facts it used, a warning (or a `fmt`-time fix) for listed facts it didn't use is cheap.
- **`goal --at`'s range** for an application with a bracketed last argument once stopped
  before the closing bracket (`Void.exfalso (Bool.falseNotTrue never` without its `)`), with
  the binary before SW-3564; not rechecked after.
