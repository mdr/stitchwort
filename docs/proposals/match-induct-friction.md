# Proposal: the three frictions of the `match induct` pilot

**Status:** draft 1, 20 November 2026. Ticket SW-4304 (Opus, paper), from
the pilot SW-4264 (the comma-dropping walkers' proofs in
`tools/fmt/src/Syntax/Settle*Proofs.sw` and `GlueQuietProofs.sw` by
`match induct`, merged as `0b0bbc339`). A design note only: nothing in the
compiler changes. Two questions for Matt, in [§5](#5-questions-for-matt).
Written against `main` at `b9b71c81c`.

Related: [functional-induction.md](functional-induction.md) (G1 as built,
D3697), [pattern-guards.md](pattern-guards.md) (the forms a guard's
hypotheses take, stage 2, SW-1301/SW-1318),
[function-equations.md](function-equations.md) (`f.eqK`, D2186),
[bool-as-proposition.md](bool-as-proposition.md) (`.read`, D3482-D3488),
[folded-calls.md](folded-calls.md) (D480), reviews
[SW-4278](../reviews/SW-4278-d3697-review.md) and
[SW-4261](../reviews/SW-4261-induct-g1-review.md).

Claims are marked **[run]** (a file in
[match-induct-friction/](match-induct-friction/) checked with the main
checkout's `target/release/stitchwort`, built 20 Nov 03:36), **[read]** (the
file named), **[measured]** (counted with `grep` over `aoc games tools
examples crates/elab/src/std`), **[recalled]** and **[estimated]**. Lean
claims are read from Lean 4.35.0's own sources
(`/nix/store/…-lean4-4.35.0/src/lean`, the version `nixpkgs#lean4` gives).

## In plain words

**The problem.** The pilot shortened the walkers' proofs by 170 lines, but
three things got in the way. (1) A guard such as `if comma.kind == Comma &&
closer.kind.isCloser && hasItem behind` reaches the proof turned into a
proposition, `isComma comma ∧ isCloser closer ∧ hasItem behind`, and its
failure as `¬(…)`, while the formatter's lemmas all speak the `Bool` form
(`lastPair … = True`, `fwdPair … = False`). So every family needs
hand-written converters, four in this one (44 lines). (2) Only the inducted
function's call is unfolded; a sibling walker in the same goal is unfolded
by hand. (3) An induction hypothesis shows `(isComma leaf).not` where the
theorem said `hasItem [leaf, ..behind]`.

**The change.** (1) State a `Bool` guard as written: `guard: c = True`, and
where it fails, `c = False`; a guard written as a proposition stays one.
This is what an `if` with the same condition already gives, and what Lean
gives for a `Bool` test. The `∧` view is one `.read` away. (2) No new
language: teach `rewrite g.eqK then …` (it already finds the arguments and
the hypotheses), and fix `rewrite repeatedly [g]`, which leaves out guarded
arms and panics when it leaves out every arm. (3) Read the goal back with
calls kept folded when the motive is built, as everywhere else since D480.

**What it should do.** (1) The pilot's four converters collapse to one
two-line `match` (or nothing, for a guard written with the family's own
predicate) [estimated: about 40 of the 44 lines, and the 9 call sites become
direct]; one condition gets one form wherever it is written, instead of the
four forms it gets today ([§1.1](#11-the-problem)). (2) A sibling's step
stays one short line, `rewrite withBareR.eq2 then ih` [run]. (3) The ih
says the theorem's own premise, by name.

## 1. Guards as `∧`/`¬` propositions, lemmas as `Bool`

### 1.1 The problem

`withoutR` (tools/fmt/src/Syntax/SettleBareProofs.sw:1148) is

```
def withoutR (behind rest: List Leaf): List Leaf := match rest with
  | [] => behind
  | [comma, closer, ..after] if comma.kind == Comma && closer.kind.isCloser && hasItem behind => …
  | [leaf, ..after] => withoutR [leaf, ..behind] after
```

and its cases are [run: `guard-forms.sw`, a model with the same arms]

```
eq2 … guard: isComma comma ∧ isCloser closer ∧ hasItem behind
eq3 … notArm2: ∀ (closer: Kind) (after1: List Kind) => after = [closer, ..after1]
        → ¬(isComma leaf ∧ isCloser closer ∧ hasItem behind)
```

(each conjunct a `Bool` read as `b = True`, shown bare). The formatter's
proofs about this family are stated with `lastPair closer.kind comma behind
= True` and the lookahead `fwdPair behind leaf after = False`
(SettleBareProofs.sw:109, :448), because that is what the walkers compute
and what `rewrite`, `byComputing` and the `…Nop`/`…Pair` lemmas use. So the
pilot added four converters (SettleBareProofs.sw:1192-1239, 44 lines,
9 uses) [read]:

- `fwdPairOfNotArm`: `notArm2` → `fwdPair … = False`, by a `match after`
  and a `match` on the test, rebuilding the `∧` from `Bool.andLeft`/`andRight`;
- `guardOfPair`: `lastPair … = True` → the `∧`, to pass a guard to
  `withoutR.eq2` at another argument (`dropRev behind`);
- `notArmOfFwdPair`: `fwdPair … = False` → a sibling's `notArm2`;
- `fwdPairOfNoPair`: the same as the first for `dropF`/`barishF`, whose guard
  is the single `Bool` `lastPair …`, and *still* needed, because `notArm2`
  ends `¬lastPair …` (that is, `lastPair … = True → Void`), not
  `lastPair … = False`.

The deeper issue is that one condition gets four forms depending on where
it is written [run: `guard-forms.sw`; read: pattern-guards.md "Stage 2",
equations.rs `Hyp`]:

| written as | holds | fails, same patterns (`NotGuard`) | fails, partial overlap (`notArmJ`) |
|---|---|---|---|
| `if a && b && c` inside the arm | `(a && b && c) = True` | `(a && b && c) = False` | (no overlap) |
| guard `a && b && c` | `a ∧ b ∧ c` | `¬(a ∧ b ∧ c)` | `… → ¬(a ∧ b ∧ c)` |
| guard `p` (one `Bool`) | `p` (`p = True`) | `p = False` | `… → ¬p` |
| guard `xs == []` (a decided `==`) | `xs = []` | `xs ≠ []` | `… → ¬(xs = [])` |

The conversion to a proposition was SW-1301's choice for guards (as built,
not a recorded D); the `if` form is D2186's. Since then Matt decided that a
`Bool` fact crosses to its proposition by an explicit word, `.read`, not
silently (bool-as-proposition.md, draft 2, D3486-D3488) [read], and the core
gives `&&` its reading: `(a && b) = True` reads as `a ∧ b`, `= False` as
`a = False ∨ b = False` (syntax.md, "Which reading") [read]. The guard
conversion predates that and is the one silent crossing left in generated
statements.

### 1.2 What Lean does

Lean has no pattern guards, so the closest shape is an `if` in the arm.
`Lean/Meta/Tactic/FunInd.lean` (`buildInductionBody`, lines 618-659)
[read]:

- `ite c` / `dite c` (a decidable proposition, which is also what a `Bool`
  `if b` elaborates to, as `b = true`): the cases take `h : c` and
  `h : ¬c`. So `if ok a b` gives `ok a b = true` and `¬ok a b = true`
  (functional-induction.md §2 [run there: `log2.induct`]).
- `cond c` (`bif`, the `Bool` conditional): `h : c = true` and
  `h : c = false`.
- `&&` is never split: the condition is whatever term the `if` tests.
- Overlapping patterns: the matcher's splitter adds `∀ b after_1, after =
  b :: after_1 → False` (FunInd.lean:99-101, "the matcher is replaced by its
  splitter, which brings extra assumptions into scope when patterns are
  overlapping") [read]; with no guards there is no guard part.

So Lean states a condition in the form the source tests it, and its `Bool`
`bif` gets `= true`/`= false`, exactly Stitchwort's `if` rule.

### 1.3 Options

**A. The source's own form (recommended).** A guard whose condition is a
`Bool` expression `c` is stated `guard: c = True`; where it fails,
`c[σ] = False`, both in `NotGuard` and as the last part of `notArmJ`
(`∀ vars => x = p → … → c[σ] = False`). A guard written as a proposition
(`if n ≠ 3`, `if h: P`) keeps today's forms (`P`, `¬P`). The same change in
`f.eqK` and `f.induct`, which must stay identical (proofs pass `notArm2`
from a case straight to `f.eqK`, SettleBareProofs.sw:1159). The table above
becomes one row per kind of condition, the same as `if`.

For the pilot: `guard` is then `(comma.kind == Comma && closer.kind.isCloser
&& hasItem behind) = True`, which is `lastPair closer.token.kind comma behind
= True` by computation (`Leaf.kind` is `leaf.token.kind`), so `guardOfPair`
goes; `notArm2` ends `… = False`, so `fwdPairOfNotArm` and `fwdPairOfNoPair`
become `match after with | [] => byComputing | [c, ..a] => notArm2 c a
byComputing`, and `notArmOfFwdPair` becomes `c a same => rewrite same at nop
then nop` [estimated, not run: the form doesn't exist yet]. Writing the
walkers' guard as `if lastPair closer.kind comma behind` (a formatter
change, not a language one) makes the guard literally the lemmas' form. A
proof that wants the conjunction writes `guard.read`.

What it costs: a single decided `==`/`!=` written as a `Bool` (`xs == []`,
`n != 3`) now gives `(xs == []) = True`, not `xs = []`, so `omega` or a
`rewrite` wants `.read` first, or the guard written as the proposition
(`if n ≠ 3`). That is the rule `if` already has. [As built (SW-4341): `!=`
is the proposition operator, `n ≠ 3` spelled in ASCII, so a guard `n != 3`
keeps `n ≠ 3`; only `==` and other `Bool`s change. See pattern-guards.md,
"Changed by D3699".]

- *Effort* [estimated from similar past lanes]: an Opus lane in
  `crates/elab/src/equations.rs` (`probe_row`: stop deriving `prop` and
  `negated` for a non-`dec` guard; `Hyp::NotGuard`/`Overlap` state `c = False`)
  and `equations/induct.rs` (`refute_guard` loses the `toBool`/`andBool`
  bridging for `Bool` guards: mostly deletion), plus
  `examples/accept/pattern-guard-equations.sw` and the
  `match-induct-guarded-overlap*.sw` pair, syntax.md, guide ch. 10 and
  pattern-guards.md: about 45-60 min. A Sonnet sweep of proofs that use the
  current forms: 43 `notArmN` lines in 10 files, 12 `guard`/`notGuard`
  binders in 5 files [measured], plus `f.eqK` call sites passing guards
  (not counted). Then a Sonnet formatter lane removing the converters.
  Migration cost doesn't count (D2303); listed for scheduling.
- *Risk*: it generates kernel terms, so it gets an Opus review (D2364). It
  accepts everything it accepts today: only hypothesis types change, and
  no theorem gets a new condition (D3688 doesn't arise). The risk is proofs
  in std or AoC that lean on `n ≠ 3` coming from `n != 3`; the sweep finds
  them by failing.

**B. Keep the propositions; add bridges to std.** Std gets generic lemmas
(`Bool.and3OfTrue`, `Bool.falseOfNotTrue: ¬(b = True) → b = False`, …). This
removes `guardOfPair` and the inner `match` of `fwdPairOfNoPair`, but not
the shape mismatch: every family whose lemmas are stated in `Bool` still
writes its own `fwdPair…OfNotArm`, because the `∀ closer after1, after =
[closer, ..after1] → …` premise is the definition's own pattern. And the
four forms of §1.1 stay. Effort: a DeepSeek task, 15 min. Risk: none. It is
the status quo with shorter converters.

**C. A only for conjunctions and negations.** Keep a lone decided `==`/`!=`
as its proposition (`xs = []`), but stop splitting `&&` and state failures
as `= False`. Fewer proofs change, but the rule is "a guard says what you
wrote, unless it is one equality test", and it is still not the `if` rule.

**Recommendation: A**, in both `f.eqK` and `f.induct`, with the formatter's
walkers then rewritten to guard with their own predicate. It removes a
silent crossing that D3486-D3488 decided against elsewhere, gives one
condition one form, and matches Lean. This changes what users see in every
guarded definition's equations and cases: **D question 1**, §5.

## 2. Only the principle's call unfolds

### 2.1 The problem

`withBareFromR` (SettleBareProofs.sw:1155) proves two walkers agree:
`withBareLastCommas behind rest = (withBareR behind rest).reverse`.
`match induct (withBareLastCommas behind rest)` unfolds the left side; the
right side's `withBareR behind [comma, closer, ..after]` is stuck on the
guard, so each case begins `rewrite withBareR.eq2 behind comma closer after
guard then ih`. In `buildDrop` (:1262) the other side is a different walker
at a different argument, `withoutR (dropRev behind) rest`, and its step
needs the guard re-proved at `dropRev behind` (`guardOfPair … pairA`, from
`hasItemDropRev`).

### 2.2 What Lean does

`fun_induction f` uses `f.induct_unfolding`, whose motive takes the result
and which "will try to automatically unfold the call to `f` in the goal"
(Init/Tactics.lean:1117-1119; FunInd.lean "Unfolding principles", lines
177-200) [read]. Only `f`'s call: Stitchwort's `match induct` already does
the same (its motive takes the result). Other functions are left to the
user, typically `fun_induction f <;> simp [g, *]` [recalled], where `simp`
discharges `g`'s conditions from the hypotheses in context.

### 2.3 Options

**A. Teach what already works (recommended).** `rewrite withBareR.eq2 then
ih` closes the sibling case with no arguments: `rewrite` finds the
equation's variables by matching, and its `guard` and `notArm2` premises
from the context, which hold the same hypotheses whenever the two walkers
share their guard [run: `sibling-rewrite.sw`, both cases]. The pilot wrote
the arguments out. A paragraph and an example in the proving guide's
`match induct` entry (docs/proving-guide.md:542) and guide ch. 10. Effort:
a DeepSeek docs task, 10 min. With §1's option A, the `buildDrop` shape
also gets shorter, since the guard there is `lastPair … = True` and
`hasItemDropRev` rewrites it directly.

**B. Fix `rewrite repeatedly [g]` for guarded definitions.** A definition
named as a rule stands for its arm equations "leaving out arms whose
patterns are constructors (a call on those computes already)" (syntax.md,
`rewrite repeatedly`, D3639) [read]. A guarded arm is left out too, though
its call doesn't compute (the guard is stuck), so `rewrite repeatedly
[withBareR]` can never take its step. Worse, when every arm is left out,
it panics: `index out of bounds` at `crates/elab/src/rewrite/repeatedly.rs:833`
[run: `repeatedly-panic.sw`, a two-arm `len`; the guarded `walkR` panics
the same way]. Fix: keep arms whose call is stuck on a guard, with their premises
found as `rewrite` finds them; and an empty rule list is an error, not a
panic. Effort: a Sonnet lane, 30 min. This widens what a definition name
does in a rule list in the direction D3639's own reason gives, so I'd call
it a bug fix (orchestrator's call), not a language decision.

**C. `match induct` unfolds every call in the goal it can.** After applying
`f.induct`, each case also rewrites with `g.eqK` for any other `g` whose
call the case's patterns select, discharging premises by assumption. Lean
doesn't do this. It would change goals silently (a proof that wanted the
folded call gets the unfolded one), cost a search per case, and only helps
when the hypotheses match exactly, which is when option A is already one
line. Effort: an Opus lane, 1-2 h. Not recommended.

**Recommendation: A now, and B as a bug ticket** (the panic is a crash on
valid input). No question for Matt: neither changes a statement.

## 3. Induction hypotheses show unfolded calls

### 3.1 The problem

With a premise `item: hasItem behind = True` generalised by `match induct
(withoutP behind rest)`, the `eq3` case shows [run: `ih-display.sw`]

```
ih: (isComma leaf).not → kindOk Comma after → withoutP [leaf, ..behind] after = …
```

where the theorem's own words are `hasItem [leaf, ..behind]`. A call whose
`match` can take a step is shown taken; a stuck one (`kindOk Comma after`)
stays a call. In the formatter the same happens to `hasItem`, `gapOk` and
the lookahead predicates on `[leaf, ..behind]`, which unfold to the bodies
of `match`es. With a different premise the original hypothesis itself
shows as `ok: True = True` after refinement [run]. The pilot reported this
as "ih premises display as unfolded matches, not named predicates".

Cause [read]: `crates/elab/src/induct_match.rs:377-379` reads the goal and
the generalised hypotheses' types back with `quote` (the unfolded readback)
to build the motive, so calls in it are already their bodies; evaluating
the motive at `[leaf, ..behind]` then runs them. `quote_folded`
(folded-calls.md stage 3, `crates/core/src/value.rs:3119`) keeps a glued
call as the call.

Correction (SW-4327, tested): switching that read-back to `quote_folded`
changes nothing. The premise shows unfolded because goals print hypotheses
with `value::quote_shown` (`crates/elab/src/goals.rs`), which writes a call
that steps at once as its one step (`Readback::Shown`, deliberately: it
shows `if True then a else b` as `a`). So option A below means changing the
goal display for induction hypotheses, not the motive.

### 3.2 What Lean does

Lean's `induction … using f.induct` abstracts the targets out of the goal
and instantiates the motive by beta-reduction only, so the hypotheses say
`hasItem (leaf :: behind) = true` [recalled: `Lean/Elab/Tactic/Induction.lean`
`mkElimApp` builds the motive from the goal; no delta step]. FunInd also
folds recursive calls back to `f arg` on purpose ("recovering the recursive
calls", FunInd.lean:115-122) [read], for the same readability reason.

### 3.3 Options

**A. Fold the motive (recommended).** `quote_folded` at
induct_match.rs:377-379. The two terms are convertible, so the kernel and
every proof that type-checks by conversion are unaffected; what changes is
the goal display, and what syntactic tactics (`rewrite … at ih`) see: they
see the named call, which is what the theorem's author wrote. A proof
written against the unfolded display could stop matching (none known; the
verifier's hash snapshots will show changed terms). Effort: a Sonnet lane,
20 min including an example with the `hasItem` premise. Risk: low.

**B. Fold only the display.** Keep the motive term, fold when printing
goals. Cheaper to argue about hashes, but `rewrite … at ih` then sees a
term different from what the user is shown, which is worse.

**C. Leave it.** The user writes `let ih2: hasItem [leaf, ..behind] = True
→ … := ih` to restate it. Costs a line per case.

**Recommendation: A.** It applies D480's rule (calls stay folded while
checking) to a place that missed it, so I'd treat it as a fix; it does
change how hypotheses look, so it is offered as **D question 2** in case
Matt wants to see it, with a recommendation that the orchestrator may take
it as a fix.

## 4. Plan, if accepted

| Lane | Model | What | Est. |
|---|---|---|---|
| 1 | Opus | §1 A in `f.eqK`/`f.induct`, examples, docs | 45-60 min |
| 2 | Sonnet | sweep std/AoC/fmt proofs onto the new forms | 30 min |
| 3 | Sonnet | formatter walkers guard by `lastPair`; converters removed | 20 min |
| 4 | DeepSeek | §2 A, the proving guide and guide ch. 10 | 10 min |
| 5 | Sonnet | §2 B, `rewrite repeatedly` keeps guarded arms; empty set is an error | 30 min |
| 6 | Sonnet | §3 A, folded motive, an example | 20 min |

Lane 2 follows lane 1 (same proofs); 4, 5 and 6 are independent. Lane 1
gets an Opus review (kernel terms, D2364).

## 5. Questions for Matt

The orchestrator numbers these.

**D question 1: a guard's hypotheses in the form the guard is written?**
[rec: yes, option A]

- *The problem.* A guard like `if comma.kind == Comma && closer.kind.isCloser
  && hasItem behind` is handed to proofs as a proposition,
  `isComma comma ∧ isCloser closer ∧ hasItem behind`, and its failure as
  `¬(…)`, while the same condition written as an `if` inside the arm gives
  `(…) = True` / `(…) = False`. Lemmas about such code are stated in the
  `Bool` form, so each family needs converter lemmas: four in the pilot,
  44 lines.
- *The change.* A `Bool` guard `c` gives `guard: c = True`, and where an
  earlier guard fails, `c = False`, in both the equations (`f.eqK`) and the
  induction cases (`match induct`); a guard written as a proposition stays
  a proposition. The `∧` view is `guard.read`, as for any `Bool` fact.
  Same as `if` today, and as Lean's `Bool` conditional.
- *What it should do.* The pilot's converters go to one two-line `match`
  [estimated: about 40 of 44 lines]; one condition has one form wherever it
  is written. Cost: a guard `n != 3` gives `(n != 3) = True`, not `n ≠ 3`;
  write `if n ≠ 3` or use `.read` for that. [As built (SW-4341): `!=` is
  the proposition `≠`, so `n != 3` keeps `n ≠ 3`; `xs == []` is the case
  that changes.] About 55 hypothesis uses in 15
  files move [measured].

**D question 2 (optional; rec: the orchestrator's call as a fix): induction
hypotheses keep the theorem's named calls?** [rec: yes, option A]

- *The problem.* In a `match induct` case, a premise `hasItem behind` shows
  in the induction hypothesis as its unfolding, `(isComma leaf).not`, not
  `hasItem [leaf, ..behind]`.
- *The change.* Build the motive with calls kept folded, as the checker does
  everywhere else since D480.
- *What it should do.* Hypotheses read as the theorem says them, and
  `rewrite … at ih` matches those words. No proof's validity changes (the
  two forms are equal by computation).

## 6. Findings to file

- **Bug**: `rewrite repeatedly [g]` panics (repeatedly.rs:833, index out
  of bounds) when every arm of `g` is left out as constructor-only;
  `repeatedly-panic.sw` reproduces it with a two-arm `len` (any
  definition whose arms are all constructor patterns; `twice n = n + n`
  is fine). Bundled in §2 B.
- **Gap**: `rewrite repeatedly [g]` leaves out guarded arms, whose calls
  don't compute (§2 B).
