# SW-2761 review: Decidable record, stage 3

Opus paper review (D2364: the change generates kernel terms), 11 Nov 2026.
Read-only: no builds or tests were run. Diff read: `main...lane/SW-2761`
(f1216be8c, e508c9831), `crates`, `docs`, `examples`; snapshots sampled.
Line numbers are on `lane/SW-2761`.

**Verdict: merge with follow-ups.** One fixup before merging, small enough
for the orchestrator to make: a doc comment that has been split (1 below).
Nothing found makes the elaborator emit a term the kernel rejects in code
that checked before, with one possible exception, a rewrite that used to
work (3 below). That one is a should-fix, not a blocker: std, aoc and rogue
pass, and the kernel re-checks.

## Must fix (fixup)

1. **`crates/elab/src/equations.rs:4989-5000`**: `plain_ifs`'s doc comment
   was put between `spine_icit`'s doc and `spine_icit`. Rustdoc now gives
   `plain_ifs` the doc "`t` as a head applied to arguments, with how each
   is passed, looking through locations. `t` with each plain `if` …", and
   `spine_icit` (`:5139`) has none. Move lines 4989-4990 down to just above
   `fn spine_icit`.

## 1. Correctness

- **equations.rs relies on `elim` and `ifThenElse` being convertible
  (`plain_ifs`, `:5001-5137`).** This is sound in principle. The equations
  are stated over the rewritten body, `Bool.ifThenElse c (_ => y) (_ => n)`,
  and proved against the real one, `Decidable.elim d (_ => y) (_ => n)`.
  Kernel conversion has to unfold both helpers to a case on the same test.
  That holds only when `c` is what `d.holds` computes to. `test` gets it
  right for each form it knows:
  - the six comparisons, through `comparison_in`, the same table `bind.rs`
    uses;
  - `Bool.decTrue c` gives `c`;
  - `andThen`, rebuilt as `ifThenElse a (_ => b) (_ => False)`, which is
    `Decidable.andThen`'s `holds` (`core/Decidable.sw:183`);
  - otherwise `Decidable.holds d`.

  A wrong `c` would make the kernel reject the equation, not state a false
  one. The new behaviour has no direct test. A function-equations example
  should cover each `test` path: a comparison, a `decTrue` in a
  `decreasing` body, `&&` on comparisons, `||`/`not` (the fallback), and an
  `if h:` that keeps `elim`. Users then see the hypotheses as `c = True`.
  Recognising a plain `if` by its binder named `_` (`:5121`) is fine,
  because `!body.mentions(0)` is the real criterion.
- **Statements users see for `||` and `not`.** These fall back to
  `Decidable.holds d`, so `f.eq.ifTrue`'s hypothesis reads
  `(Decidable.or …).holds = True`, not the `Bool` the user wrote. That is
  correct but harder to read than the `&&` case. Follow-up.
- **pretty.rs `decided_if` (`crates/core/src/pretty.rs:2450`).** For
  `Decidable.elim`, `if p then a else b` (or `if h: p …` when a branch uses
  the proof) matches the term. Two inaccuracies:
  - The helper call is printed from `p` alone, and the test argument
    (`args[5]`) is ignored. Where that test is no longer `d`'s (a
    generalised `X` in a motive, which `E-MATCH-MOTIVE` or a hole in an arm
    can show), the display says `if p` while the term is stuck on something
    else. Fix: print the helper call as `if` only when `args[5]` is `d`'s
    test or a projection of `d`; otherwise print it as is.
  - Any `Decidable.elim d …` prints as `if p`, including one on a decision
    the user chose (not the instance `if p` would find). Pasting the
    printed text back can then give a different term. This is rare.
    Mention it in the printer's doc rather than fix it.
- **Mixed notation in messages.** In `rfl-long-computed.snap`, one note now
  shows `≤` for decided `if`s and `<=` for `Bool` ones. It does read
  better than before (`≠ 0` instead of `.equal 0).not`). The mix comes
  from the decided and `Bool` `if`s printing their conditions differently,
  and doesn't need fixing.
- **rewrite.rs has no pass without carrying (should-fix).**
  `replace_occurrences_as` (`crates/elab/src/rewrite.rs:1089-1135`) tries
  two passes: selective carrying first (`carry_everywhere = false`), then
  carrying everywhere. It never tries the plain motive that `main` used.
  The selective pass carries a record when `decides_other`
  (`:1477`, `:1509-1543`) says its proposition doesn't mention the left
  side. `decides_other` reads that from the type the kernel *infers* for
  `sound`, which can be folded (`m ≤ n`) while the goal's `elim {p}` has `p`
  unfolded (`Nat.leq m n = True`) and generalised. In that case carrying is
  ill-typed, the plain motive would have checked, and both passes fail with
  `E-REWRITE-MOTIVE`, so a rewrite that worked on `main` would now fail.
  Nothing in std, aoc or rogue hits this, but the comment "tried second, so
  nothing that checks the usual way changes" (`:1107`) isn't quite true of
  the first pass. Suggested fix: run the plain motive first (as
  `matching.rs` does), then selective carrying, then everywhere. Or have
  `decides_other` test the `p` the goal's `elim` carries, not the inferred
  type.
- **`cases` now checks every motive (`crates/elab/src/matching.rs:1069-1086`).**
  For `skip.is_some()`, `motive_checks_now` (a `lifted_type` kernel
  inference) runs on every split. Before, the kernel checked the motive
  once, at the end. Correctness is fine; the cost is per split in a
  `cases` search. The lane's bench baseline passed. Add a `cases`-heavy
  proof to the next comparison run (follow-up).
- **omega `as_if` (`crates/elab/src/carry.rs:228-261`, used at
  `omega.rs:936`).** Each branch closure is applied to `Value::Refl` as its
  proof. The doc says the bodies "don't look at" it, but nothing checks
  that. For an `if h:` whose branch uses `h` (`Fin.mk i h`), the `Bool`
  form that omega reads then holds `Refl` where a proof of `p` belongs.
  Omega's certificate goes to the kernel, so this can't be unsound. At
  worst it is a spurious omega failure. Suggested fix: apply each closure
  to a fresh neutral and return `None` if that neutral occurs in the
  result.

## 2. carry.rs: general or tuned?

The mechanism is general. It carries `{holds, sound, complete}`,
`d.sound a` and `d.complete a` along an equation by `J`. The `J` terms
(`forward`, `backward`, `along`, `then`, `sym`) are each correct as
written, including the shifts. They depend on no std names except one
fact: `Decidable.elim` has a single helper with seven arguments
(`elim_helper`, `as_if`'s `[_, _, _, yes, no, test, _]` at `:253`,
`matching.rs` `decided_if` at `:2094` with positions 2/5/6, and pretty.rs's
copy at `:3055`). If `elim`'s definition changes, each of these quietly
gives `None`. That fails safe, but it would silently turn off SW-2751's
fix. Add a unit test that pins `elim_helper(g).arity() == 7` and the
argument roles.

Edge cases:

- **Nested decisions.** These compose. The hook visits from the top down,
  and a carried record's parts go back through `apply_under`, so inner
  records whose test is the scrutinee are carried too. With literals,
  `Decidable.not`/`andThen` of a comparison work through the inner literal
  being carried (`holds` generalised, proofs retyped consistently).
  `transported_inside` covers the remaining case, where the inner decision
  is a variable `d` and the scrutinee is `d.holds` (2020 day 4).
- **A test that mentions the scrutinee twice.** `along` replaces every
  occurrence in `t[s]` with `y` at once (`matching.rs` `transported_inside`,
  the `ty` hook), so this is fine. If a test mentions *two different*
  scrutinees, only the first found is carried.
- **Dependent motive / mixed goal.** `matching.rs` carries every occurrence
  once the plain motive fails, with no per-occurrence test like rewrite's
  `decides_other`. A goal with two records on the same test fails both
  ways if one has a proposition the motive generalises (`Bool.decTrue s`,
  `p` = `s = True`) and the other needs carrying. This is unlikely, but it
  is a spurious failure that `main` didn't have, since `main` had
  `unused_proof_if`. Add a per-occurrence check (follow-up).
- **`Met::Sound` with a `d` that mentions its own test.** `carried` builds
  `part(d).sound (forward …)`, where `forward` proves `s = True` about the
  original test. If generalising `d` changes `d`, the types disagree. This
  is rare. The kernel rejects it and the original error is reported.
- The comment at `matching.rs:2149` ("a scrutinee of another type") means
  a scrutinee of another *form* (not `d.holds`). Comparisons are `Bool`
  too. Reword it.

**Tests for each path.**

| Path | Example |
|---|---|
| `decided_if` | `match-decision-refines-if.sw` (`cappedSplit`, `splitBig`) |
| `transported_inside` | `allZeroAndNotFalse` |
| `Met::Record` with `holds` = scrutinee | `match-if-and.sw` |
| `Met::Sound`, `Met::Complete` | none |
| rewrite.rs carrying | none |
| `cases` path with transport | `allZeroAndNotFalse` |

`Met::Sound`/`Met::Complete` and rewrite.rs carrying are reached only
incidentally (std, aoc). Each should get a focused accept example: a
`rewrite` of `x ∈ xs`'s test under an `if`, a `rewrite … at` with `Place::Goal`
(the `sym`/`then` path), and a match on `d.holds` with `d.sound` in the
goal.

## 3. Leftovers

- `crates/elab/src/rewrite.rs:1236`: `let carried_any = search_carried;`
  renames the variable for nothing. Inline it.
- `crates/elab/src/rewrite.rs:1352-1357`: two doc sentences for different
  tuple fields run together ("…in the motive's context. Whether everywhere
  …"). Better as a small struct with named fields.
- `crates/elab/src/decreasing/plain.rs:734`: a doc line well over the width
  (rustfmt doesn't wrap comments). Rewrap it.
- `crates/core/src/pretty.rs:3055` duplicates
  `crates/elab/src/carry.rs:213` (`elim_helper`). Keep one in `core` and
  make it `pub`.
- `crates/elab/src/bind.rs:213-217`: `comparison_in` was split out for
  `equations.rs`, which is fine. It is the only part of the dropped
  generalisation left, and it isn't dead.
- `Builtin::ToBool` is `"Decidable.holds"` (`crates/core/src/registry.rs:360`)
  and is read as `holds` in `cases.rs:1857` and `equations.rs`. Rename it to
  `Holds` (stage 4, or a small ticket).
- `examples/accept/match-if-and.sw:1-5`: the header explains the `if` by
  "not yet known then whether the branches use its proof". That was the
  `%conj` tag's reason, and the tag is gone. Restate it as what the example
  tests.
- No comments narrate the change. The new ones (`check.rs:5263`,
  `cases.rs:1854`, `matching.rs:507`) say why. `matching.rs:1095` names the
  equation `%tested`, which the arms see. The warning logic treats it as
  unnamed (`:1300`). Check that hole and goal messages hide `%` names; I
  assume they do, but didn't check.
- The two snapshots taken at the same point (`matching.rs:1065-1066`) are
  needed because `restore` consumes the snapshot. Fine.
- Snapshot headers changed `source: crates/cli/tests/examples.rs` to
  `running/examples.rs` (insta metadata only). Harmless.

## 4. Docs

- **`docs/syntax.md:1534` (the `if` row) is accurate on the term:** one
  `Decidable.elim`, refined by a match on the test or the decision.
  "Branch equations have the `Bool` hypotheses `c = True`" is wrong for a
  proposition `c`: the hypotheses are about the *test* (`Nat.leq (Succ x)
  y = True` for `x < y`), not `c`. Reword it as "`t = True` and
  `t = False` on the decision's test `t`". The row says "a case on the
  decision's test (`Nat.leq x y` for `x <= y`)"; that is right for `≤`.
- **`docs/syntax.md:2078`** is accurate and better than before. It changes
  the example from `Nat.decLessThan 9` to `Nat.decLessEq 10`, which matches
  2021 day 18.
- **`docs/syntax.md:2076`** (the `Fin`/`Ord.byKey` paragraph) still
  describes "matches on `b`" for a decision computing to `Bool.decTrue b`.
  `tested_bool` is gone, but `(Bool.decTrue b).holds` computes to `b`, so
  the behaviour and the sentence still hold.
- **`docs/proving-guide.md:418`** reads well, and `W-MATCH-DECISION-IF`
  is removed. **`docs/guide/10-proofs.md:584`** is accurate.
- **`docs/proposals/decidable-record.md` §5.1/§8 isn't updated.** It still
  says `bind.rs`'s comparison case is "generalised", and that
  `short_circuit`'s choice "goes". Both stayed. Add a line for each with
  the reason the lane gave: `DecEq.sound e` at `List/Lemmas.sw:1688`, and
  the 5 aoc proofs that rewrite with `Bool.andTrue`/`andFalse`. Otherwise
  the note misleads stage 4.

## 5. The `bind.rs` generalisation: drop it for good?

**Yes, drop it.** Its point was that `==` and a plain `if` would write any
literal instance's `holds` in place. Now that the record computes, the
elaborator, kernel and runtimes reach the same `Bool` by one projection of a
literal, so all it would gain is a few steps. Its cost is real: `==` would
elaborate to a different term, and lemmas stated with `==` (`DecEq.sound e`)
would stop unifying with it. Every such lemma would need restating, for no
gain users can see. Keep the six-comparison case, which pins runtime natives.
SW-2704's reader ("which proposition does this `Bool` decide?") computes the
`holds` anyway and doesn't need it. Record the decision in the proposal (4
above). The same reasoning supports keeping the `short_circuit` choice.

## Follow-ups

1. rewrite.rs: try the plain motive before selective carrying, or base
   `decides_other` on the goal's `p` (should-fix; §1).
2. Add focused examples for `Met::Sound`/`Met::Complete` carrying, for
   rewrite carrying (`Place::Goal` and `at`), and for `plain_ifs`'s paths in
   function equations (§1, §2).
3. Pin `Decidable.elim`'s helper shape in a unit test, and keep one
   `elim_helper` in `core` (§2, §3).
4. pretty.rs: print the helper call as `if` only when its test is the
   decision's (§1).
5. omega `as_if`: check that a branch doesn't use its proof (§1).
6. matching.rs: decide per occurrence whether to carry, as rewrite does
   (§2).
7. Readable `f.eq.*` hypotheses for `||`/`not` conditions (§1).
8. Measure `cases`' per-split `motive_checks_now` on a `cases`-heavy proof
   (§1).
9. Small cleanups: `carried_any`, the `Search::carry` doc, `plain.rs:734`
   wrap, the `matching.rs:2149` comment, `match-if-and.sw`'s header, and
   renaming `Builtin::ToBool` to `Holds` (§3).
10. syntax.md `if` row: hypotheses are on the test, not `c`; and the
    proposal §5.1/§8 deviations (§4).
