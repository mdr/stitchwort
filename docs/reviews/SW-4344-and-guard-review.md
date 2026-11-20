# SW-4344 review: a `&&` guard whose proof the arm uses, stated as its `Bool` (D3699)

Ticket SW-4359, Opus paper review of `lane/SW-4344` (f8c0674ff, 7c820d131),
20 Nov 2026. Read only: no builds or tests run.

**Verdict: merge.** No blockers and no required fixes. Two notes worth
filing (N1, N2), one optional tidy (N3).

## What the change does, as read

- `probe_row` (equations.rs:2672-2686): a guard tested by `Decidable.elim`
  (`dec`), written as a `Bool` (`written_bool`), not an unfolded comparison,
  not `if h:`, whose `Bool` `c` reads as a conjunction (`decided_view`) gets
  `cond = (c = True)` and `GuardRead.tested`. Given `logic::Condition`, `dec
  && written_bool` without `unfolded` or `if h:` is exactly
  `Condition::Conjunction` (`Condition::Bool` carries no decision), so the
  new branch reaches the `&&`-with-used-proof case and nothing else.
- Statement RHS (equations.rs:3330-3337): the arm's proof is
  `(Decidable.and dl dr).sound guard`, from the guard's own `Bool`
  (`tested_proof`), not a bare variable.
- eqK walk, arm (7347-7352): the branch is read with that proof, and it is
  the `hyp` given to `dec_step`. Below the arm (7502-7511): `Decidable.refute
  d hyp h` with the tree's decision `d` (`andThen`), `hyp: c = False` (a
  `NotGuard`, or an overlap applied; `fails_as_bool` is true for `c = True`,
  so the overlap path gives the applied `= False`).
- `f.induct` (induct.rs:3686-3721): the split stays `Decidable.elimProof`
  on the tree's decision; the facts are `d.complete h: holds d = True` and
  `toBoolOfNot d r: holds d = False`.

## 1. Statements: what D3699 says, and the same in eqK and induct

- Arm: `guard: (a && b) = True`; below, `notArmJ: (a && b) = False`, or for
  a partial overlap `∀ vars => x = p → … → (a && b)[σ] = False`. That is
  D3699's rule for a condition written as a `Bool`, and now matches what
  every other `Bool` guard gets (pattern-guards.md D3699 paragraph,
  syntax.md "Equations").
- eqK and induct are identical by construction: induct's case binders are
  `s.binders` (induct.rs:1000), the eqK statement's binders, built from the
  one `GuardRead` by `hyp_type`; the facts only have to convert to those
  types. `holds (andThen dp (u => dq)) ≡ ite dp.holds (u => dq.holds) (u =>
  False)` is `a && b` by unfolding (Decidable.sw:180), so they do; the
  kernel confirms it on `positiveGaps.induct` and `capped.induct`.
- Coverage: `positiveGaps` (arm, partial overlap eqK, induct with
  `guard.read.right`), `capped` (full overlap, `notArm2` as `c = False`, and
  `byComputing` discharging it at `0`). Good.

## 2. Can a generated term state something other than the definition's behaviour?

No. Every changed term goes through `declare_def`, and the statement can
differ from the old one only in the hypotheses' form (`c = True` for `P ∧
Q`, `c = False` for `¬(P ∧ Q)`), which are equivalent through the
conjunction's decision (`sound`/`complete`, `refute`/`toBoolOfNot`) and
which the kernel checks the proofs against. The only other change to a
statement is the proof term inside the RHS, discussed next.

## 3. The first risk: an arm that computes with the proof

docs/core.md "Proof irrelevance" (line 276) and line 145: there is no
definitional proof irrelevance for bare proofs; conversion skips proofs
only at proof positions (a constructor's proof field, a data type's proof
parameter, a definition's inert parameter). So the RHS's `sound guard` and
the definition's `h` from `Decidable.elim` are equal to the kernel only
where the arm uses the proof at such positions.

The walk handles both cases, and neither is unsound:

- **Proof used only at irrelevant positions** (`gap x y` with `[auto h:
  x < y]`, inert): `proof_is_inert_in` holds, `uniq = None`, and `ey = h
  => q` checks because `body[h]` and `body[sound guard]` convert. This is
  the path the examples test. Before the change it was the same mechanism
  with a different stated proof (the hypothesis variable, also not the
  elim's `h`).
- **Proof computed with:** `dec_step` needs `uniqueness(P ∧ Q, andThen …)`.
  `uniqueness` (equations.rs:4568) gives a proof only for an equation of
  `Bool`s or a `DecEq.decide` decision; `P ∧ Q` decided by `andThen` is
  neither, so it always skips (`E-NO-EQUATION`, D2180). That was so before
  the change too. The `Uniq` branch with `hyp = sound guard` is therefore
  unreachable for a tested guard; were it reached, `unique (sound guard)
  h'` is well-typed (both are proofs of `P`) and the kernel checks it.

So the step is sound and well-typed; "untested" is accurate but the
untested branch is dead for this guard form. No fix needed.

**N1 (note, file). The same substitution in `f.induct` can lose an
induct the old form had.** induct's IHs are read from `s.rhs` (induct.rs
997-1013), which now holds `sound guard`, while the split binds the arm's
proof as its own `h` and the case's `guard` as `complete h`. A recursive
call whose *argument* computes with the conjunction's proof at a relevant
position needs `sound (complete h) ≡ h`, which doesn't hold, so the kernel
refuses `f.induct` (reported as a skip). Before, `guard` was `h` itself and
the two matched exactly. Not unsound, and narrow (structural recursion
rarely lets an argument depend on a proof; `Fin.mk n p` and inert
`[auto]` parameters are proof positions and convert). Suggest a ticket:
try to build a reproducer (a recursive call through a non-inert use of the
proof); if one exists, bind the arm's proof in the induct case to the
split's `h` rather than `sound guard`, or skip with a clear reason.

## 4. The silent fallback

If `decided_view(c)` is `None` for a `Condition::Conjunction`, `tested` is
`None` and the guard keeps `P ∧ Q` / `¬(P ∧ Q)` with no message.
`BranchLib::conjunction` fails only when `Std.Decidable.and` or the
`toBool` lemmas aren't loaded (std before core/Decidable.sw), when the
`as_bool` isn't `Bool.ifThenElse a (u => b) (u => False)`, or when an
operand has no reading (a `Bool` side without `decTrue`). `logic::Conjunct`
builds exactly this `as_bool`, so outside std's bootstrap the fallback
shouldn't occur. Its statements are still true (the old, kernel-checked
form), so it is a form inconsistency, not a wrong theorem.

**N3 (optional).** Make the end state uniform: for `dec && written_bool &&
unfolded.is_none() && !guard_named` with no view, `Skip("an `&&` guard
whose proof the arm uses isn't read as a conjunction")` instead of falling
through to `prop`. Orchestrator's call; a debug assertion would do as well.
Not needed to merge.

## 5. Scope (D3688)

Not a narrowing. No driver, grammar or alphabet change, no program refused
that was accepted; the new `Skip` in `tested_proof` only drops a generated
equation, and can't fire where `tested` was set (the same view is read
from the same `c`). No top theorem gains a condition: the hypotheses change
form to the equivalent `Bool` statement. The definition's elaboration is
unchanged (`modGuard`, `positiveGaps` hashes are the definition's own; only
`modGuard.eq1`/`eq2` move). `auto-conjunction.sw` has no proof using
`modGuard.eq*`. Repo proofs outside examples that use the old `P ∧ Q`
hypothesis of such an equation (aoc, rogue, tools/fmt) weren't checked by
the lane; Overmind's rolling check covers them.

## 6. Docs

syntax.md "Equations", proving-guide.md, guide ch. 10 and pattern-guards.md
(D3699 paragraph) all drop the exception and give the example with its
`(i < n && 0 < i) = True` form; no leftover "still `P ∧ Q`" in docs or web
(the one in docs/reviews/SW-4341 is a record and stays). The previous
review's N2 is resolved by the removal.

**N2 (note).** The arm's proof is `Decidable.and`'s `sound` while the
failure path and induct use the definition's `andThen`; both tests are `a
&& b` by computation, so this is cosmetic, but a one-line comment at
`tested_proof` saying why the statement can't use the tree's decision (it
is built from the guard record, without the tree) would save the next
reader the question.

## Verdict

Merge. File N1 (possible lost `f.induct` when a recursive call's argument
computes with a `&&` guard's proof; reproducer first). N2 and N3 are
optional tidy-ups.
