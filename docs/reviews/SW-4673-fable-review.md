# SW-4673 (rules K and S, full proof irrelevance stage 4): Fable review

Fable paper lane, 23 November 2026. Reviewed: `lane/SW-4673` at `ad3b6e363` (`ce8791355`,
`823f5ecfa`, `ec9b19733` on `59e5b7d97`). Decisions it implements: D3721, D3723, D3724. Read
with it: the lane's notes (`docs/reviews/SW-4673-notes.md`), the design note §3, §4.4, §5, the
audit's conditions A, B, G, and the stage 3 review.

Marks: **[run]** a probe checked with the branch's release binary and with `main`'s;
**[read]** the code read today; **[inferred]** reasoning from what I read.

## Verdict

**Merge.** I found no way to make the checker accept something false. Every probe I wrote to
get a false equation through rule K, rule S or the comparison of stuck casts was refused, and
the five soundness examples that moved to accept are each justified by the rule, not by a gap.

One finding should be fixed before stage 5, and can be a follow-up ticket rather than a
condition of this merge (the orchestrator's call; F1 below): **a statement `main` checks in
0.35 s runs for ever on the branch**, because a cast now compares its ends every time it is
evaluated, and that cost can double at each level of a recursion. It is a synthetic program,
and it is a hang, not a wrong answer.

| | Finding | Severity | Confidence | Fix, size |
|---|---|---|---|---|
| F1 | A stuck cast tests its ends eagerly at evaluation; in a recursive definition whose cast's ends mention the recursive call, the cost doubles per level, and the budget doesn't stop it within 100 s. `main` checks the same statement at once | medium | high (run) | make the cast a real lazy form (test the ends only when its head is needed), and share the evaluation of a call that occurs in both ends; M, Opus |
| F2 | Four walkers over values skip a cast's ends (`check::Unchanged`, `unify_index::value_levels`, `value::identical` and `shape_hash`, `elab/matching/untouched.rs`). Safe today for reasons that live nowhere in the code | low today, medium for stage 5 | medium | walk the ends, or say in each why not; S, with stage 5 |
| F3 | Rule K fires on a `J` whose mark is *unknown* (the elaborator's own terms), not only on one the kernel marked as data. `docs/core.md` says K reads only kernel-derived marks | low | medium | fire only on `NotProof`, or correct the doc; S |
| F4 | In the unifier, two stuck casts whose shapes differ are answered "different" at once, even when an end still holds an unsolved unknown that could later make one of them fire | low (elaboration order only) | low (not reproduced) | postpone while an end mentions an unknown; S, Opus |
| F5 | The reference evaluator's K and S are separate code but the same design, and it takes the ends from the same annotation the kernel wrote | note | high | none now; see "The reference evaluator" |

No finding is a soundness bug. No question here is Matt's.

## The soundness set and the moved examples

`binary(running) & test(/examples::soundness/)` passes on the branch **[run]**.

| Example | Why it is accepted now | Justified? |
|---|---|---|
| `-05` (`J (y e => Nat) d h`, `h: n = n`) | rule K: ends `n`, `n` | yes |
| `-17` (`cast a a byComputing x = cast a a h x`) | rule K: ends `a`, `a` | yes |
| `-18`, `-21`, `-27` (`match t with MkTok => k`, `t: Tok`) | rule S, no indices, no fields | yes: `Tok` passes `E-PROP-ELIM`, and has one element |
| `sealed-theorem-cast`, `omega-basics`, `quot-transport-ind-rule-k` | rule K on closed ends (`3 + 0` and `3`; `0` and `0`) | yes; the proof (a sealed theorem, `Quot.ind`) is never opened |

The four new refusals (`-31` fresh variables, `-32` different ends, `-33` indices apart, `-34`
indexed with a field) each fail for the reason their header gives **[run, read]**.

## 1. Rule K

**Can the ends be wrong? No [read].** The ends are the annotation on the proof,
`Ann(p, Eq(A, x, y))`, and there are three ways one gets there:

- `infer_j` writes it from the type it inferred for `p` (`check.rs:1168`).
- The term already has one (re-checked, read back, or written by the elaborator). `infer`
  on `Ann` checks `p` against the annotation (`check.rs:449`), and `infer_j` then takes `x`
  and `y` from that annotation's own value. So an annotation with ends that aren't the proof's
  is a type error, and one with ends convertible to the proof's is as good as the kernel's.
- A `J` whose proof isn't an equation is refused before any of this (`E-TYPE-MISMATCH`).

Substitution and shifting treat the ends as part of the term, which is the point of using an
annotation; read-back writes the stored ends back (`value.rs:3841`, `reference.rs:980`), and
the unifier's renaming goes through them (`unify.rs:3862`), so its scope and occurs checks see
them. The check cache keys entries by the build's source fingerprint, so no format bump is
needed: an entry written before this change is another build's.

**Condition A (fresh variables) holds [read, run].** `meet_in_evaluation` compares at
`2^40 + cast_levels` and raises `cast_levels` by `2^24` for the duration, restoring it on exit
and on error. A test met while another's comparison is running therefore starts above every
variable the outer one can have made. Probes:

- `k_nested.sw`: an inner cast with ends `w => w` and `w => z`, where `z` is the outer test's
  fresh variable. If the inner test reused the outer's level it would call them equal.
  Refused. The partner with ends `w => z`, `w => z` is accepted.
- No context reaches `2^40`, and nothing in `value.rs` allocates or loops by `level` (the
  `(0..level)` environments are in `check.rs`, `pretty.rs` and `unify_index.rs`, which the
  comparison doesn't call).
- Values holding a reserved-level variable don't outlive their test: the memo is made new for
  each test, and a glued call's kept unfolding made under the fresh variable belongs to a call
  value made under it.

**Condition B (stuck casts by parts) holds [read, run].** `conv_step`, `reference::conv_in`
and the unifier compare the ends' type, the ends, the motive, the base, then the rest of the
spines, and never the heads or what precedes the cast. Probes, all as they should be: equal
ends, motive and base with different proofs (accepted); different bases, different ends,
swapped ends (`x = y` against `y = x`), a different argument after the cast (all refused); a
stuck cast against its own base (refused); two casts composed there and back (refused).
Transitivity: the arm only adds equalities to the ones the same-head arm gave, and what it adds
holds in the model, so I see no new failure of it **[inferred]**.

**The gate on the mark (F3).** `value.rs:2189` fires for any mark but `Proof`, so for the
elaborator's *unknown* too. In a kernel-checked term every mark is decided, so the kernel's
own evaluation is as the spec says. In the elaborator an unmarked `J` into a proposition whose
proof happens to carry an annotation would compute by K, which is sound in the model and
re-checked by the kernel, but is the Abel-Coquand door in principle. I couldn't open it: a
written ascription on the proof is dropped before evaluation (`ac3.sw`, `ac4.sw`: same result
on both binaries).

## 2. Rule S

**The acceptance in `infer_proj` is sound [read].** `Proj(D, i, t)` for a proposition with one
constructor, no indices and only proof fields gives a proof of field `i`'s statement from a
proof of `D`: a proof out of a proof, which a `case` into a proposition could already do. It
doesn't check that `D` is non-recursive or alone in its group, and needn't: nothing data-valued
comes out. It adds no eta for such a `D` (D1981's limit is untouched), and `Quot` isn't
involved (its forms are checked by `infer_quot`).

**No-index case [read, run].** The evaluator fires on one constructor, all fields proofs, and
a definition whose result is data. It doesn't re-check `E-PROP-ELIM`'s other conditions (not
recursive, not nested, alone in its group); it relies on the kernel having refused such a
`case` into data. That holds: the only exemption is "every branch impossible", which needs
indices, and with indices the rule requires no fields. `s_rec.sw` (self-referential), `s_data.sw`
(a data field) and `s_two_ctor.sw` are still `E-PROP-ELIM`.

**Indexed case [read, run].** The scrutinee's type is read off the definition's type at the
scrutinee's level and evaluated over the arguments before it. I looked for a way to read the
wrong type and found none:

- The tree always starts with exactly the definition's arguments as its environment
  (`value.rs:3084`, `:3170`, `:3226`, `:3341`), and matches only append to it, so level `k`
  below the arity is parameter `k`.
- A `case` in a leaf, outside the tree, runs with no definition (`value.rs:1881`), so stays
  stuck; so does one on a field of an enclosing match (level at or above the arity).
- A type not written as a function type that far gives no answer, so stuck.
- An impossible branch needs the indices to clash, and then they aren't `≡`.

Probes: a match on `h` nested under a match on the parameter `h`'s type mentions (refused with
the index unknown, accepted with it `0`); two parameters of the same family, only the first
with equal indices (refused); a branch that uses the refinement to return `v: p x` as `p y`
(refused with `x`, `y` apart); a heterogeneous equality with two indices (accepted on `a x a x`,
refused on `a x a y`). Shadowed parameters can't be written (`E-DUPLICATE-PARAMETER`).

## 3. Subject reduction, termination, Abel-Coquand

- Subject reduction is as the notes say, including the gap they name: a K step takes
  `P y p` to `P x byComputing`, equal only where D1′ skips the proof. That is October's §5.7
  gap, not a new one, and the model has the two equal.
- `examples/accept/abel-coquand.sw` checks unchanged. The note's claim that "a cast into data
  can't be built from that loop" needs one qualification: a cast into data **along** the loop
  can. `J (y e => Nat) n (bigOmega h (0 = 0))` now computes to `n` (`ac1.sw`, accepted; refused
  on `main`). It terminates because the loop's own `J` is into a proposition and stays stuck.
  The answer is the model's.
- A cast's proof is still evaluated to its head before the ends are tested (`Frame::JProof`
  forces it, and a folded call is unfolded). So "the proof is never looked at" means its value
  never decides the answer, not that it costs nothing. Stage 5's rule F is what stops that.

## F1: the ends are tested eagerly, and the cost can double per level

```
import Std (Nat)
def idn (k: Nat): Nat := match k with
  | Zero => Zero
  | Succ j => Succ (idn j)
def tower (hyp: ∀ (k: Nat) => idn k = k) (n: Nat): Nat := match n with
  | Zero => 0
  | Succ m => J (y e => Nat) 0 (hyp (tower hyp m))
theorem oneStep ∀ (hyp: ∀ (k: Nat) => idn k = k):
  tower hyp 41 = J (y e => Nat) 0 (hyp (tower hyp 40)) := byComputing
```

`main`: checked, 0.35 s. Branch: still running at 100 s, when I stopped it; no `E-RESOURCE`.
With `tower hyp n = 0` the branch takes 0.37 s at `n = 12`, 0.58 s at 16, 1.29 s at 18, about
double per level **[run]**.

Why: on `main` the left side unfolds once to a `J` stuck on `hyp (…)` and the two sides are the
same term. On the branch, evaluating that `J` tests its ends, `idn (tower hyp 40)` against
`tower hyp 40`. Each end holds its own copy of the call `tower hyp 40`, each is evaluated, and
each evaluation tests the next level's ends the same way.

The design note calls a cast with equal ends a *lazy form*. The implementation decides it at
evaluation instead (`Frame::JForced`), so every evaluation of a cast pays for a comparison,
needed or not. Two changes, either of which removes this case: test the ends only when rule E
needs the cast's head (here the two sides are identical and nothing needs it), and evaluate a
call that occurs in both ends once. Stage 5's rule I doesn't fix it. The notes' sentence "the
shared budget bounds it" is true in principle and not in practice at this size.

How likely in real code: it needs a cast whose proof's statement mentions the enclosing
recursive call, with ends that aren't written alike. I'd expect none in std or AoC; the
verifier's and Overmind's timings will say.

## F2: walkers that skip the ends

`Elim::J { motive, base, .. }` with the ends ignored, in `check.rs:2568` (`Unchanged`),
`unify_index.rs:453` (`value_levels`), `value.rs:5881` (`shape_hash`) and `:6299`
(`identical`), and `elab/src/matching/untouched.rs:251`.

- `Unchanged` decides whether a context value can be kept as it is when a matched variable is
  replaced. A cast along `h: n = m` mentions `n` only in its ends; kept through a match on `n`
  it would hold ends that no longer fire or compare as the re-evaluated ones do. It can't
  happen today, because a `J`'s motive is always a closure and `Unchanged` gives up on any
  closure (`check.rs:2514`). Nothing says the ends depend on that.
- `value_levels` gives the same answer as on `main`: the ends repeat what the proof's type
  says, and that type was never in the value.
- `identical` and `shape_hash` compare the proof (head and earlier spine), and one proof has
  one type, so equal proofs have convertible ends. **That argument ends with rule I**: once
  proofs aren't compared, `identical` must compare the ends, or the memo will answer for two
  casts with different ends.

## 4. The unifier

- `fire_cast` is a `conv` on stored values, solves nothing, writes no trail, and its result
  is pushed as work, not stored **[read]**. Condition G's read-only requirement holds.
- **A glued call's kept unfolding computed while a cast fired on a solution later taken
  back**: traced. A kept unfolding records the metavariable epoch it was made in and is used
  only in that epoch or from epoch 0, which is the kernel's and never the elaborator's
  (`value.rs:316`-`334`); taking a solution back starts a new epoch. The remembered pairs of
  the tree comparison are keyed by the epoch too (`value.rs:5566`). "Equal with fewer
  solutions stays equal with more" still holds, since K only adds equalities as solutions
  arrive. No new cache was added. Sound **[read]**.
- **An assumption mentioned only in a cast's ends now counted as relied on**: not probed. The
  ends are built from the proof's type, which is made of the types of the proof's own
  variables and constants; a walk that follows what the proof mentions reaches the same
  declarations through their statements. If it does differ, it over-reports, the safe side
  **[inferred]**.
- F4: the by-parts arm answers "different" when the spines after the casts don't pair up
  (`unify.rs:2227`), and other arms treat a cast waiting on an unknown as a rigid stuck term.
  Before this change a stuck cast never became anything else, so that was right; now it can
  fire later. The cost is an elaboration error where postponing would have succeeded; the
  kernel sees nothing wrong either way. Not reproduced.

## 5. The reference evaluator

`reference.rs` has its own K (in `eval` and `apply_spine`), its own counter for the reserved
levels, its own S (`rule_s`), read-back and by-parts comparison, and calls no evaluating code
in `value.rs` **[read]**. Two limits on what that independence buys:

- It is the same design, line for line in places (`rule_s` and `one_shape`). It would catch a
  slip in one of them, not a mistake in the rule.
- It reads the ends from the annotation the kernel wrote. Nothing but the kernel's own check
  of `Ann` establishes that the ends are the proof's. That check is three lines and I think it
  is right; a validator pass that re-derives the ends from the proof's type, as
  `validate_marks` does for marks, would make it independent.

## 6. `docs/core.md`

Accurate and complete for what was built: the term form, `Proj`'s second case, K, S and
D3724's scope, the reserved levels, by-parts comparison, the elaborator's behaviour, the
subject-reduction gap, and that §5.2's "no K-like rule" is superseded. Three corrections:

- "Rules K and S read only the marks the kernel derived itself": the evaluator also fires on
  an unknown mark (F3).
- "A cast into data can't be built from that loop": add that one *along* it can, and computes
  (section 3).
- "a `J` into a proposition carries nothing": one whose proof was already annotated keeps the
  annotation; it is ignored because of the mark.

## To carry into stage 5

1. F1's fix, before rule I multiplies the number of casts and matches that fire.
2. F2: `identical` and `shape_hash` must take the ends once proofs are skipped; `Unchanged`
   must walk them or say why it needn't.
3. Rule F for a cast's proof: stop evaluating it before the ends are tested.
4. The by-parts arm takes the first `J` with ends in the spine. With decided marks nothing
   after a data cast can be a `J`'s proof, so first and last are the same; keep that true if
   marks can be unknown where rule I reads them.
5. `one_shape` trusts the kernel's `E-PROP-ELIM` for "not recursive, alone in its group".
   Under rule I, if any other path can put a `case` on a proof in a data definition's tree,
   re-check them there.
6. The audit's open item, "equal arguments in shortcut mode give equal unfoldings" with K
   tested in normal mode inside an unfolding compared in another: I found nothing against it
   (K only adds equalities, and the ends test always runs in normal mode), but I didn't trace
   the shortcut mode's callers.

## Not checked

- The test of record (`proof_equivalence`): I read the lane's log (20 passed) and didn't
  rerun it.
- Whole std, `tools/fmt`, AoC, the roguelike, the examples suite: the verifier's.
- F4 and the assumption walk: reasoned, not reproduced.
- The elaborator's other value walkers (`omega.rs`, `ring.rs`, `effects.rs`, `partial.rs`,
  `cases.rs`): each gives up on any `J`, so the ends don't matter to them; seen in a listing,
  not read.
- Extraction and the fast runtime on a term holding a `Proj` of a proof: such a term is a
  read-back, which isn't run; not traced.
- That by-parts comparison is sound in the model: argued (two transports of one base along
  proofs of one equation), not proved, as in the audit.

## Probes

Thirty-five files, checked one at a time with both binaries; they are in the lane's scratch folder
(`sw4673/review`) and will go with it. The ones worth keeping as examples: F1's program (as a
timing test once fixed), `k_nested.sw` and its partner (condition A under nesting), `s_shift.sw`
and its partner (a match on a proof nested under a match on its index), `s_two.sw`, `s_het.sw`
and `s_het_bad.sw`, and `ac1.sw` (a cast into data along the Abel-Coquand loop).
