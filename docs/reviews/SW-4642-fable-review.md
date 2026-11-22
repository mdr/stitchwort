# SW-4642 review (Fable): the conversion change in 622010542

Branch `lane/SW-4642`. Read-only paper review: nothing built or run, so
every claim below is reasoned from the code. Line numbers are on the branch
(`crates/core/src/value.rs` unless another file is named).

## Verdict

**Merge with changes.** The new conversion step is sound in every mode and
can't loop. But the lane's claim that the kernel is unaffected is wrong:
the kernel's conversion can reach `unfold_folded_head` with a `Some`
result, so the kernel now accepts more than it did. What it newly accepts
is true (delta, then the ordinary eliminations), and the equality rule in
`docs/core.md` already asks for it, so this closes an unrecorded gap rather
than opening a hole. The changes wanted before merging are a `docs/core.md`
update (D3210), a kernel-level test, one guard and two comment fixes.

## 1. Kernel acceptance: yes, the kernel reaches it

Neither `unfolds_head` (3140-3147) nor `conv_step`'s unfold stage
(4200-4224) looks at `Machine::kernel`. The kernel builds values the new
path unfolds in two ways, neither involving the elaborator-only arm.

**K1 (the main one): a theorem applied beyond its arity.** A definition's
arity is its body's leading lambdas (`docs/core.md:153`: "Lambdas inside
the case tree belong to its result"), so a theorem whose proof is
`match n | … => (h => …)`, a tactic proof that introduces after a case
split, or a point-free `:= other x` has an arity below its number of
arguments. Applying it fully goes through `apply_step` (1317-1320): the
argument is pushed on the folded call's spine and `Control::Unfold` runs,
and `case_tree` (2788-2812) only runs a tree when `def.arity ==
spine.len()` (2791). So `T a h` is `Neutral(Def(T), [a, h])` in every
mode, the kernel included, with `T a` not stuck at all. Nothing unfolded
that value before this branch: `is_folded` needs exactly `arity`
arguments or a projection suffix (2965-2986), and `JForced`, `Scrutinee`
and `ProjForced` test `folded_call`, which is false for it.

On the branch, `unfolds_head` is true for it (more than `arity` elims, an
`App` after the arguments, `folds`, a body), and `unfold_folded_head`
(3107-3136) unfolds `T a`, applies `h` and returns `Some`. The same holds
for `J m b (T a h)` (`[a, h, J]`).

Failure-to-accept scenario on `main`, accepted on the branch, in the
kernel (a probe worth running; syntax approximate):

    theorem viaCase ∀ (n: Nat): n = n → n = n :=
      match n | Zero => (h => h) | Succ _ => (h => h)     -- arity 1
    theorem probe ∀ (h: 0 = 0) (x: Tag 0):
        J (m _ => Tag m) x (viaCase 0 h) = J (m _ => Tag m) x h := byComputing

Left side: `Neutral(viaCase, [0, h, J])`. Right side: `h` with a `J`. On
`main` the heads differ and `opens_by_tree` is false for a theorem, so
conversion says "different". On the branch the left unfolds to the right.
Definitions marked `Def::fold` (dictionaries, `decreasing` definitions)
have the same shape when declared with a function result.

**K2: a definition with a `Quot.lift` leaf applied beyond its arity and
stuck at the lift.** `f q y` (arity 1) is `Neutral(Def(f), [q, y])`.
`unfolds_head` accepts `folds_on_lift`, and `unfold_folded` runs the tree
with the stuck flag false, so a stuck lift leaf comes back as the lift
itself, not the call (1945). The kernel now compares `f q y` as
`Quot.lift F H q y`. A bare `f q` was already compared this way; the
branch extends it to the over-applied form.

**K0: stuck in its own tree.** `J m b (T a)` with `T a` stuck in its own
tree (the only way the kernel builds a `J` straight after the arguments,
`Frame::Unfolding`'s first arm) passes `unfolds_head`, then
`unfold_folded` finds it stuck and returns `None`. No change in what's
accepted, only a tree run per comparison, as for a bare stuck call.

**Is it sound?** Yes. The step is delta on a body the kernel checked
(`folded_call` requires `body_seen`, so hidden opaque definitions,
stand-ins, pending group members and assumptions are excluded, under the
transparency set of the moment), then the rest of the spine replayed by
`Frame::Replay`/`ReplayElim`, which apply, project and `J` by the
ordinary rules (`Refl` gives the base, a neutral takes the `J`).

**Does `docs/core.md` cover it?** The equality rule does: a folded call
is a lazy form, a head is what's left once lazy forms are removed, and
rule C answers "different" only on rigid heads (`docs/core.md:325-331`).
The plain evaluator, which says what's equal, computes `T a h`
(`reference.rs:25-28`: no folds). So `main`'s behaviour is an unrecorded
known gap, and the branch fixes the conversion half of it. But the text
at `docs/core.md:266` says only three things look inside a proof and
"each unfolds a folded call first", which doesn't describe an
over-applied call, and nothing says conversion unfolds a call with
eliminations after its arguments.

**`docs/core.md` must change** (D3210: what the kernel accepts changed):

- at "Theorems stay folded too" (266) and the lazy-forms list (325): a
  call folded by name, or on a lift leaf, with further eliminations after
  its arguments (`T a h`, `J m b (T a)`) is compared unfolded with the
  rest applied, in every mode;
- in "Known gaps": evaluation still leaves `T a h` unfolded when a
  `case`, `J`, projection or lift inspects it (rule E), so
  `J m b (T a h)` with `T a h` computing to `Refl` stays stuck until a
  comparison looks at it. That half is pre-existing and not fixed here.

## 2. Soundness of `unfold_folded_head` in every mode: sound

- **Mixed tails** (`[Proj, App]`, `[App, J]`, `[J, App]`): replayed in
  order by `Frame::Replay` (2242-2290). A projection or `J` goes through
  `ReplayElim` (2292-2334), which unfolds a folded value first, so a
  chain of theorem calls is followed. In the kernel
  `names_folded_fields` is false, so the projection is the plain one.
- **Arity counting.** Arity counts every leading lambda and the spine
  holds every argument, implicit ones too, so `spine[..arity]` is the
  call. Lifted helpers are ordinary definitions with their own arity.
- **Opaque, sealed, stand-ins.** Excluded by `body_seen` in
  `folded_call` (2981-2986) and in `unfolds_head`.
- **Erasure.** `ReplayElim`'s `J` arm has no erased case, unlike
  `JReady`, but `folds` is false while a program runs, so the path is
  never taken then.

**Finding F3 (low): a missing guard.** `unfolds_head` checks that the
first `arity` elims are applications; `unfold_folded_head` doesn't, and
`conv_step` calls it on both sides whenever the stage runs, whichever
side triggered it. A `J` or projection among the first `arity` elims
would reach `folded_parts`' `unreachable!` (2999-3003). Only an ill-typed
value has that shape, so it's a panic risk, not a soundness one. Start
`unfold_folded_head` with `if !unfolds_head(g, value) { return Ok(None) }`
so the two can't drift.

**Finding F4 (low): two comments are now untrue.** `ReplayElim`'s "Only
while elaborating (a metavariable's solution)" (2294): the kernel reaches
it through `unfold_folded_head`. And the arm's "Elaborator only, as for
fields" (2186) is true of the arm but reads as covering the conversion
rule beside it, which isn't gated.

## 3. Termination: no new loop

`unfold_folded_head` returns `Some` only when `unfold_folded` did, and
that returns `Some` only when the call's case tree took a step (a tree
stuck in itself returns `None`, 3070-3075). So each pass through the
unfold stage does at least one real unfolding. If the result is again a
folded head with eliminations after it (the inner theorem over-applied),
the next pass unfolds that one. A recursive theorem unfolds only while
its cases fire, which is the termination argument `docs/core.md:264`
already makes for evaluation. Every pass costs a budget step
(`conv_with`, 3945, and `run_on`, 1450), so a runaway ends in
`E-RESOURCE`. The unifier's rule is the same.

## 4. `unfolds_head` against `unfold_folded_head`

- `unfolds_head` true, `unfold_folded_head` `None`: the call is stuck in
  its own tree (K0). The stage is taken, nothing is pushed, and the pair
  falls through to the rules it met before. Correct; the cost is one tree
  run.
- `unfolds_head` false, `unfold_folded_head` `Some`: only
  `native::folds_mul`, which `folded_call` accepts and `unfolds_head`
  doesn't. A product is a number and can't have a `J` or application
  after it, so it's unreachable in well-typed values. F3's guard removes
  the question.
- Same head on both sides: `conv_step` now sends such a pair to
  `Recursion::Folded` (4202-4206), which compares whole spines, `J`s and
  later arguments included (`same_spines` → `spine_pairs`, 4592-4628),
  and only answers "equal"; on failure it goes on to the unfold stage. I
  checked this because a comparison of the arguments alone would have
  been unsound; it isn't that. It does compare the spines twice when they
  differ and nothing unfolds, as bare folded calls already do.

## 5. The unifier's rule (`crates/elab/src/unify.rs:1812-1823`)

- It can't solve a metavariable wrongly: it replaces a value by one equal
  to it by delta and pushes the pair again. Metavariable-headed sides are
  excluded, so an unknown is still solved with the call by name.
- **Finding F5 (low): it accepts less than `main` in one narrow case.**
  The rule skips two values with the same head. `(T a) + J` against
  `(T a2) + J`, where `a` and `a2` differ but the unfoldings are equal
  (an argument `T` ignores), was `U + J` against `U' + J` on `main` and
  unified. Now the shape rule compares the spines and fails; `conv`
  handles this (Folded, then Unfold) but the unifier doesn't. Make it
  match the folded rule above it (1799-1809): same head, try the spines
  with roll-back, otherwise unfold both.

## Findings

| # | Severity | Finding | Action |
|---|---|---|---|
| F1 | medium | The kernel accepts more (K1, K2); the lane's "kernel isn't affected" is wrong. Sound. | Update `docs/core.md` (section 1); say so on the ticket and in the commit |
| F2 | medium | No test covers the kernel's new acceptance, or the still-stuck evaluation half | Add the probe above as an example and to `proof_equivalence.rs`'s wrapping test (an over-applied theorem and an over-applied lift-leaf definition); run it on `main` first to confirm K1 |
| F3 | low | `unfold_folded_head` lacks `unfolds_head`'s argument check | Guard it |
| F4 | low | Two stale comments (2294, 2186) | Reword |
| F5 | low | Unifier skips same-head pairs | Mirror the folded rule, or file it |
| F6 | info | Evaluation leaves `T a h` unfolded under `case`, `J`, projection and lift (pre-existing, rule E gap) | New ticket; a known-gaps row |

## What I couldn't settle without running anything

- K1 is read from `apply_step` and `case_tree`; I haven't seen the probe
  fail on `main` and pass on the branch. If elaboration always gives
  theorems an arity equal to their argument count, K1 would need a
  hand-built term, but `docs/core.md:153` says otherwise.
- Whether `proof_equivalence.rs`'s properties and all of
  `examples::soundness` still pass. A change to what the kernel's
  conversion accepts should have both run before merging.
