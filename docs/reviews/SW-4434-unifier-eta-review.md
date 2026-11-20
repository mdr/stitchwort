# SW-4434 review: eta-contractible lambdas in `unify_by_unknown_arguments`

Reviewer: Opus paper lane SW-4439, 20 Nov 2026. Branch `lane/SW-4434`,
one commit `f104f7721`. Paper only: nothing built or run.

**Verdict: merge after one named fix (M1).** The change is small, sits
on the unifier's last-resort path, and cannot affect kernel soundness:
the solution it records is the lambda as written, not the contracted
function, and every solution still goes through `unify_solving_arguments`
with the `only_whole` guard and full undo. One new error path (a size
error from the read-back) is fatal where `main` would have carried on;
that is the only must-fix.

## What the change does

`unify_by_unknown_arguments` (crates/elab/src/unify.rs) has one caller,
`compare_named` (check.rs ~8557), and is reached only after plain
unification, dictionary search, effect coercion, row postponement,
helper awaiting, queue waiting and `along_match_equation` have all
failed; the next step is `compare_failed`, which errors unless an error
hole or `build::build` rescues it. Before, an unknown facing a forced
`Value::Lam` that wasn't a thunk set `against_lambda`, and the rule then
fired only if a data unknown also faced a known argument. Now a lambda
for which `eta_function` holds counts as a known argument instead, so
`Rel ?rel ?run` against `Rel (x y => SameNat x y) (() => 3)` behaves as
against `Rel SameNat (() => 3)`, which already fired on `main`.

`eta_contract` moved from walk/mod.rs verbatim (only the `Ev` path in the
signature differs); walk imports it back.

## 1. Soundness of the contraction

`λx. f x ≡ f` exactly when `x ∉ FV(f)` (and the binder's icit matches the
application's); for nested binders, `x y => f x y` contracts to `f` when
the inner step gives `y => f' y` with `y ∉ FV(f')`, and then `x ∉ FV(f)`.
`eta_contract` checks exactly this, binder by binder from the inside,
with `Term::mentions` (free occurrences only, including `Case`/`NumCase`
scrutinees), and requires `applied == icit`. Cases I traced:

| lambda | result | right? |
|---|---|---|
| `x y => f x y` | `f` | yes |
| `x y => f y x` | none (inner last arg is `x`; outer body is a lambda) | yes |
| `x y => f y` | none (outer body `f` is not an application of `x`) | yes, it is `x => f`, a lambda |
| `x y => h x x y` | none (`h x` mentions `x`) | yes |
| `f x => f x` | none (inner gives `f`, outer body is a variable) | yes, it is the identity |
| `{a} x => g {a} x` | `g` | yes, icits match per binder |
| `x => g ?m x` | `g ?m` | yes as eta; see risk 2 |

Dependent types: eta holds whatever the codomain (`(n: Nat) → Vec n`);
the domain annotation on the lambda is not compared with `f`'s domain,
but the lambda is well typed at the call's parameter type, so `f` is at
that type up to conversion. Implicit arguments: covered by the icit
check. Erased or proof arguments: `Term::Lam` carries no quantity, and
eta over a proof binder is a definitional equality like any other.

More importantly, **soundness doesn't rest on it.** `eta_function` is
only a gate: when it holds, `unify_solving_arguments(a, b)` compares the
unknown with the lambda itself and records `?rel := x y => SameNat x y`.
A wrong answer from `eta_function` can only open the rule where it
shouldn't (or keep it shut), and anything it then solves is a genuine
solution of `found ≡ expected`, which the kernel re-checks from scratch
without needing eta.

One inconsistency, not a soundness issue (F1 below): the caller
classifies a known argument with `force`, which unfolds a glued
`Value::Call`, while `eta_function` uses `force_solved`, which keeps it,
and `is_some_and(|f| !Term::Lam)` looks at the contracted *term*. So
`x y => Flip r x y`, with `def Flip (r) := x y => r y x`, contracts to
`Flip r`, a term that isn't a lambda, and counts as known; but `Flip r`
written bare forces to a lambda and still counts as "against a lambda".
The stated aim, "behaves as the function written bare", fails in that
direction for definitions whose arity is below the lambda's depth.

## 2. Determinism and wrong-but-well-typed solutions

Deterministic: no iteration order reaches a decision (`whole` is a
`HashSet` used only for membership), and `eta_function` is a pure
function of the value and level.

Could a well-typed program now get a different, still well-typed,
solution that the kernel accepts? Only at comparisons that failed on
`main`, since the rule runs after every other route has failed. Three
ways that could still matter:

- **Inside a speculative transaction.** If a `compare` that failed on
  `main` sat inside a transaction whose caller then tried another route,
  the new rule can now succeed first and commit a different elaboration
  (a hash change), or one that fails later (see 3). The lane's quarter
  sample of hash snapshots showed no movement; the full snapshot set and
  std pins at the verifier, and Overmind's AoC check, are the right net.
- **Non-injective relations.** If `Rel` ignores its `rel` argument,
  `?rel := (x y => SameNat x y)` is one of many solutions. This is the
  rule's existing lossy nature (`note_lossy`, `solved_lossily`), not new:
  bare `SameNat` already chose the same way. The change makes the
  eta-expanded spelling behave as the bare one, no worse.
- **Risk 2, `x => g ?m x`.** Counted as known; `?rel` is solved to a
  lambda that still holds the unsolved `?m`. The `only_whole` check
  ensures `?m` itself isn't solved by this rule (else everything is
  undone), and `?m` stays open for later constraints. Bare `g ?m` already
  behaved this way on `main`. Acceptable; a follow-up could refuse a
  contracted function that mentions an unsolved unknown, if one ever
  bites (F3).

## 3. D3688: can anything that checks on `main` stop checking?

The new branch only turns some `Ok(false)` results into a solve attempt,
and a failed attempt is undone exactly as before (`undo_since` plus the
`undo::transaction` wrapper). So through the success/failure channel,
nothing that checked can stop checking, except via a speculative caller
as above, where the rule's solution is a genuine solution and the
risk is small.

**The error channel is new (M1).** `eta_function` calls
`crate::check::quote_folded`, which on a value too large for both the
folded read-back (2,000,000 nodes, `FOLDED_NODES`) and the as-written
fallback returns `Err(ResourceError::Size)`. The `?` takes it out of
`unify_by_unknown_arguments` into `undo::unify_by_unknown_arguments`, where
it becomes an `E-RESOURCE` diagnostic, which `undo::fatal` treats as
"elaboration must stop", not "this way didn't work". On `main` the same
comparison returned `Ok(false)` and went on to `compare_failed`, whose
`build::build` path can still succeed, and whose mismatch error an outer
transaction can catch and recover from. So a program can in principle go
from checking to a fatal resource error. It needs a lambda whose body
ends by applying something to its innermost variable and reads back to
millions of nodes, so it is very unlikely, but it is a strict narrowing
and costs a few lines to close. The closure application and forcing in
the cheap check also spend steps from the shared budget; step exhaustion
is sticky and would equally be hit by `unify_solving_arguments` straight
after, so that part is not a new failure.

## 4. Cost

Only reached on a comparison that has already failed every other way,
and only for a non-thunk lambda facing an unknown. The cheap check
applies each closure to a fresh variable and forces the result (one
evaluation of the body to weak head, glued calls kept folded), then looks
at the last spine element. The read-back runs only when the body ends in
the innermost variable, and is capped. No measurable cost expected; no
hot path touched. Nit: the check runs even when `data_against_known`
would fire the rule anyway; not worth restructuring.

## 5. Tests

One accept example, `examples/accept/unify-eta-lambda-argument.sw`, with
the bare and expanded forms side by side: good, it pins the user-visible
behaviour and the hash. Thin for a unifier change. Before merge, nothing
further is required beyond M1's test; follow-ups worth adding (F2): a
Rust unit test of `eta_function` on the table in §1 (cheap and pins the
boundary: `x y => f y x`, `x y => f y`, `f x => f x`, `x => ?f x` false;
`x y => f x y`, `{a} x => g {a} x` true), and an accept example with an
implicit binder and one with a dependent codomain.

## Must fix before merge

- **M1. Size error from the read-back must not be fatal.** In
  `eta_function`, treat `Err(ResourceError::Size(_))` from `quote_folded`
  while `budget.exhausted()` is none as `Ok(false)`, restoring the
  budget's too-large and ran-out-in notes as `quote_folded`'s own
  fallback does (or as `undo::recoverable`/`recovered` do), so the
  comparison falls through to `compare_failed` exactly as on `main`.
  Other resource errors (steps, stack, time) stay errors. A test is
  impractical (it needs a 2M-node lambda); say so in the commit, per
  D3608's "name why" spirit.

## Follow-ups (file as tickets)

- **F1.** Make "known function" agree with the bare classification:
  evaluate the contracted term and require that `force` of it is not a
  `Value::Lam`, so `x y => Flip r x y` behaves as bare `Flip r` does.
  Low risk either way; the rule is last-resort and guarded.
- **F2.** Unit test of `eta_function` over the cases in §1, plus accept
  examples with an implicit binder and a dependent codomain.
- **F3.** Optional: refuse a contracted function that mentions an
  unsolved unknown (`x => g ?m x`), if a case ever shows the eager
  `?rel := x => g ?m x` choosing badly. No evidence it does today.
- **F4.** Nit: in `eta_function`, test `depth == 0` before computing
  `level + depth - 1`. It can't underflow today (a `Var` head implies
  `level ≥ 1`), but the order reads as if it could.
- **F5.** SW-4425's walk-side `eta_contracted` (walk/mod.rs ~536): its
  doc says it exists because of exactly the limitation this lane lifts.
  Check that its walk cases now pass without it, then remove it, in its
  own lane (it also rebuilds the goal and converts, so confirm nothing
  else depends on that).
- **Verifier note for the orchestrator:** run the full hash-stability
  snapshot set and std pins on the batch (the lane sampled a quarter),
  since the change can alter elaboration under a speculative caller.
