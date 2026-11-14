# SW-2847: review of `sort_of_applied_variable`

Paper review (D3473) of commit `1ac6babbd` on `lane/SW-2847`, which adds a
fast path to `sort_of` in `crates/core/src/check.rs`. Read from the source
only: nothing was built or run. Line numbers are in that commit's
`check.rs` unless another file is named.

## Verdict

**SOUND.** No must-fix. Whenever the new path answers, the old path either
gives the same sort or gives an error (it never gives a different sort),
and every shape the new path can't handle reaches the old path unchanged.

Two things to do, neither blocking:

1. The commit has no test. Add a small kernel test of the cases below
   (section "A test worth adding").
2. State the precondition in the doc comment: the value is well typed in
   `cx` (section "Where the two paths differ").

## What the change does

For `ty = Neutral(Var(level), spine)` (633), the helper (647-663) takes
`cx.types[level]`, forces it, and for each spine entry requires an
application against a `Pi`, applies the codomain closure to the argument
value, and forces the result. If what is left is `Sort s` it returns `s`;
anything else returns `None` and `sort_of` continues to `quote_kept` +
`check_type` (640-641) as before.

The old path on the same value: `quote_kept` gives `Var(ix) a1 .. an`;
`infer` on `Var` returns `cx.types[level - 1 - ix]`, the same entry
(244-246); `infer` on `App` forces the function's type to a `Pi`, checks
the argument against the domain, evaluates it, and applies the codomain
(321-334); `check_type` forces the result and requires `Sort s` (585-595).
So the new path is the old one with the read-back, the argument check and
the argument's re-evaluation left out.

## The cases asked about

| Case | Verdict | Why |
|---|---|---|
| Codomain depends on the argument | SOUND | The codomain closure is applied to the real argument value (656), not a placeholder. With `q : (T : Type 1) -> T`, `q Prop` gives `Sort Prop` and `q (Type 0)` gives `Sort (Type 0)`, as `infer` would. If the result is stuck on the argument (`q T` with `T` a variable), it isn't a `Sort`, so `None` and the old path decides. |
| Universe levels, `Sort` vs `Prop` | SOUND | The helper returns the `s` of the forced `Sort s` (660), which is what `check_type` returns (587-588). No level arithmetic happens here. The existing arm for `ty` itself being a sort (621, `universe_above`) is untouched and comes first. |
| Variable's type is a `let`, a glued call, or needs unfolding | SOUND | `cx.types` holds values, already evaluated when bound (`bind` 87, `define` 105). `force` (`value.rs` 835) unfolds a glued call or solved metavariable at the head before each shape test (651, 657), the same call `infer` makes at 323 and `check_type` at 587. An unsolved metavariable or other stuck type is neither `Pi` nor `Sort`: `None`. |
| Partially applied variable | SOUND | The loop ends with a `Pi`, not a `Sort`: `None`, and the old path reports `E-NOT-A-TYPE` as before. |
| More arguments than Pis | SOUND | The `let ... else` at 653 fails on the first argument with no `Pi`: `None`, old path reports `E-NOT-A-FUNCTION`. |
| Spine entry that isn't an application (`J`, `Proj`) | SOUND | Same `let ... else`: `None`. `Elim` has only `App`, `J` and `Proj` (`value.rs` 487). |
| Bare variable (empty spine) | SOUND | Returns the sort its type forces to, equal to `infer` on `Var` followed by `check_type`. |
| Level outside the context | SOUND | `cx.types.get(level)` is `None` (648): fallback. |
| Argument order | SOUND | `Spine` stores eliminations "in order" (`value.rs` 499) and `iter` walks them first-applied first, matching the Pis from the outside in. |
| Inside a case branch (refined context) | SOUND | See below. |

### Refined contexts

In a case branch `cx.env[x]` is the constructor and index unification may
have refined other entries. The old path re-evaluates the quoted arguments
in that refined environment; the new path uses the argument values as they
stand, which may still mention the unrefined variable. The two argument
values differ only by the refinement's substitution, and reduction is
stable under substitution: if the type applied to the unrefined arguments
already forces to `Sort s`, the type applied to the refined ones forces to
the same `Sort s`. If it is stuck on the unrefined argument the new path
returns `None`. Both paths read the head's type from the same `cx.types`
entry, refined or not. So the answers agree here too.

## Where the two paths differ

Only in errors, and only in one direction: the new path can return a sort
where the old one returned `Err`.

- **Budget.** The old path could run out of budget or memory reading back
  the argument; that is the point of the change.
- **Ill-typed arguments.** The old path checked each argument against the
  Pi's domain (325) and that the application's implicitness matched the
  Pi's (324). The new path does neither (653 ignores both `Icit`s). For a
  value that is well typed in `cx` these checks can't fail, and every
  caller passes one: a case's goal (1005), an evaluated checked parameter
  type (3046), or a domain or result of an already-checked type (4557,
  4562, 4567, `inert.rs` 102, `reference.rs` 1313). So this is the same
  trust the `Eq` and `Data` arms above it already place in the value
  (624, 628): neither looks at its arguments at all.

The doc comment on `sort_of` should say that `ty` must be a well-typed type
in `cx`, since three of its arms now rely on it.

The new path propagates an error from `force` or `apply` (651, 656, 657)
instead of falling back. That is the conservative choice: the old path
does the same applications and would hit the same limit.

## Who calls `sort_of`

One caller is the kernel's own checking; the rest decide erasure.

- **`check_case`, 1005 (kernel rule).** A match on a proof may produce
  data only for a subsingleton proposition; `sort_of(goal) != Prop` is the
  test. A wrong `Prop` here would let any proposition eliminate into data,
  which is unsound (with proof irrelevance, `True ∨ True` would decide
  `0 = 1`). So this arm is kernel code and deserves this review. The goal
  `q (settle x k 3000)` with `q : Nat -> Prop` now answers `Prop` from
  `q`'s type; with `q : Nat -> Type` it answers `Type 0` and the rule
  applies as before. Since the answer equals the old path's whenever the
  old path answered, the rule accepts the same programs, plus those that
  used to run out of budget and are correctly typed.
- **`check_let_value`** doesn't call it (it uses `check_type`'s sort).
- **Erasure:** `proof_params` (3046), `telescope` via `is_erased` (4539,
  4548, 4567), `proof_telescope` (4557, 4562), `inert.rs` 102,
  `reference.rs` 1313 (`not_a_proof`, the validator for inert marks). A
  wrong `Prop` would erase data that runs; a wrong non-`Prop` would only
  keep a proof. Same answer as before, so neither happens. All of these
  build their context with `cx.bind` at the level they pass to
  `Value::var`, so `cx.types[level]` is the head variable's type.

## Other notes

- `docs/core.md` needs no change: it doesn't describe how the sort of a
  type is computed, and what the kernel accepts is unchanged apart from
  budget.
- The "Read-backs that keep calls" comment (2074-2090) still holds; the
  new arm is one more shape answered before the read-back.
- The same idea would cover `Head::Def` (a stuck definition applied to a
  huge argument, sort read off `def_type`) and a `Value::Call`. Not needed
  for SW-2847's example; worth a ticket only if a profile shows it.
- Cost: one closure application and a `force` per argument, and the
  variable's type is cloned once (651). The old path did the same
  applications plus the read-back and check, so this is never slower.

## A test worth adding

A kernel unit test calling `sort_of` on hand-built values, in a context
where the old path would also answer, asserting the sort:

- `q : Nat -> Prop`, `q n`: `Prop`. `r : Nat -> Type`, `r n`: `Type 0`.
- `q : (T : Type 1) -> T`: `q Prop` is `Prop`, `q (Type 0)` is `Type 0`
  (the codomain depends on the argument, and the sort with it).
- `f : Nat -> Nat -> Prop`, `f n`: an error (partial application), and
  `q n m` with `q : Nat -> Prop`: an error (too many arguments), both from
  the old path.
- An `E-PROP-ELIM` example whose goal is `r (big)` with `r : Nat -> Type`:
  matching on a proof of an `Or` must still be refused.
