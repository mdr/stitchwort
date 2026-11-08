# SW-2439 review: a let's lambda applied in a filled placeholder

Lane `lane/SW-2439`, first commit `5893f8d88`. An independent Opus review
recommended merging it after two fixes. It found the annotation's type and
context correct, and the terms well-typed.

## Findings, most important first

1. **Should-fix: the stripping reached more than the lane added.** The gate
   in `zonk_call` was syntactic: any `App` with an `Ann` head in the call.
   The elaborator makes such heads itself (`bind.rs`, `pipe.rs`, operation
   values and partially applied constructors in `check.rs`). Once the gate
   fired, every `(x : A) a` in the refolded term was stripped, including
   annotations the user wrote, and in lifted helpers' calls too, since they
   share `zonk_call`.
2. **Should-fix: the annotation's type was mapped with `applied`.** If the
   `let`'s type mentions a variable outside the placeholder's spine,
   `applied` raises `E-MALFORMED`, and `placeholder_call` returned `None`
   for a call it used to produce.
3. **Left for SW-2446 (filed by the orchestrator):** `match`es and `Proj`s
   of inlined `let` values; `refold` matching lambdas without looking at
   their types; a fold-back that is deterministic by slot; `lift.rs:1053`.

## Response

- **Finding 1, fixed.** `lifted_calls` now records, with each call, whether
  `placeholder_call` annotated a lambda in it. Helpers' calls and fills
  without such an annotation record `false`. Only flagged calls are
  stripped, and only of `(x : A) a` where `x` is a `let` variable of the
  `lets` that `refold` folds back to (`unify::unannotate_let_heads`).
  `examples/accept/postpone-let-lambda-annotated-use.sw` has a written
  `(double: Nat -> Nat) 3` in a waiting comparison, beside a lambda the fill
  annotates and a pipe. I dumped its kernel term to check: the written
  annotation stays, while the fill's annotation on `sizeAt` is dropped. A
  hash snapshot pins it. What is still possible: a written annotation on a
  `let` variable, in a call where the fill also annotated a lambda, is
  dropped. That changes the hash, not the meaning.
- **Finding 2, fixed.** The type is mapped with `variable`, which inlines
  the way the value's mapping does.
