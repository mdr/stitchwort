# Effect-polymorphic `List.map` (SW-369, D1050 experiment)

Status: experiment done, **not kept**. The std change was reverted; this report is the only change.

## What was tried

In `crates/elab/src/std/List/Toolkit.sw` the pure

    def List.map (f: a -> b): List a -> List b

was replaced by the body of `List.mapIn`:

    def List.map (f: a -> {e} b): List a -> {e} List b
      | Nil => Nil
      | Cons x xs => Cons (f x) (List.map f xs)

(with `mapIn` deleted), then the CLI was rebuilt and `cargo test --release -p stitchwort-driver --test std_library` run.

## What broke

The standard library no longer loads: `std/List/Toolkit.sw` fails to check
(`E-INTERNAL: the library file std/List/Toolkit.sw doesn't check`), so 9 of 30
`std_library` tests fail (the library-test run, the index and lazy-loading
tests, and so on), and nothing after that file was reached. `hash_stability`,
`examples`, `run_js`, `run_reference`, `fmt_repo` and the AoC check were not
run: they all load the standard library and would fail the same way.

All 32 errors in `Toolkit.sw` are one error, `E-TYPE-MISMATCH`. Examples:

    std/List/Toolkit.sw:251:75   theorem List.lengthMap (f: a -> b) ...
      expected `a -> {?3 a b f xs} ?4 a b f xs`, but this has type `a -> b`
    std/List/Toolkit.sw:235:91   List.map (List.drop 1) rows
      expected `List (?3 ..) -> {?1 ..} ?2 ..`, but this has type `List (?3 ..) -> List (?3 ..)`
    std/List/Toolkit.sw:992:58   List.Distinct (List.map Succ [1, 2])
      expected `{?1} ?2`, but this has type `Nat`
    std/List/Toolkit.sw:1164:81  List.concat (List.map f xs)
      expected `a -> {?1 ..} ?2 ..`, but this has type `a -> List b`

Every site where the callback is not a literal lambda fails: a variable
(`f`), a partial application (`List.drop 1`, `cell x`), or a constructor
(`Succ`). Roughly 30 sites in `Toolkit.sw`, mostly theorem statements
(`lengthMap`, `mapMap`, `mapAppend`, `takeMap`, `memMap`, `mapCong`,
`mapReverseOnto`, `distinctMap`, ...), plus `flatMap` (1164), `transposeN`
(235) and the transpose lemmas (761, 774). The repository has about 245 `map`
uses in std and 244 in AoC and examples, so many more sites were likely hiding
behind this file.

## Cause

A function type `a -> b` is a plain Pi type, while `a -> {e} b` is
`a -> Comp (ops of e) (results of e) b` (`crates/elab/src/effects.rs`
header). Applying an effect-polymorphic function to a pure function value has
to solve the row variable `e` to the empty row and the result meta to `b`, but
unification of `Comp (ops ?e) (res ?e) ?b` against a rigid `b` does not do
that. This is the situation of SW-223 (effect-polymorphic calls don't pass the
expected type to their arguments), and it is broader than that ticket: the
elaborator needs "if the expected parameter type is a `Comp` over a row meta
and the argument is not computation-shaped, close the row".

Evidence that this is not caused by the `map` change but is already true of
today's `List.mapIn` (checked on unmodified `main` with scratch files
`/tmp/claude-501/t/b.sw` and `c.sw`):

    mapIn (x => x + 1) xs        accepted (lambda: elaborated against the Comp type)
    mapIn f xs                   E-TYPE-MISMATCH expected `Nat -> {?1 f xs} ?2 f xs`, has `Nat -> Nat`
    mapIn (List.drop 1) xs       E-TYPE-MISMATCH (same shape)
    mapIn Succ xs                E-TYPE-MISMATCH expected `{?1 xs} ?2 xs`, has `Nat`
    f: Nat -> {} Nat; mapIn f xs E-TYPE-MISMATCH (even with an explicit empty row)
    theorem about mapIn f        E-TYPE-MISMATCH (cannot even be stated with a pure `f`)

So `mapIn` works today only for lambdas and genuinely effectful functions
(`Range.read`, `Text.toNatOrFail`).

## Not measured

Because the library does not load, these could not be examined: whether the
`map_*` lemmas still reduce at the empty row, JS codegen and performance
changes (a `Comp` over a closed `NoOp` row may or may not erase), and hash
moves. The D1055 decision (a call whose ability row is empty after
instantiation is a plain value) is the likely mechanism for the first; it was
not tried here.

## Decision taken

Not clean: the failures are one elaborator limitation, not mechanical fixes.
Wrapping each pure callback in a lambda (`(x => f x)`) would touch about 30
theorem statements, make them read worse, and still leave open whether the
proofs reduce. Per the brief, the std change was reverted (`mapIn` stays,
`map` stays pure) and only this report is committed.

## Follow-ups

- Elaborator: when a parameter's type is `A -> Comp ops res B` with a row meta
  and the argument has the pure type `A -> B'` (or is a constructor or partial
  application), solve the row to the empty row (D1055 territory) and
  `B := B'`. This is SW-223 widened; it removes the need for a separate
  `mapIn`.
- After that, redo this experiment. The fold of `mapIn` into `map` is the
  one-hunk edit above plus the callers (`Fail.sw` tests,
  `aoc/src/Aoc/Common/Lines.sw`, `Day02.sw`, `Day03.sw`,
  `examples/accept/fail*.sw`, `examples/extract/results.sw`,
  `docs/syntax.md:634`, `docs/proposals/errors.md`).

## Decision for Matt (for the morning)

Should `List.map` become effect-polymorphic?

1. Keep `map` pure and `mapIn` separate (current state). No work; two names.
2. Fix the elaborator first (close the row for pure arguments, SW-223
   widened), then redo this experiment and fold `mapIn` into `map`. Real
   elaborator work plus a re-check of all `map_*` lemmas.
3. Fold now by wrapping pure callbacks in lambdas. Not recommended: churn in
   about 30 lemma statements, worse reading, proofs unverified.

Recommendation: 2. `mapIn` already cannot take a pure variable or a
constructor, which is a bug in its own right, and the fix is needed for any
effect-polymorphic list function.
