# Effect-polymorphic `List.map` (SW-369, D1050 experiment)

Status: two experiments done, both **not kept** (the second, after SW-393, is at the end). The std changes were reverted; this report is the only change.

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

### Update: fixed by SW-393

A pure function is now accepted where an effectful one is expected. In
`compare` (`crates/elab/src/check.rs`), `effects::coerce` wraps a function
whose result type is not a `Comp` as `x … => Done (f x …)`, which fits any
row, exactly as a lambda with a pure body is elaborated. The row is not
solved there: like a lambda's, it is left to the call's context (so
`List.mapIn f xs` is a plain value where a `List b` is expected). A
constructor checked against such a function type goes through the same
path. All five calls in the table above now check
(`examples/accept/effect-poly-pure-callback.sw`). A theorem
`List.mapIn f xs = List.map f xs` can now be stated, but its `Cons` case
doesn't follow by `Eq.cong` alone: the left side is
`runPure (bind (mapIn …) …)`, which needs a lemma to reduce. SW-223 (the
`orElse 0` case) is a separate mechanism and is unchanged.

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

## Second attempt (after SW-393)

Status: done, **not kept** again. The std change was reverted; this section
is the only change. The callback problem is gone, but two new blockers
appeared, and each meets a stop condition in the brief.

### What was done

On `main` at `538d269d` (SW-393 merged), `List.map` in
`crates/elab/src/std/List/Toolkit.sw` got `mapIn`'s signature and body
(`(f: a -> {e} b): List a -> {e} List b`), `mapIn` was deleted, and every
caller was renamed (`Fail.sw` tests, AoC `Lines.sw`, `Day02.sw`,
`Day03.sw`, `examples/accept/fail.sw`, `main-fail.sw`, `main-fail-ok.sw`,
`effect-poly-pure-callback.sw`, `examples/extract/results.sw`). Then the
release CLI was rebuilt and a file was checked. Loading the library
failed, so none of the named test binaries were run: they all load the
library.

### What broke: the proofs

The callbacks now check (SW-393 works). What fails is the proofs. The
library doesn't load (`E-INTERNAL: the library file std/List/Toolkit.sw
doesn't check`), with 33 errors in `Toolkit.sw` alone (19
`E-TYPE-MISMATCH`, 10 `E-REWRITE-NOTHING`, 2 `E-UNIVERSE`, one each
`E-CALC-STEP` and `E-REFL`). They are at lines 250, 260, 286, 336, 348, 355,
363, 370, 724–791, 852–872, 925–974 and 1204–1241: `lengthMap`, the
transpose lemmas, `allMap`, the `map` composition, append and take lemmas,
`distinctMap`, `flatMap`. Nothing after `Toolkit.sw` was reached. About 58
std theorems mention `map`, and 26 AoC files mention it.

They all have the same cause. The first one:

    std/List/Toolkit.sw:250:18  | Cons x xs => Eq.cong Succ (List.lengthMap f xs)
      expected `List.length (Effect.runPure (Effect.bind (List.map (_ => Done (f _)) xs) (%8 => Done (Cons (f x) %8)))) = Succ (List.length xs)`,
      but this has type `Succ (List.length (Effect.runPure (List.map (_ => Done (f _)) xs))) = Succ (List.length xs)`

`map`'s body is elaborated once, for any row `e`, so its `Cons` case is
`bind (f x) (y => bind (map f xs) (ys => Done (Cons y ys)))`. With a pure
callback, `f x` becomes `Done (f x)` and the first `bind` reduces. The second
one doesn't: it waits on `map f xs`, which is stuck on the variable `xs`. The
D1055 "run in place at the empty row" rule doesn't help here, because it
acts where a call is elaborated, not inside `map`'s body.

### Why a few supporting lemmas aren't enough

The obvious fix is one bridging lemma, `runPure (map f xs) = <pure map> f
xs`, after which every old lemma follows by rewriting. Its `Cons` case needs
`runPure (bind c k) = runPure (k (runPure c))` over the empty signature. That
is true, since `NoOp` has no operations, but the source language can't state
it or prove it. Checked on unmodified `main`, where `mapIn` has exactly the
body the folded `map` would have:

    theorem mapInPure (f: a -> b): (xs: List a) -> List.mapIn f xs = List.map f xs
      | Nil => rfl
      | Cons x xs => Eq.cong (Cons (f x)) (mapInPure f xs)
    -- E-TYPE-MISMATCH: expected `Effect.runPure (Effect.bind (List.mapIn (_ => Done (f _)) xs) (%8 => Done (Cons (f x) %8))) = ...`,
    --                  but this has type `Cons (f x) (Effect.runPure (List.mapIn (_ => Done (f _)) xs)) = ...`

    theorem runPureBind: (c: Effect.Comp Effect.NoOp Effect.NoRes a) -> (k: ...) ->
        Effect.runPure (Effect.bind c k) = Effect.runPure (k (Effect.runPure c))
    -- E-TYPE-MISMATCH at `c`: expected `Comp ?0 ?1 ?2`, but this has type `a`
    -- (a `Comp` value written in source is sequenced, not passed)

This is the gap errors.md §5 already records for `Fail.toResultMapIn`: "no
proof can take apart a computation". So the fold needs language work, not
mechanical fixes.

### JS for a pure `map`

`stitchwort build --js`, release CLI on `main`, for
`export def doubledAll (numbers: List Nat): List Nat := List.map double
numbers` and the same with `mapIn`. The folded `map` would have `mapIn`'s
body, so the `mapIn` output is what every pure `map` call would compile to
(the folded library didn't load, so it couldn't be built directly):

    // today's pure map: a loop that fills in the list's tail (tail recursion modulo cons)
    const $Main$ddoubledAll = (v0) => $Std$dList$dmap($Main$ddouble)(v0);
    const $Std$dList$dmap = (v2) => (v3) => { ... for (;;) { ... continue; } };

    // mapIn with a pure callback: the shape every pure map call would get
    const $Main$ddoubledAllIn = (v0) => $Std$dEffect$drunPure($Std$dList$dmapIn({ tag: "MkSig" })(((v1) => ({ tag: "Done", value: $Main$ddouble(v1) })))(v0));
    const $Std$dList$dmapIn = (v1) => (v3) => (v4) => { ...
      return $Std$dEffect$dbind((v3)(v5))(((v7) => $Std$dEffect$dbind($Std$dList$dmapIn(v1)(v3)(v6))(((v8) => ({ tag: "Done", ... })))));

This is the computation-tree shape: a `Done` box per element, two `bind`s per
element, and recursion that isn't in tail position. Measured with Node
22.23.3, on lists of `n` naturals:

| n | pure `map` | `mapIn` with a pure callback |
|---|---|---|
| 1,000 | 0.3 ms | 3.1 ms |
| 10,000 | 3.6 ms | stack overflow (`StitchwortResourceError`) |
| 100,000 | 81 ms | stack overflow |
| 1,000,000 | 692 ms | stack overflow |

So the JS fails the brief's other stop condition as well: pure `map` would
become the effect-handler shape, and it would also fail on lists over about
10,000 elements.

### Decision taken

Stopped and reverted per the brief: `map` stays pure and `mapIn` stays.
Nothing in the language today keeps the pure behaviour definitional. There
is no pure fast path, no `implemented_by`-style attribute, and no
specialisation at the empty row in the JS backend. And the one bridging
lemma that would make the proofs mechanical can't be stated.

### What would make the fold clean

Two pieces, both language work (they would go through the design review gate):

1. **Proofs.** The kernel or evaluator reduces `runPure (bind c k)` to
   `runPure (k (runPure c))` when the signature is `NoOp`. This is sound for
   the same reason as D1055 (`runPure`'s `Call` case is absurd). With it,
   `runPure (map (x => Done (f x)) xs)` computes the way the pure `map`
   does, and the existing lemmas should go through unchanged, as stated. That is
   likely, not checked. The other route is a surface way to state and prove
   lemmas over `Comp` (which `Fail.toResultMapIn` also needs), plus a
   bridging lemma and a rewrite in each of the ~60 affected proofs.
2. **Codegen.** The JS (and rt) backend compiles a row-polymorphic
   definition used at the empty row as a pure copy: `Done v` becomes `v`,
   `bind c k` becomes `k c`, and `runPure` becomes the identity. After that,
   the existing tail-recursion-modulo-cons loop applies. Without this, the
   fold makes every pure `map` in an extracted program slower, and
   unsafe on long lists.

## Decision for Matt (for the morning, second attempt)

D1050 follow-up: folding `mapIn` into `map` isn't clean. What next?

1. **Keep `map` pure and `mapIn` separate** (the current state, which
   works for every callback since SW-393). No work.
2. **Language work first, then fold:** the `NoOp` reduction rule for
   proofs, and empty-row specialisation in the JS and rt backends, then a
   third attempt. Two design notes and two lanes, each a stage.
3. **Only the codegen half** (empty-row specialisation) now, because it
   also speeds up today's pure calls of `mapIn`, `Fail.toResult` and other
   handlers. Revisit the fold later.

Recommendation: 1 for now. The fold would buy one name instead of two. Its
cost is a kernel rule and a backend specialisation pass, and nothing else
needs those yet. Revisit (option 2) when a second effect-polymorphic list
function (`filter`, `foldLeft`) is actually wanted.
