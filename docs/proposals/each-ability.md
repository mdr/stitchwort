# `Each`: list comprehensions as an ability

**Status:** as built, 22 October 2026 (SW-296, D528). A prototype: `Std.Each` (`crates/elab/src/std/Each/Each.sw`) and AoC day 2's `allTemplatesForRange` written with it. User documentation is in [docs/syntax.md](../syntax.md#each).

## What

A computation that performs `Each` may pick an element of a list (`each`) and drop the current choice (`require`). The handler `collect` runs the rest of the computation once per element and joins the results in order. It's the list monad written in direct style:

```
def allTemplatesForRange (range: Range): List RepetitionTemplate := Each.collect (() =>
  let maxDigits := (Nat.digits range.to).length
  let blockLength := each (List.between 1 maxDigits)
  let copies := each (List.between 2 maxDigits)
  require (blockLength * copies <= maxDigits)
  { blockLength, copies })
```

This is the day 2 target, character for character; nothing in the surface had to change. The imports are `import Std (Each)` and `import Std.Each (each, require)`. The thunk is `() =>` with a block body in brackets, as `Abort.orElse` takes it.

## Surface

| Name | Type | |
|---|---|---|
| `Each.each` | `List a -> {Each} a` | each element in turn; `[]` ends this choice |
| `Each.require` | `Bool -> {Each} ()` | ends this choice unless `True` |
| `Each.collect` | `(() -> {Each} a) -> List a` | every result, the first choice varying slowest |
| `Each.collectIn` | `(() -> {Each \| e} a) -> {e} List a` | the same, with other abilities passing through |
| `Each.fork` | `() -> {Each} Bool` | operation: resumed with `True`, then `False` |
| `Each.stop` | `() -> {Each} Empty` | operation: never resumed |

**Why two operations, not an `each` operation.** An operation can't be polymorphic: its type would have to be stored in the operation, which raises universe questions, so they're excluded ([abilities.md](abilities.md), "Polymorphic operations"). `fork` and `stop` are the classic nondeterminism pair (Koka's and Eff's `flip`/`choose` and `fail`), and `each` is an ordinary recursive function over them: `each [x, ..xs]` is `if fork() then x else each xs`. `require` is `stop` unless `ok`, so it isn't an operation either. An `Each a` ability with a type parameter would allow an `each` operation, but a row holds one instance of each ability, so one computation couldn't choose from a `List Nat` and a `List Text`.

**Why two handlers.** `collectIn` is the general one. But at the empty row its result is a `Comp NoOp NoRes (List a)`, and its clause `List.append (k True) (k False)` is two `bind`s. In a pure function that's run with `runPure`, and `runPure (bind c f)` doesn't reduce for an unknown `c`, so the `flatMap` lemma's induction step doesn't compute. Stating the missing lemma (`runPure (bind c f) = runPure (f (runPure c))`) isn't possible either: naming a `Comp NoOp NoRes a` in source runs it (syntax.md, "Abilities"), so `c` can't be mentioned as a computation. So `collect` is written out separately for the closed row, with the clause `Each.both (b => k b)`, where `both` is a pure function: there `k b` is a plain value, and the clause is `Done` of a pure expression. Its lemmas then compute.

## Lemmas

Stated over `collect`, with the continuation as a variable, so proofs needn't know about trees:

| Lemma | Statement | Proof |
|---|---|---|
| `Each.collectPure v` | `collect (() => v) = [v]` | `rfl` |
| `Each.collectEach k xs` | `collect (() => k (each xs)) = xs.flatMap (x => collect (() => k x))` | induction on `xs`, one `Eq.cong` per step; each step is `rfl` by computation |
| `Each.collectRequire k ok` | `collect (() => (require ok; k())) = if ok then collect k else []` | `rfl` on each case of `ok` |
| `Each.collectEachSelf xs` | `collect (() => each xs) = xs` | induction |

They're applied by giving the continuation explicitly (`Each.collectEach withCopies (List.between 1 size)`), and conversion checks it against the program. Day 2 needed one more fact, local to it: `sumBy f (if b then [t] else []) = if b then f t else 0`.

There are no lemmas over `collectIn` at an open row: an equation between two `{e}` computations would be an equation between trees, and isn't needed yet.

**A quirk found on the way.** In a proof term, `Each.collect (() => k x)` as an argument to `Eq.cong` left a metavariable for the thunk's body (`?4 a b k x xs ()`), while `Each.collect (u => k x)` checks. The proofs use `u =>`. Not investigated further.

## Day 2

`templatesSum` (aoc/src/Aoc/Day02/Proofs/Repeated.sw) keeps its statement, so Part1.sw and Part2.sw are unchanged. The proof is now: `collectEach` for the block length, `List.sumByFlatMap`, then for each block length `collectEach` for the copies, `List.sumByFlatMap`, and for each template `collectRequire` and the one-template fact; finally `between` becomes `rangeFrom`. The tight-bounds version needed the arithmetic of `size / k` (eight helper theorems: `predLe`, `copiesLe`, `copiesGt`, `copiesNo`, `blockTooLong`, `copiesRun`, `copiesRow`, `rowOfBlock`); the loose bounds and `require` state the fit directly, as the grid in the statement does, so none are needed. Repeated.sw went from 506 to 428 lines: templatesSum and its helpers from 120 lines to 42.

The answers are unchanged: Part 1 16793817782, Part 2 27469417404.

## Costs

Run time of `Aoc.Day02.main`, wall-clock seconds, release build, median of 3. The real input is 28 ranges and runs in about the CLI's start-up time, so the input repeated 300 times (8,400 ranges) is shown as well. The "flatMap, loose bounds" row is a control: the same loose bounds and test, written with `List.flatMap` and `if`, so the difference between it and `Each` is the ability's own overhead.

| `allTemplatesForRange` | rt, real | JS, real | rt, ×300 | JS, ×300 |
|---|---|---|---|---|
| before: tight bounds, `flatMap` | 0.12 | 0.23 | 0.42 | 0.35 |
| control: loose bounds, `flatMap` | | | 0.56 | 0.40 |
| `Each` | 0.13 | 0.23 | 1.55 | 0.64 |

So on the real input nothing is visible, and on a 300 times larger one `Each` costs about 2.8× on `stitchwort run` and 1.6× on JS over the same enumeration with `flatMap`. The overhead is the tree: each element is a `fork` node, each `bind` rebuilds the continuation, and the handler dispatches through the row's `Plus`. Checking and `stitchwort test` (the kernel's evaluator, including the real-input tests) didn't change measurably: 5.2 s for Day 2's tests and 5.8 s for its proofs, before and after.

Things that would make it cheaper, not done: an index operation (`pick: Nat -> {Each} Nat`, resumed once per index) would make `each` one operation instead of a `fork` per element, at the price of indexing the list and harder lemmas; a runtime that runs handlers natively instead of building trees ([abilities.md](abilities.md), option A) would remove the tree altogether.

## Comparison

- **Scala `for`/`yield`.** `for (b <- 1 to m; c <- 2 to m if b * c <= m) yield (b, c)` is sugar for `flatMap`, `withFilter` and `map`. The guard is `require`. Scala needs the syntax because it has no direct style for monads; `Each` gets the same reading from the ability.
- **Haskell's list monad.** `do { b <- [1..m]; c <- [2..m]; guard (b * c <= m); return (b, c) }`, or the list comprehension `[(b, c) | b <- [1..m], c <- [2..m], b * c <= m]`. `each` is `<-` on a list and `require` is `guard`. The `collectEach` lemma is the monad's bind law for lists.
- **Koka and Eff.** Nondeterminism is the standard example of a multi-shot handler: an operation like `flip: () -> bool` (Koka) or `choose` (Eff), resumed twice, with `fail` not resumed, and a handler collecting a list. `Each` is that, plus `each` over a list. Stitchwort's handlers are folds over a finite tree, so resuming twice needs nothing special and termination is the kernel's ordinary structural check.
- **Unison.** Abilities with multi-shot continuations, and per its documentation a `Stream` ability with `emit` in its base library. Whether its base library has an `Each`-like ability for choosing from a list is unverified here.

## Not done

- The JS backend fails on a top-level constant (a definition with no parameters) whose body is lifted into a helper, as a handler with an `if` is: `ReferenceError: Cannot access '$Main$dhalves$d$gmatch1' before initialization`. It happens with `Abort` alone (`def halves: Option Nat := Abort.toOption (() => …)`), so it isn't `Each`'s; `stitchwort run` is fine. Written as a function (`def halves(): …`) it works.
- No lemmas for `collectIn` at an open row, and no `Each` with `State` in the std tests (only `Abort`, both orders).
