# Proposal: one effect-polymorphic version of the other list functions

**Status:** plan for review, 25 Oct 2026. Nothing is built. Decisions
D1239–D1243 at the end.

It continues [effect-polymorphism.md](effect-polymorphism.md) (D1110: one
`List.map` that takes pure, effectful and partial callbacks, runs as fast as
the plain one when the callback is pure, and stays provable) and
[partial-stage-3.md](partial-stage-3.md) §7.1 and §10. It asks Matt to
revise one earlier decision: D1120 said "others one at a time, when a
program needs them".

How claims are marked:
- **[ran]**: run for this note with `target/release/stitchwort` built from
  `main` at `02374f46`, using `--std-dir` on edited copies of `std`, Node
  22, on a shared machine.
- **[source]**: read in the code at that commit.
- **[inferred]**: my reasoning, not tested.
- **[unverified]**: I couldn't find a source that I could open.

Claims about other languages link to a page that was opened for this note.

## 0. Summary

- **The machinery is already generic.** I changed nine functions' signatures
  to the `map` shape (`p: a -> {e} Bool` and result `{e} …`) in a scratch
  copy of std: `filter`, `foldLeft`, `foldRight`, `sumBy`, `count`, `any`,
  `all`, `find`, `filterMap`, `findMap`, `takeWhile`, `flatMap`. Every std
  file still checks, with no theorem touched, and so do all 39 AoC
  namespaces. The JS generated for pure uses is the same code as today
  (after renumbering variables). Partial callbacks work with no extra
  change **[ran]**, §5.
- **Three bodies need restructuring, for what they do with effects:**
  1. `filter` runs the callback's effects **last element first**. It needs
     a `let` to run them in order.
  2. `findMap` doesn't stop at the first `Some`. It needs a `match`.
  3. `partition` calls the predicate **twice** per element (two `filter`
     passes). It needs one pass.
- **Recommended semantics**, as in Koka, Effekt, Lean and Haskell's
  `extra`:
  - effects run left to right;
  - the callback is called at most once per element;
  - `any`/`all`/`find`/`findMap`/`takeWhile` stop at the first result that
    decides the answer.
- **What's name-specific:** only three diagnostic strings that say "so far
  only `List.map`'s callback may be partial", two reject examples, and one
  sentence in the guide. These are listed in §4.
- **The plan:** three lanes, each gated on unchanged theorems, identical
  pure JS, and a pure benchmark within 10% (§6).

## 1. What other languages do

| Language | One version or two? | Short-circuit (`any`, `find`) | Order | Laws or proofs |
|---|---|---|---|---|
| **Koka** | One. `filter(xs, pred: (a) -> e bool): e list<a>`, `foldl(…, f: (b, a) -> e b): e b`, `any(…, predicate: (a) -> e bool): e bool` ([std/core/list](https://koka-lang.github.io/koka/doc/std_core_list.html)). `div` doesn't appear in these signatures. | Yes, per [source](https://raw.githubusercontent.com/koka-lang/koka/master/lib/std/core/list.kk): `if predicate(x) then True else xx.any(predicate)` | Left to right in the source (`Cons(f(x), xx.map(f))`). No general statement in the docs. | None |
| **Unison** | One. `List.map : (a ->{𝕖} b) -> [a] ->{𝕖} [b]` ([docs](https://www.unison-lang.org/docs/fundamentals/values-and-functions/reading-type-signatures)), `Optional.filter : (a ->{g} Boolean) -> Optional a ->{g} Optional a` ([docs](https://www.unison-lang.org/docs/fundamentals/abilities/using-abilities-pt1/)). | **[unverified]**: Share pages render only in a browser, so I couldn't read `List.filter`/`any`. | **[unverified]** | None |
| **Flix** | One. `filter(f: a -> Bool \ ef, l: List[a]): List[a] \ ef`, `exists`, `foldLeft`, `find`, `partition` and `takeWhile` likewise ([api](https://api.flix.dev/List.html), [effect polymorphism](https://doc.flix.dev/effect-polymorphism.html)). | Not checked | Documented only for `foldLeft` ("going from left to right") | None |
| **Effekt** | One, with no effect variable at all: effects are capabilities, and the polymorphism is implicit ([paper](https://pl.cs.uni-tuebingen.de/publications/brachthaeuser20effects/)). `def any[A](list: List[A]) { predicate: A => Bool }: Bool` ([source](https://raw.githubusercontent.com/effekt-lang/effekt/master/libraries/common/list.effekt)) | Yes: `predicate(x) \|\| any(xs) { predicate }` | Left to right (built on `foreach`) | None |
| **OCaml 5** | One. Effects aren't in types, so the ordinary `List.filter` takes effectful callbacks (general knowledge; I found no page that says so). | `exists` "returns `(f a1) \|\| (f a2) \|\| …`" ([List](https://ocaml.org/manual/latest/api/List.html)) | Stated only for `iter` | None |
| **Haskell** | Two: `filter` and `filterM :: Applicative m => (a -> m Bool) -> [a] -> m [a]`; `foldM` "works from left-to-right" ([Control.Monad](https://hackage-content.haskell.org/package/base-4.22.0.0/docs/Control-Monad.html)). `anyM` "retains the short-circuiting behaviour" ([extra](https://hackage-content.haskell.org/package/extra-1.8.1/docs/Control-Monad-Extra.html)). | Yes (`anyM`) | Left to right | Monad laws only |
| **Lean 4** | Two: `any` and `anyM`, `filter` and `filterM`. `anyM` "short-circuits upon encountering the first `true`", and its elements are "examined in order from left to right" ([Control.lean](https://raw.githubusercontent.com/leanprover/lean4/master/src/Init/Data/List/Control.lean)). | Yes, documented | Left to right, documented | Lemmas link the two: `anyM_pure`, `mapM_pure`, `idRun_mapM` ([Monadic.lean](https://raw.githubusercontent.com/leanprover/lean4/master/src/Init/Data/List/Monadic.lean)) |
| **F\*** | Two: `FStar.List.Tot` (pure, used in specs) and `FStar.List` (`ML` effect) ([Tot](https://raw.githubusercontent.com/FStarLang/FStar/master/ulib/FStar.List.Tot.Base.fst), [ML](https://raw.githubusercontent.com/FStarLang/FStar/master/ulib/FStar.List.fst)) | `for_all` stops early (source) | | Proofs are about the `Tot` versions |

What this says:
- The languages with effect rows (Koka, Flix, Unison, Effekt) keep one
  version of each function.
- The languages with proofs (Lean, F\*) keep two, and in Lean, lemmas
  connect the two.
- Stitchwort's design is what makes one version possible with proofs: at
  the empty row `{e} b` *is* `b`, so the existing theorems are about the
  pure instance (effect-polymorphism.md §0).
- Every source I could read short-circuits and runs left to right. Only
  Lean writes this down in the docs.
- None of them has a proof about the effectful behaviour itself.

## 2. Which functions, in what order

Here is how often each name occurs, counted with the script
`grep -rhoE "\.name\b"` over `*.sw` **[ran]**. The count includes
`List.name`, `xs.name` and `|> .name`, so a few hits have another receiver,
such as `Map.count`.

The "theorem statements" column is from effect-polymorphism.md §2.2.

| Function | AoC | examples, guide, web | std | std theorem statements |
|---|---|---|---|---|
| `sumBy` | 178 | 28 | 217 | 51 |
| `count` | 90 | 18 | 38 | 8 |
| `filter` | 38 | 31 | 118 | 17 |
| `all` | 30 | 7 | 47 | 10 |
| `any` | 27 | 16 | 99 | 15 |
| `flatMap` | 22 | 11 | 50 | 6 |
| `foldLeft` | 20 | 52 | 131 | 15 |
| `findMap` | 9 | 0 | 9 | 1 |
| `zipWith` | 9 | 4 | 17 | |
| `filterMap` | 4 | 9 | 35 | 10 |
| `scanLeft` | 4 | 3 | 15 | |
| `find` | 0 | 7 | 32 | 13 |
| `foldRight`, `takeWhile`, `findIndex`, `partition`, `span`, `dropWhile`, `maxBy`, `minBy`, `mapAccumLeft` | 0–2 each (`span`'s 23 AoC hits are `Text.span`) | 0–2 | 4–15 | 0–1 |

For comparison, `Option.map` has 15 AoC uses and `Result.map` has 10.
`Map.*` and `Set.*` callbacks have 0–2 AoC uses each.

Priority:
1. `filter`, `foldLeft`, `any`, `all`, `find`.
2. What derives from those: `sumBy`, `count`, `foldRight`.
3. `filterMap`, `findMap`, `flatMap`, `takeWhile`, `dropWhile`, `span`,
   `partition`, `findIndex`.
4. `Option.map`/`flatMap`/`filter` and `Result.map`/`flatMap`.

I'd leave these out until a program needs them:
- `Map`/`Set`/`Vec`;
- `zipWith`, `scanLeft` and `mapAccumLeft` (simple to add later);
- the sorts. A comparison callback that performs effects is rare, and
  `maxBy` calls `f` twice per step (`maxByStep`).

Real programs need this now **[source]**:
- AoC parsing already threads `Fail` through `map`
  (`Aoc/Common/Lines.sw`).
- Day 7 checks a grid with a pure `findMap` that returns `Option Text`, and
  then turns the result into an error by hand
  (`Day07.sw:60`, `manifoldError`). That is an `all` or `forEach` with a
  `{Fail}` callback.
- The guide (`07-recursion.md:236`) and two reject examples tell readers
  that `filter` can't take a partial callback.

## 3. Each function

**Shared facts**, all **[ran]** on a scratch copy of std with the
signatures below:
- Every std file checks. I loaded all 47 library files through one scratch
  program. A deliberate mistake in `Sort.sw` was reported, so the files
  really were checked.
- `aoc` checks.
- Pure uses compile to the same JS as today, function for function, after
  renumbering variables: the empty-row variants `filter$e`, `any$e`,
  `foldLeft$e` and so on are today's loops.
- Checking all of std took 1.50–1.56 s against 1.47–1.50 s, and AoC
  5.57–5.65 s against 5.36–5.51 s: within 3%.
- A partial callback works through the generic re-check:
  `reject/partial-filter.sw` checks.

| Function | New signature (callback, result) | Body under `{e}` | Effects as checked with a `Log` callback on `[1, 5, 2, 7]`, `> 4` | Change needed |
|---|---|---|---|---|
| `filter` | `p: a -> {e} Bool`, `{e} List a` | `filterStep x (filter xs p) (p x)` evaluates the arguments in order, so the **rest of the list goes first** | today's body: `4 3 2 1` (last first); a `Fail` reports the *last* bad element | `let keep := p x` before the `filterStep` call. That gives `1 2 3 4`, and the first bad element is reported. The `filterStep` trick (no doubling while checking) is kept, and `filterKeep`/`filterSkip` still check |
| `foldLeft` | `f: b -> a -> {e} b`, `{e} b` | unchanged; still a tail call | left to right | none |
| `sumBy`, `count` | `f: a -> {e} b` / `p: a -> {e} Bool`, `{e} …` | unchanged: they are `foldLeft` with a lambda | `1 5 2 7` | none. `sumBy`'s 51 theorem statements check |
| `foldRight` | `f: a -> b -> {e} b`, `{e} b` | unchanged: `foldLeft` over the reversed list | `7 2 5 1`, last first, as its definition `f x (foldRight xs …)` says; Koka's `foldr` is also a left fold over the reversed list **[unverified]** | none; say "last to first" in its comment |
| `any`, `all`, `find` | `p: a -> {e} Bool`, `{e} Bool` / `{e} Option a` | unchanged (`if p x then … else …`) | `any`: `1 5` then stops; `all` on `[5, 6, 1, 7]`: `5 6 1` | none |
| `takeWhile` | `p: a -> {e} Bool`, `{e} List a` | unchanged | `7 5 1` on `[7, 5, 1, 9]`: stops | none; `dropWhile` the same |
| `filterMap` | `f: a -> {e} Option b`, `{e} List b` | unchanged (`consSome (f x) (filterMap xs f)`: `f x` first) | `1 5 2 7` | none |
| `findMap` | `f: a -> {e} Option b`, `{e} Option b` | `Option.orElse (f x) (findMap ys f)` evaluates both arguments | `1 5 2 7`: **doesn't stop** | `match f x with Some y => Some y \| None => findMap ys f`. Then the effects are `1 5`, and `findMapIsHeadFilterMap` still checks. The pure JS is no longer one function: it is two that call each other. It still ran at 100,000 elements on both backends, but it needs the benchmark gate |
| `flatMap` | `f: a -> {e} List b`, `{e} List b` | unchanged (`concat (map xs f)`) | follows `map` | none |
| `partition` | `p: a -> {e} Bool`, `{e} Pair …` | two `filter` passes: **every effect twice** **[inferred]** from the body | not run | one pass, a `let` for `p x`, then a cons onto the left or the right side. Its theorems need re-proving (it has few) |
| `span` | likewise | `takeWhile` then `dropWhile`: the prefix's effects twice **[inferred]** | not run | one pass, like `partition` |

**Stack safety and speed of the effectful case [ran]** (a `{Fail}`
callback that never fails, under `Fail.toResult`, whole `stitchwort run`,
on both backends):

| Function | 100,000 elements | 1,000,000 elements |
|---|---|---|
| `foldLeft` | 0.3 s | 0.4 s |
| `any` | 0.4 s | 0.6–0.7 s |
| `filter` | 0.3–0.5 s | 2.5–2.9 s, linear |
| `flatMap` | 0.3 s | JS 0.9 s; native **E-RESOURCE** |

The native `flatMap` failure isn't new. The pure
`List.flatMap (List.range 1000000) (x => [x, x])` fails the same way
natively today, and so does `concat (map …)` with today's effectful `map`.
`concat` isn't stack-safe in the native runtime. That is a separate bug,
outside this plan.

**Pure speed [ran]:** the pure `filter` at 1,000,000 elements × 10 rounds
was the same within noise. The best of five, today's std then the new one:
- native: 1.273 s and 1.277 s;
- JS: 0.652 s and 0.630 s.

**Proofs.** Nothing new is needed for the pure theorems: they are about the
empty-row instance, which computes as before. No current theorem is about
a function's effectful behaviour, such as "`any` stops at the first match".
I'd test that behaviour (§6) rather than prove it now. Proving it would
need D1126's lemmas about `Comp`, such as `bindDone`, and Lean shows the
shape such lemmas take (`anyM_cons`, `anyM_pure`). **[inferred]**

## 4. What's generic and what isn't

Generic already **[source, ran]**:
- `{e}` in a signature;
- the divergence index for bare rows;
- specialisation at `Empty`/`Total`, which is keyed on the parameter types
  `Effects` and `Divergence`, not on names (`crates/rt/src/specialise.rs`
  header);
- `pure_first`;
- the re-check for partial callbacks.

`grep` for `List.map` in `crates/{elab,rt,js}/src` finds only comments,
apart from the items below.

Name-specific, to change:
1. **The three notes** in `crates/elab/src/check.rs`. Each says "(so far
   only `List.map`'s callback may be partial)": in `total_callback_note`
   (~1821), `total_lambda_note` (~1862), and the E-PARTIAL-CALLBACK builder
   (~2015). Proposal: say why from the parameter's own type, as the
   non-std branch already does, with no list of names. For example:
   "`List.sortBy`'s callback has the type `a -> a -> Ordering`, which has
   no `{e}`, so it must finish." The `in_std` branch then differs only in
   saying "doesn't take partial callbacks" instead of suggesting a
   signature change. Snapshots: `examples__reject__partial-filter*.snap`.
2. **`examples/reject/partial-filter.sw`** and
   **`partial-filter-lambda.sw`**. Both become accepted, which I checked
   for the first. They move to `examples/accept/` with tests. A reject
   example for a function that stays pure (`List.sortBy`, say) keeps the
   diagnostic covered.
3. **`docs/guide/07-recursion.md:236`** says `filter`'s callback must
   finish. The sentence changes, and so does `08-abilities.md:142` ("This
   is how `List.map` works") and the "List toolkit" header comment in
   `List/Toolkit.sw`.

## 5. The scratch experiment

The edited std copies and the programs are in the scratchpad, not
committed. Each was run with
`stitchwort check|run|build --js --std-dir <copy>`:

1. Only `filter`'s signature changed: std and AoC check.
   - A `Log` callback shows `4 3 2 1`.
   - `Fail.toResult (() => List.filter ["1", "x", "y"] parseSmall)` gives
     `err: not a number: y`.
2. Plus the `let`: `1 2 3 4` and `err: not a number: x`. std and AoC check,
   and the pure JS is identical.
3. Plus `any` and `all`: they stop at the first decisive element. std and
   AoC check, and the pure JS is identical.
4. Plus `foldLeft`, `find` and `flatMap`, then `sumBy`, `count`,
   `foldRight`, `filterMap`, `takeWhile` and `findMap`: std and AoC check.
   Pure JS for all of them is identical to today's.
5. Plus `findMap` as a `match`: `findMapIsHeadFilterMap` checks, and the
   effects stop at `5`.

No theorem broke at any step.

## 6. Build plan

Every lane resets to local `main` first. Gates for every lane:
- **Theorems unchanged:** no edits to any theorem statement or proof,
  except the re-proofs this plan names for `partition` and `span`.
- **Pure JS:** an extract test per function. Each compares its empty-row
  variant with a pure copy written in the example, as
  `map_at_the_empty_row_is_a_pure_maps_loop` does.
- **Pure speed:** `bench/effect-map` gains modes `filter`, `fold` and
  `any`. Pure is within 10% of `main` on both backends, best of five.
- **Effect semantics:** one `examples/extract` file with a `Log` callback
  per function, with the expected order and the short-circuit as `run:`
  lines. The differential tests compare the backends with the reference.
- **Tests:** `task test:lane AREA=std`, then `AREA=effects`,
  `AREA=examples NAME=partial`, and the named extract tests.

The lanes:
- **Lane 1: core batch.**
  - `filter` (with the `let`), `foldLeft`, `any`, `all`, `find`, `sumBy`,
    `count`, `foldRight`.
  - The three notes generated from the signature.
  - The two reject examples move to accept, with a new reject for a pure
    std helper.
  - The guide's two sentences.
- **Lane 2: second batch.**
  - `filterMap`, `flatMap`, `takeWhile`, `dropWhile`, `findIndex` (via
    `findIndexFrom`).
  - The restructures: `findMap`, and `partition` and `span` as one pass,
    with their re-proofs.
  - The benchmark gate matters most here (`findMap`'s JS shape changes).
- **Lane 3 (if D1243):** `Option.map`/`flatMap`/`filter`,
  `Result.map`/`flatMap`. They aren't loops, so they need checking: does a
  pure `Option.map` still inline as before?

Hashes change for every definition that mentions these functions, which is
fine (no users). The snapshots move with them.

## 7. Risks

- **The pure checker's speed** on large proofs over these functions. It is
  +2–3% on std and AoC in the scratch run **[ran]**. A lane should re-run
  the nested-call timing script from effect-polymorphism.md (SW-437).
- **Type inference at use sites.** `map`'s fold needed several elaborator
  fixes (effect-polymorphism.md, stage 3 table). The scratch run found no
  new failures in std, AoC or the seven reject examples that use these
  functions. The examples in `examples/accept` and the web were not run.
  **[ran, partly]**
- **Effectful speed:** effectful `filter` is about 6× effectful `foldLeft`
  at 1,000,000 elements. That is linear, not a regression; it is stage 4's
  domain.

## 8. Decisions for Matt

**D1239. Make the list toolkit effect-polymorphic now, in batches.**
D1120 said: one function at a time, each when a program needs it. The
scratch run shows the cost is small: no theorem changes, and the pure code
is identical. The guide tells readers that `filter` can't take a partial
callback, which is a gap with D1110's goal.
**Recommend yes:** lanes 1 and 2 of §6.

**D1240. Fix the semantics: left to right, at most one call per element,
stop early.** Effects happen in list order. `any`, `all`, `find`,
`findMap` and `takeWhile` stop calling the callback once the answer is
decided. `foldRight` runs last to first, as its definition reads. All of
this goes in the doc comments and is checked by tests. Koka and Effekt do
the same in their source, and Lean documents it.
**Recommend yes.**

**D1241. Restructure the bodies that break D1240, even where the pure
definition changes.** This covers:
- `filter`: a `let`; the pure code is identical.
- `findMap`: a `match`; its one theorem still checks.
- `partition` and `span`: one pass instead of two, with their few theorems
  re-proved.

The alternative is to leave `partition` and `span` pure.
**Recommend yes.**

**D1242. Explain why a callback must finish from its own type, not with a
list of names.** The three "so far only `List.map`" notes in `check.rs`
say instead that the callback's type has no `{e}`, so it must finish. The
two `partial-filter` reject examples become accept examples.
**Recommend yes.**

**D1243. Include `Option.map`/`flatMap`/`filter` and `Result.map`/`flatMap`
as lane 3.** They have 25 AoC uses and are natural next to the list
functions. `Map`, `Set`, `Vec`, the sorts, `zipWith` and `scanLeft` wait
until a program needs them.
**Recommend yes.**
