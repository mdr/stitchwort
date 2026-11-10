# 11. Running and shipping

## Three ways to run

| Command | Runs on | Use it for |
|---|---|---|
| `stitchwort run` | the fast runtime: types and proofs erased, compiled to register code, and run by a machine with its own stack | the default |
| `stitchwort run --reference` | the type checker's own evaluator | checking a surprise: it defines what programs mean, and it's much slower |
| `stitchwort run --js` | the program compiled to JavaScript, run with Node (`node` on the `PATH`) | heavy computation |

All three print the same output and fail the same way, which the repository's tests check on every example program: the reference evaluator is the oracle, and the other two are compared with it. Tests use the fast runtime too (`stitchwort test --reference` uses the reference).

Exit codes: 0 on success; 1 when the program doesn't check, or `main` fails with `Fail`; 2 when it fails while running: an `IO` error, or running out of resources (a deep recursion, a huge number). How deep a recursion may go depends on the runner (D3450): `stitchwort run` allows 2 million pending calls, native code (`run --native`, `build --native`) allows 16 million, or fewer if a function's frames are so wide that 16 million wouldn't fit the 64 GiB cap on a native stack. The limit is the same on every run of a build, so a program fails at the same depth each time. A native run that recurses to its limit uses memory in proportion to the depth: several GB for a few million pending calls of a hundred bytes or more.

`stitchwort run --native` is a fourth, experimental way: the functions `main` calls run as native code where they and everything they reach compile, and on the fast runtime otherwise (`--verbose` says which). It needs a build with the `native` feature, which `task build` makes. `stitchwort test --native` runs tests the same way ([chapter 9](09-testing.md#two-runtimes)).

## Finding where the time goes

`stitchwort run --profile` runs the program as usual, then prints on standard error where its time went, one row per definition. Here is 2020 day 11 of the AoC solutions (`aoc/`), a seating simulation that takes 20 s:

```
$ stitchwort run --profile --profile-top 8 Aoc.Year2020.Day11.main < inputs/2020/day11.txt
Part 1: 2354
Part 2: 2072
profile: 21.247 s in the program, 15,782 samples every 1 ms
  self %    self s   total %   total s          calls  definition
   68.3%    14.517     68.3%    14.517    113,607,401  Std.Map.Tree.get
   10.1%     2.156     72.1%    15.310      9,789,020  Std.List.foldLeft
    3.0%     0.640     97.8%    20.778      3,234,903  Std.List.map
    2.6%     0.544      2.6%     0.544      3,045,338  Std.List.withIndexFrom
    2.5%     0.526      4.0%     0.844      1,492,400  Std.Map.Tree.joinBuilt
    2.3%     0.488     61.9%    13.154      8,347,578  Std.List.count.λ
    1.8%     0.379     83.2%    17.686      9,771,000  Aoc.Year2020.Day11.Layout.round.λ
    1.6%     0.342     59.6%    12.671      8,515,402  Aoc.Common.Grid.lookup.λ
  (69 more; --profile-top 0 shows them all)
```

- **calls** is exact: how many times the definition was entered, each step of a loop included.
- **self** is the time spent in the definition's own code, **total** the time with it anywhere on the stack (so it includes what it calls). A recursive definition's time is counted once, however deep it goes. Times are sampled every millisecond, so small numbers are rough.
- A lambda is counted under the definition it's written in, with `.λ` after: `Grid.lookup.λ` is the lambda inside `Grid.lookup`. A small function the optimiser inlined has no row of its own; its time is its caller's.

Read it from the top: two thirds of the run is `Map.Tree.get`, and the rows below say who calls it: `Grid.lookup`'s lambda is 60% of the run in total but under 2% itself. Every neighbour of every seat is a `Map` lookup, and 14.5 s over 113.6 million steps of `get` is 128 ns a step. Dividing a total by its calls gives the cost of one call.

A run that's too slow to wait for can be stopped: Ctrl-C, or `timeout 30 stitchwort run --profile …`, prints the profile so far. `--profile-top N` shows N rows (25 by default; 0 for all). Profiling slows a run by a few percent, and only `stitchwort run` on the fast runtime profiles (not `--js`, `--native` or `--reference`).

## A standalone executable

`stitchwort build FILE` (or a project folder, or a function's full name) writes an executable that runs `main` and needs neither `stitchwort` nor the source. It links with the system's C compiler (`$CC`, or `cc`). `-o` names the executable; `--native` compiles `main` and everything it reaches to native code, and fails if any of it can't be.

## Exporting to JavaScript and TypeScript

`export` on a definition makes it part of the ES module that `stitchwort build --js` generates, with TypeScript declarations beside it. The rest of the program is compiled too, but only exports are visible:

<!-- snippet: export.sw -->
```stitchwort
-- Chapter 11: exporting functions to JavaScript and TypeScript.
import Std (List, Option, SafeNat, Text)

type Item = { name: Text, pence: Nat, note: Option Text }

type Discount =
  | NoDiscount
  | PercentOff (percent: Nat)

-- A `Nat` is a `bigint`, a record a plain object, an `Option` a value or
-- `undefined`, and a variant an object with a `$tag`.
export def total (items: List Item) (discount: Discount): Nat :=
  let full := items.map .pence |> .sum
  match discount with
    | NoDiscount => full
    | PercentOff percent => full - full * percent / 100

-- `SafeNat` is a whole number that fits a JS `number`.
export def count (items: List Item): Option SafeNat := SafeNat.ofNat items.length

-- A proof the caller can't give becomes a check when the function is called.
export def share (pence: Nat) (people: Nat): [auto someone: people ≠ 0] → Nat := pence / people

test "total" := total [{ name = "tea", pence = 250, note = None }] (PercentOff 10) == 225
```

```sh
stitchwort build --js export.sw -o out/      # writes out/export.js and out/export.d.ts
```

The declarations:

<!-- generated: build --js export.sw | export.d.ts -->
```ts
// Generated by stitchwort. Do not edit.

export declare class StitchwortInputError extends Error {}
export declare class StitchwortResourceError extends Error {}
export type Item = { readonly name: string; readonly pence: bigint; readonly note?: string };
export type Discount =
  | { readonly $tag: "NoDiscount" }
  | { readonly $tag: "PercentOff"; readonly percent: bigint };
export declare function total(items: readonly Item[], discount: Discount): bigint;
export declare function count(items: readonly Item[]): number | undefined;
export declare function share(pence: bigint, people: bigint): bigint;
```

How Stitchwort's types cross the boundary:

| Stitchwort | TypeScript |
|---|---|
| `Nat`, `Int` | `bigint` (no limit, like the Stitchwort numbers) |
| `SafeNat`, `SafeInt`, `Float` | `number` |
| `Bool`, `Text`, `Char` | `boolean`, `string`, `string` (one character) |
| `List a` | `readonly a[]` as a parameter, `a[]` in a result |
| `Option a` | `a \| undefined`; in a record, an optional property |
| a record | a plain object with its fields |
| a variant | an object with a `$tag` property naming the constructor, and its fields |
| `Map Text v` | a plain object used as a dictionary |
| a proof | nothing: proofs are erased |

Using the module from JavaScript:

<!-- snippet: use-export.mjs -->
```js
import { total, count, share, StitchwortInputError } from "./export.js";

const basket = [{ name: "tea", pence: 250n }];
console.log(total(basket, { $tag: "PercentOff", percent: 10n }));
console.log(count(basket));

for (const attempt of [() => share(100n, 0n), () => total([{ name: "tea", pence: 250 }], { $tag: "NoDiscount" })]) {
  try {
    attempt();
  } catch (e) {
    console.log(e instanceof StitchwortInputError, e.message);
  }
}
```

<!-- node: export.sw use-export.mjs -->
```text
225n
1
true precondition `people != 0` doesn't hold
true items[0].pence: expected a non-negative bigint
```

Everything that comes in is checked. A value of the wrong shape (a `number` where a `bigint` belongs, a missing field, an unknown `$tag`) is refused with a `StitchwortInputError` naming the path to the problem, rather than producing a wrong answer later. A proof the caller can't supply becomes a check: `share` asks for `people != 0`, so the generated code tests it on each call. Running out of stack, on a very deep recursion or very nested data, is a `StitchwortResourceError`.

This is where theorems pay off most: a function that's exported is called by code the compiler never sees, and a theorem about it ([chapter 10](10-proofs.md#a-specification-and-its-program)) holds for every input that passes the checks.

### Fitting an existing format

Attributes change how a type looks at the boundary, to match a JSON format an app already uses, without changing anything inside Stitchwort:

- `@[js.tag "type"]` on a variant type: the tag property is `type` instead of `$tag`;
- `@[js.name "…"]` on a constructor or a field: its tag value or key;
- `@[js.enum]` on a type whose constructors have no fields: a string union, `"IMPORTANT" | "SLIDE_TEXT"`;
- `@[js.unboxed]` on a one-field record: the field's own value, such as a plain `string` for a `UserId`, while Stitchwort still keeps `UserId`s and `OrderId`s apart;
- `@[js.optional]` on a constructor's `Option` field: an optional property.

The details, and the exact rules for each type, are in [syntax.md](../syntax.md#attributes) (sections Numbers in an `export`, `Option` in an `export`, `Map Text V` in an `export`, Attributes, Microtypes) and DESIGN.md §12. `--source-map` also writes a source map from the generated module to the `.sw` files.

## Performance notes

- **Numbers are unbounded.** `Nat` and `Int` never overflow. On the fast runtime a number that fits 64 bits is a machine integer and a bigger one a big integer; in JavaScript every `Nat` and `Int` is a `bigint`.
- **Tail calls are loops.** A function whose recursive call is the last thing it does runs in constant stack everywhere. That matters most in an exported module, which runs on the app's own JavaScript stack: there, a deep non-tail recursion over a long list can run out of stack (a `StitchwortResourceError`), so use an accumulator, as `sumFast` does in [chapter 10](10-proofs.md). The fast runtime has its own stack, and `stitchwort run --js` runs the program in a worker with a large one.
- **Proofs cost nothing at run time.** Theorems, proof fields and `auto` proofs are erased. A one-field record is stored as its field.
- **Types shaped like `Nat` are numbers.** On the fast runtime a `Fin n`, and any type of yours with one constructor that stores nothing and one that stores only a value of the type itself (proofs and indices aside), is a machine number, as `Nat` is, rather than a chain of cells. `Fin.toNat` and `Fin.ofNatLt` take constant time there, since the number is already the one they return.
- **Checking can compute.** Tests and `rfl` proofs run code while checking. That's usually fast, but a proof that needs to compute a lot shows up as slow checking; `STITCHWORT_TIMINGS=1` prints where the time went, declaration by declaration. For a slow run, `stitchwort run --profile` (above).
- **Results are cached.** The check cache and the test cache are keyed by content, so after the first run only what changed is checked and tested again.
- **`include` is cheap.** A file read with `include "…"` becomes one compact text literal, so a large puzzle input costs no more than a string of the same size.

More: DESIGN.md §12 (the JavaScript contract), [evaluator-speed.md](../evaluator-speed.md), [fast-runtime.md](../proposals/fast-runtime.md), and [publishing.md](../publishing.md) for publishing the playground.
