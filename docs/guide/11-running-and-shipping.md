# 11. Running and shipping

## Three ways to run

| Command | Runs on | Use it for |
|---|---|---|
| `stitchwort run` | the fast runtime: types and proofs erased, compiled to register code, and run by a machine with its own stack | the default |
| `stitchwort run --reference` | the type checker's own evaluator | checking a surprise: it defines what programs mean, and it's much slower |
| `stitchwort run --js` | the program compiled to JavaScript, run with Node (`node` on the `PATH`) | heavy computation |

All three print the same output and fail the same way, which the repository's tests check on every example program: the reference evaluator is the oracle, and the other two are compared with it. Tests use the fast runtime too (`stitchwort test --reference` uses the reference).

Exit codes: 0 on success; 1 when the program doesn't check, or `main` fails with `Fail`, or returns `ExitStatus.failure` (see [An exit status](#an-exit-status)); 2 when it fails while running: an `IO` error, or running out of resources (a deep recursion, a huge number). How deep a recursion may go depends on the runner (D3450): `stitchwort run` allows 2 million pending calls, native code (`run --native`, `build --native`) allows 16 million, or fewer if a function's frames are so wide that 16 million wouldn't fit the 64 GiB cap on a native stack. The limit is the same on every run of a build, so a program fails at the same depth each time. A native run that recurses to its limit uses memory in proportion to the depth: several GB for a few million pending calls of a hundred bytes or more.

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

## An exit status

`main` may return an `ExitStatus` instead of `()`, and the program then ends with that number: `stitchwort run`, `--reference`, `--js`, `--native`, built executables and the playground (which shows `exit status 3` below the output when it isn't 0) all do. It is the way for a tool to say more than "worked" and "failed": `stitchwort fmt --check` exits 1 when a file would change and 2 when it can't read one.

<!-- snippet: exit-status.sw#main -->
```stitchwort
-- 0: nothing to fix; 1: something to fix; 3: no file named.
def verdict (arguments: List Text): ExitStatus := match arguments with
  | [] => ExitStatus.of 3
  | ["clean", ..rest] => ExitStatus.success
  | _ => ExitStatus.failure

def main(): {IO} ExitStatus :=
  let status := verdict (IO.args ())
  IO.print "exit status ${status}"
  status
```

<!-- output: run exit-status.sw -- clean -->
```text
exit status 0
```

With no argument it prints `exit status 3` and the shell sees 3.

`ExitStatus` holds a number from 0 to 255 (a `Fin 256`): a bigger one means different things on different systems, so `ExitStatus.of 300` is refused when the program is checked, and a number computed at run time goes through `ExitStatus.ofNatCheck`, which gives `None` when it is too big. The library names two statuses, `ExitStatus.success` (0, the only code that means the same everywhere) and `ExitStatus.failure` (1); a program names the others itself. A status is an ordinary value, so tests read it: `(IO.simulate [] program).snd` is the status a program would end with, and `(verdict []).toNat == 3` states it directly. `Fail` that nothing handles is still status 1, and a runtime error is still 2, so a program that returns 2 itself can't be told apart from one that ran out of resources.

## A command line

A program that takes options describes them once with `Args` (a standard library namespace), instead of matching on `IO.args()` by hand. From the description come the parser, the usage line, `--help` and the error messages. Each option is one combinator, and `.and` joins them: the function at the start takes the options' values in the same order and builds the program's own record. Write the function's parameter types; an unannotated lambda there isn't accepted yet.

<!-- snippet: args.sw#spec -->
```stitchwort
type Options = { shout: Bool, times: Nat, names: List Text }

def program: Args.Program := { name = "greet", about = "Greets each person." }

def options: Args.Spec Options :=
  Args.Spec.start ((shout: Bool) (times: Nat) (names: List Text) => ({ shout, times, names }: Options))
    |> .and (Args.flag "shout" (help := "Greet with three exclamation marks."))
    |> .and (Args.option "times" (default := 1) (help := "How often to greet each person."))
    |> .and (Args.arguments "NAME" (atLeast := 1) (help := "Who to greet."))
```

`Args.flag` is a switch, `Args.option` takes a value (`--times 2` or `--times=2`) and falls back to its `default`, `Args.required` and `Args.optional` take one that must or may be left out, `Args.many` one that can be repeated, and `Args.arguments` the plain arguments. Values are read by the `Args.Value` interface, which `Text`, `Nat`, `Int` and `Path` have; `Args.choice` makes one for a type with a finite list of values, read as each shows itself. `--` ends the options, so everything after it is an argument (a file called `-x` is still reachable), and a lone `-` is an argument. `--help` and `-h` print the help. An option that doesn't repeat is an error the second time, never "last one wins".

`Args.run` reads `IO.args()`, calls the program with its options, prints the help for `--help` (exit status 0) and, for a mistake, prints the message, the usage line and where the help is to standard error and exits with status 2 (`Args.misuse`: 2 is the usual code for a command used wrongly, in Bash's builtins, `argparse` and Go's `flag`, and it keeps that apart from 1, a program's own failure). Its program returns `()`, so `main` returns an `ExitStatus`; a program that picks its own statuses uses `Args.runStatus`, whose body returns an `ExitStatus`. Here is the first:

<!-- snippet: args.sw#main -->
```stitchwort
def greet (options: Options): {IO} () := options.names.forEach (name =>
  let line := if options.shout then "Hello, ${name}!!!" else "Hello, ${name}."
  List.replicate options.times line |> .forEach IO.print)

def main(): {IO, Fail} ExitStatus := Args.run program options greet
```

<!-- output: run args.sw -- --shout --times 2 Ada Grace -->
```text
Hello, Ada!!!
Hello, Ada!!!
Hello, Grace!!!
Hello, Grace!!!
```

<!-- output: run args.sw -- --help -->
```text
usage: greet [--shout] [--times N] NAME...
Greets each person.

arguments:
  NAME...     Who to greet.
options:
  --shout     Greet with three exclamation marks.
  --times N   How often to greet each person. (default: 1)
  -h, --help  Show this help.
```

Parsing itself is a pure function of a list of text, `Args.parse program options arguments`, whose result is `Run options`, `Help text` or `Wrong error`, so a command line is tested with plain tests and no `IO`. Each `Args.Error` is a value (`BadValue "--times" "twice" "a whole number"`) and `error.describe` is its message; `Args.problems options` lists a spec's own mistakes, such as a name used twice.

<!-- snippet: args.sw#tests -->
```stitchwort
def parse (arguments: List Text): Args.Outcome Options := Args.parse program options arguments

test "options, in any order, and the defaults" :=
  parse ["Ada", "--times=2", "--shout"] == Run { shout = True, times = 2, names = ["Ada"] }
    && parse ["Ada"] == Run { shout = False, times = 1, names = ["Ada"] }

test "after -- everything is a name" := parse ["--", "--shout"] == Run { shout = False, times = 1, names = ["--shout"] }

test "what is wrong" :=
  parse [] == Wrong (Missing "NAME")
    && parse ["--times", "twice", "Ada"] == Wrong (BadValue "--times" "twice" "a whole number")

test "--help is an outcome, not an effect" := match parse ["--help"] with
  | Help text => text.startsWith "usage: greet [--shout] [--times N] NAME..."
  | _ => False
```

## Exporting to JavaScript and TypeScript

`export` on a definition makes it part of the ES module that `stitchwort build --js` generates, with TypeScript declarations beside it. The rest of the program is compiled too, but only exports are visible:

<!-- snippet: export.sw -->
```stitchwort
-- Chapter 11: exporting functions to JavaScript and TypeScript.
import Std (List, Option, SafeNat, Text)

type Item = { name: Text, pence: Nat, note: Option Text }

type Discount = | NoDiscount | PercentOff (percent: Nat)

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
export def share (pence people: Nat): [auto someone: people ≠ 0] → Nat := pence / people

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
- **A field read in a lambda runs every time.** `cave.height` inside a lambda is `cave.rows.length`, called on each pass; hoist it into a `let` outside the lambda. In the AoC 2021 day 15 notes, that one `let` took the day's run from 31.7 s to 17.6 s (`aoc/NOTES-2021.md:3676`), and the proofs didn't change. Nothing warns about it, and hoisting by the compiler is parked (SW-1814).
- **Types shaped like `Nat` are numbers.** On the fast runtime a `Fin n`, and any type of yours with one constructor that stores nothing and one that stores only a value of the type itself (proofs and indices aside), is a machine number, as `Nat` is, rather than a chain of cells. `Fin.toNat` and `Fin.ofNatLt` take constant time there, since the number is already the one they return.
- **Checking can compute.** Tests and `byComputing` proofs run code while checking. That's usually fast, but a proof that needs to compute a lot shows up as slow checking. A declaration still checking after about 7 seconds (250 million evaluation steps) gets a note on standard error, `` note: still checking `Main.t`: over 250,000,000 evaluation steps so far, unfolding `countdown` (it stops at 10,000,000,000) ``, and another each time the steps double; at 10 billion steps it fails with `E-RESOURCE`, naming the declaration and the definition it was unfolding. `STITCHWORT_TIMINGS=1` prints where the time went, declaration by declaration. For a slow run, `stitchwort run --profile` (above).
- **Results are cached.** The check cache and the test cache are keyed by content, so after the first run only what changed is checked and tested again.
- **Checking can use several cores.** `stitchwort check --jobs 4` (or `-j 4`, or `STITCHWORT_JOBS=4`) checks a project's namespaces on four workers side by side, each namespace once what it imports is done, filling the check cache; then the check runs as usual over what they wrote, so it prints exactly what one job prints. It helps a cold check of a project with many namespaces that don't import each other; a warm check has nothing to share out. With `--no-cache` the workers' results are kept in memory for the run. Each worker holds what its namespaces import, so memory grows with the jobs. `--recheck`, `--carry-over`, `--only` and `--no-project-cache` run one job.
- **`include` is cheap.** A file read with `include "…"` becomes one compact text literal, so a large puzzle input costs no more than a string of the same size.

More: DESIGN.md §12 (the JavaScript contract), [evaluator-speed.md](../evaluator-speed.md), [fast-runtime.md](../proposals/fast-runtime.md), and [publishing.md](../publishing.md) for publishing the playground.
