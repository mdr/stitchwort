# Proposal: errors with messages (`Fail` and `Result`)

**Status:** accepted 23 October 2026 with the decisions in §6 (SW-367, D1042 (b)). Stage 1
is built ("Stage 1 as built", §5); `Fail.toResultMapIn` from §3.7 followed with proof-only
reification (SW-419, closing SW-378); stage 2 is next.

## 1. The problem and the goals

An outside review of Advent of Code day 2 found that `parseRanges` hides bad
input:

```
def parseRanges (t: Text): List Range := t.trim.split ',' |> .filterMap Range.parse
```

(`aoc/src/Aoc/Day02/Day02.sw:106`). `filterMap` keeps the pieces that
`Range.parse` (`aoc/src/Aoc/Common/Range.sw:9-12`) reads and drops the others
without telling anyone. So `11-22,bad` gives one range, and `11-22, 33-33` also
gives one range: `" 33"` isn't a number, so the second range is lost. Both runs
print answers as if nothing were wrong.

Most of the other days do the same thing. Each parser below drops or ignores
input it can't read:

| Day | Parser | What happens to bad input |
|---|---|---|
| 1 | `parseTurns` = `lines.filterMap Turn.parse` (`Day01.sw:23`) | a bad line is dropped |
| 2 | `parseRanges` (above) | a bad range is dropped |
| 3 | `Bank.parse` = `t.toList \|> .filterMap .toDigit` (`Day03.sw:43`) | a non-digit is dropped |
| 4 | `parseGrid: … -> Option Grid` (`Day04.sw:51`) | `main` prints a fixed message for `None`. It is visible, but it doesn't say which line |
| 5 | `parseDatabase` (`Day05.sw:32-33`) | a line that is neither a range nor a number is dropped |
| 6 | `parseWorksheet` (`Day06.sw:39`) | reads by layout and never fails. Its proofs cover the parse (`Day06/Proofs/Correct.sw:136`) |
| 7 | `Abort` turned into `Option` (`Day07.sw:44-51`) | `main` prints "There is no S." |
| 8 | `parsePoints` = `lines.filterMap parsePoint` (`Day08.sw:42`) | a bad line is dropped |

Std has nothing that carries a reason for a failure. `Std.Abort`
(`crates/elab/src/std/Abort/Abort.sw`) says only *that* a computation gave up.
There is no `Result` or `Either` type: a search of `crates/elab/src/std` finds
only a comment that uses the word "Either" (`core/Decidable.sw:9`). `IO` has
`print`, `readLine` and `readAll` (`core/IO.sw:11-14`), but no way to write to
standard error or to choose an exit code. The text-and-IO proposal left this
for later: "Recoverable errors, through `Result`-returning operations, can come
later" (`docs/proposals/text-and-io.md:308`).

**Goals.**

1. **A failure is visible and names its cause.** It carries a message, such as
   `expected a range like 11-22, got 'bad'`.
2. **It works in pure code and in `main`.** A parser stays a function that tests
   and proofs can call. In `main`, a failure nobody handles is printed to
   standard error and the program exits with a non-zero code.
3. **It works with `Abort`.** Each can be turned into the other, and both can
   appear in the same code.
4. **It can be proved about.** Each handler comes with theorems, as `Abort`'s
   do (`Abort.toOptionNeed`, `Abort.orElseNeed`, `Abort.sw:54-63`). Proofs
   stated over a parsed model can then assume that the parse succeeded.
5. **JavaScript callers can use it.** A failure should look sensible to code
   that calls an exported function.

## 2. Unison's design, and what we borrow

Unison is the closest relative: its abilities are the model for ours (DESIGN.md
§8). It has three abilities for errors, which its docs describe together
(<https://www.unison-lang.org/docs/fundamentals/abilities/error-handling/>):

| Unison | Signature (base 7.20.0) | Carries |
|---|---|---|
| `Abort` | `abort : {Abort} a` | nothing |
| `Throw e` | `throw : e ->{Throw e} a` | a value of a type you choose |
| `Exception` | `raise : Failure ->{Exception} x` | a `Failure` |

The page says: "The Exception ability is similar to the Throw ability, except the
error type is pinned to be a data type called Failure". A `Failure` is
`Failure : Link.Type -> Text -> Any -> Failure`. Its fields are a type tag, a
message, and a payload of any type (`Any`). `Generic.failure : Text -> a ->
Failure` builds one from just a message and a value
(<https://www.unison-lang.org/docs/fundamentals/control-flow/exception-handling/failure/>).

The handlers and conversions in `@unison/base` 7.20.0 are below. I read each
signature from Share's API,
`https://api.unison-lang.org/users/unison/projects/base/releases/7.20.0/definitions/by-name/<name>`.
The same definitions are browsable at
<https://share.unison-lang.org/@unison/base/code/releases/7.20.0/latest>.

| Name | Signature | What it does |
|---|---|---|
| `Exception.catch` | `'{g, Exception} a ->{g} Either Failure a` | turns a failure into data |
| `Exception.reraise` (also `Either.toException`) | `Either Failure a ->{Exception} a` | turns data back into a failure |
| `Exception.raiseGeneric` | `Text -> a ->{Exception} b` | fails with a message and a value |
| `Exception.unsafeRun!` | `'{g, Exception} a ->{g} a` | crashes on a failure |
| `Exception.toThrow` | `'{g, Exception} b ->{g, Throw Failure} b` | |
| `Throw.toEither` | `'{g, Throw e} a ->{g} Either e a` | |
| `Throw.toException` | `(e ->{g1} Failure) -> '{g2, Throw e} a ->{g1, g2, Exception} a` | |
| `Throw.toOptional` | `'{g, Throw e} a ->{g} Optional a` | |
| `Either.toThrow` | `Either e a ->{Throw e} a` | |
| `Abort.toOptional!` | `'{g, Abort} a ->{g} Optional a` | |
| `Abort.toException` | `'{g, Abort} a -> Link.Type -> Text ->{g, Exception} a` | gives a reason to a plain abort |
| `Abort.toThrow` | `e -> '{g, Abort} a ->{g, Throw e} a` | |
| `Optional.toAbort` | `Optional a ->{Abort} a` | our `Abort.need` |
| `Optional.toException` | `Text -> Link.Type -> Optional a ->{Exception} a` | our proposed `need o "msg"` |
| `IO.catchAll` | `'{IO, Exception} a ->{IO} Either Failure a` | also catches `bug` |
| `bug` | `a -> b` | stops the program. `catch` doesn't see it |
| `List.map` | `(a ->{𝕖} b) -> [a] ->{𝕖} [b]` | map accepts a function that performs abilities |

**At the top level.** "The Exception ability, along with the IO ability, are the
only two ability requirements that can remain unhandled" in a program that
`run` executes, and "The UCM runtime will stop the execution of the program
which raises an Exception with the Failure in the console" (error-handling page
above). Their guidance is to prefer abilities, and to convert to data
(`Either`, `Optional`) at the edges.

**What we borrow.**

- **A message-carrying ability, used by default.** Unison's everyday error is
  `Exception`, a failure with a message. We do the same with one small ability,
  `Fail` (§3.1).
- **The family of conversions,** each in both directions: ability → data
  (`catch`, `toEither`, `toOptional`), data → ability (`reraise`,
  `Optional.toException`, `Optional.toAbort`), and ability → ability
  (`Abort.toException`, `Throw.toException`). §3.3 has one of ours for each
  that we need, with the same shape.
- **`main` may leave the error ability unhandled,** and the runtime reports it.
  This is Unison's rule for `run` (§3.5).
- **`map` with a function that performs abilities,** so that a parser can map a
  failing function over a list (§3.4, D1050).

**What we don't borrow, and why.**

- **`Any` and type links in the error.** `Any` holds a value whose type is only
  known at run time. Stitchwort has no such type, and adding one would weaken
  what proofs can say. A message is what this ticket needs. A typed error
  (Unison's `Throw e`) can be added later if a program needs to branch on the
  kind of error (D1045).
- **`bug`, a crash that `catch` can't see.** If one existed, the theorem
  "`Fail.toResult` turns every failure into `Err`" would be false. Running out
  of resources (`E-RESOURCE`) already covers "this shouldn't happen". `Partial`
  covers code that might not stop (D1052).
- **`Either` with `Left` as the failure.** The name doesn't say which side is
  the error. Rust (`Result<T, E>`, `Ok`/`Err`), Roc (`Result ok err`) and Koka
  (`error<a>` with `Ok`) all name the sides. We do too (D1047).
- **A result type that every operation can return.** Unison's `raise` has
  result type `x` for any `x`. Our operations can't be generic in their result
  (`docs/proposals/abilities.md:254`). So `Fail` is built the way `Abort` is:
  the operation returns `Empty`, and a wrapper function turns that into any
  type (`Abort.sw:23-28`).

**Other languages,** where they help decide a choice:

- **Koka** (`std/core/exn`): an `exn` effect, `throw(message)`, and handlers
  `try` and `maybe` that turn it into a value. Like Unison, the default carries a
  message. This supports `Fail` carrying `Text`
  (<https://koka-lang.github.io/koka/doc/std_core_exn.html>).
- **Rust**: `main` may return `Result<(), E>`. When it returns `Err`, the error
  is printed to stderr and the exit code is 1
  (<https://doc.rust-lang.org/std/process/trait.Termination.html>). This
  supports exit code 1 (D1048). `?` also corresponds to our `orFail`.
- **Lean**: `Except ε α` with `throw` and `tryCatch`. An uncaught `IO` error
  prints `uncaught exception: <msg>` and exits with code 1
  (<https://lean-lang.org/doc/reference/latest/IO/>).
- **Roc**: `Result ok err` with `?` for early return. The order (value first,
  then error) is Rust's too. This supports `Result a e` (D1047).
- **Effekt**: has typed exceptions, with a signature like Unison's
  `Throw e`. Nothing there changes the choices above.

## 3. The proposed std API

### 3.1 The ability

A new module, `crates/elab/src/std/Fail/Fail.sw`, laid out like
`Abort/Abort.sw`:

```
-- Fail with a message. The one operation returns `Empty`, so no handler can
-- resume the computation: there's no value to resume it with. Code calls
-- `Fail.fail msg`, which has any result type; handlers match on `stop`.
ability Fail where
  stop: Text -> {Fail} Empty

def Fail.fail (msg: Text): {Fail} a := Empty.absurd (Fail.stop msg)

-- The value in an `Option`, or fail with `msg`.
def Fail.need (o: Option a) (msg: Text): {Fail} a :=
  match o with
    | Some x => x
    | None   => Fail.fail msg

-- The same, for dot notation: `t.toNat.orFail "expected a number, got '${t}'"`.
def Option.orFail (o: Option a) (msg: Text): {Fail} a := Fail.need o msg

-- Fail with `msg` unless `ok`.
def Fail.ensure (ok: Bool) (msg: Text): {Fail} () := if ok then () else Fail.fail msg
```

In code, after `import Std (Fail)` and `import Std.Fail (fail, need, ensure)`,
this reads as `need o "msg"`, `ensure (from <= to) "msg"` and `fail "msg"`.
`need` and `ensure` have the same names as Abort's, but they also take a
message. A file that imports both by their short names gets `E-AMBIGUOUS` where
it uses one, and fixes it by writing the qualified name. That's acceptable.

### 3.2 The result type

```
-- A computation's value, or why it failed.
type Result (a: Type) (e: Type) =
  | Ok (value: a)
  | Err (error: e)
```

It goes in the prelude next to `Option` (`docs/syntax.md:214`), so that `Ok`
and `Err` can be written without an import. It also gets a `DecEq` instance, as
`Option` has (`core/DecEq.sw:32`), so that tests can compare results with `==`.
It comes with the usual functions: `Result.map`, `Result.mapError`,
`Result.flatMap`, `Result.toOption`, `Result.getOrElse`, `Result.isOk`, and
`Option.toResult (err: e): Option a -> Result a e`. The type takes any error
type, not just `Text`, so that a typed `Throw e` added later (D1045) can reuse
it.

### 3.3 Handlers and conversions

| Ours | Type | Unison's counterpart |
|---|---|---|
| `Fail.toResult` | `(() -> {Fail \| e} a) -> {e} Result a Text` | `catch`, `toEither` |
| `Fail.toOption` | `(() -> {Fail \| e} a) -> {e} Option a` | `Throw.toOptional` |
| `Fail.orElse` | `a -> (() -> {Fail \| e} a) -> {e} a` | `Abort.toDefault!` |
| `Fail.recover` | `(Text -> {e} a) -> (() -> {Fail \| e} a) -> {e} a` | `catch` then `Either.fold` |
| `Result.orFail` | `Result a Text -> {Fail} a` | `reraise` |
| `Fail.context` | `Text -> (() -> {Fail \| e} a) -> {Fail \| e} a` | none (Rust's `anyhow` `.context`) |
| `Abort.orFail` | `Text -> (() -> {Abort \| e} a) -> {Fail \| e} a` | `Abort.toException` |
| `Fail.toAbort` | `(() -> {Fail \| e} a) -> {Abort \| e} a` | `Exception.toAbort`-like (forgets the message) |

The main handler is written as `Abort.toOption` is:

```
def Fail.toResult (prog: () -> {Fail | e} a): {e} Result a Text :=
  handle prog() with
    | return x         => Ok x
    | Fail.stop msg, k => Err msg
```

`Fail.context` puts something in front of a failure's message, such as where
the failure happened. The `Fail.fail` inside its clause isn't caught by this
handler, because a handler's clauses run outside it (`docs/syntax.md:495-497`).

```
def Fail.context (where: Text) (prog: () -> {Fail | e} a): {Fail | e} a :=
  handle prog() with
    | return x         => x
    | Fail.stop msg, k => Fail.fail "${where}: ${msg}"
```

### 3.4 Helpers for parsing

- **`List.mapIn (f: a -> {e} b): List a -> {e} List b`** maps a function that
  may perform abilities, such as `Fail`. Today `List.map` takes only a pure
  function, `a -> b` (`std/List/Toolkit.sw:12`), so a parser has no way to map a
  failing function over a list. Unison's `List.map` takes any function; whether
  we generalise ours instead is D1050.
- **`Text.toNatOrFail` and `Text.toIntOrFail`** (`{Fail} Nat`, `{Fail} Int`)
  trim the text, then read it. If that doesn't work they fail with
  `expected a whole number, got 'x'`, so that every program words this message
  the same way (D1051).
- **Message style** (D1051): start with a lowercase letter, say what was
  expected and then what was found, and put the found text in single quotes,
  which also shows stray spaces: `expected a range like 11-22, got ' 33-x'`. Add
  where it happened with `Fail.context "line 3"`.

### 3.5 An unhandled failure in `main`

Today `main` must have type `() -> {IO} ()` or `() -> {IO, Partial} ()`
(`crates/driver/src/run.rs:100`, `:132`). We would also allow
`{IO, Fail}` and `{IO, Fail, Partial}`.

How the runner does it (stage 2 decides the details):

- The runner runs `Std.Fail.toResult (() => main())` instead of `main()`. The
  handler is ordinary Stitchwort code, so the reference evaluator, the fast
  runtime (`stitchwort-rt`), the JS runner (`crates/js/src/run.rs`) and the
  playground all get the same `Result` back. None of them needs a new built-in
  operation, and `IO` stays as it is.
- If the result is `Err msg`, everything printed so far is flushed. This is
  already done for other errors (`run.rs:308-312`, and the JS runner at
  `crates/js/src/run.rs:599-603`). Then `error: <msg>` is written to standard
  error and the program exits with code 1 (D1048). The JS runner passes the
  message back to the CLI through the error file it already uses, under a new
  exit code like `EXIT_IO` and `EXIT_RESOURCE` (`crates/js/src/run.rs:48-51`).
  The CLI prints it as it does for those.
- Exit codes today: a runtime error (`E-IO`, `E-RESOURCE`) exits with 2
  (`crates/cli/src/main.rs:695`, `:757`), and a program that doesn't check exits
  with 1. Note that `text-and-io.md:72` still says 1 for every failure, which no
  longer matches the code. Exit code 1 for `Fail` matches Rust and Lean. A
  script that needs to tell "bad input" apart from "the runtime gave up" can
  still do so, because the runtime's errors use 2.
- In the playground, the message appears below the output, the way `E-RESOURCE`
  does now.
- **Testing `main`:** `IO.simulate input (() => Fail.toResult main)` gives the
  lines printed and the `Result`. Nothing new is needed for this.

### 3.6 JavaScript

Exported functions must be pure today (DESIGN.md:786), so an exported function
can't perform `Fail`. What it can do is return a `Result`. Data types with
parameters already cross the boundary (DESIGN.md:834), so
`export def parse (t: Text): Result Range Text` gives

```ts
export type Result<A, E> = { $tag: "Ok"; value: A } | { $tag: "Err"; error: E };
```

and a TypeScript caller writes `if (r.$tag === "Err") …`. This needs no new
code, only a test in `examples/extract/`.

Later, an exported function whose row is `{Fail}` could be wrapped in
`Fail.toResult`, and its `Err` thrown as a `StitchwortFailure` (an `Error`
subclass with the message), next to the existing `StitchwortInputError`. That
belongs to "host-provided abilities" (DESIGN.md:801), and is D1049.

### 3.7 Theorems to ship

These are in the style of `Abort.toOptionNeed` and `Each.collectEach`
(`std/Each/Each.sw:64-67`). Each holds by `rfl` or by case analysis plus `rfl`:

```
theorem Fail.toResultPure (v: a): Fail.toResult (() => v) = Ok v
theorem Fail.toResultFail (msg: Text): Fail.toResult (() => (Fail.fail msg: a)) = Err msg
theorem Fail.toResultNeed (msg: Text): (o: Option a) -> Fail.toResult (() => Fail.need o msg) = Option.toResult msg o
theorem Fail.toResultEnsure (msg: Text): (ok: Bool) -> Fail.toResult (() => Fail.ensure ok msg) = (if ok then Ok () else Err msg)
theorem Fail.toResultOrFail: (r: Result a Text) -> Fail.toResult (() => Result.orFail r) = r
-- Reading an `Option` and going on: the form a proof about a parser uses.
theorem Fail.toResultNeedThen (k: a -> {Fail} b) (msg: Text): (o: Option a) ->
    Fail.toResult (() => k (Fail.need o msg)) = Option.fold (Err msg) (x => Fail.toResult (() => k x)) o
-- A map over a list fails with the first element's failure, or gives every result.
theorem Fail.toResultMapIn (f: a -> {Fail} b): (xs: List a) ->
    Fail.toResult (() => xs.mapIn f) = Result.traverse (x => Fail.toResult (() => f x)) xs
theorem Fail.toOptionNeed (msg: Text): (o: Option a) -> Fail.toOption (() => Fail.need o msg) = o
theorem Abort.orFailNeed (msg: Text): (o: Option a) -> Fail.toResult (() => Abort.orFail msg (() => Abort.need o)) = Option.toResult msg o
```

These make results usable in proofs. For example, a theorem about day 2's
answers can take `h: Fail.toResult (() => parseRanges t) = Ok ranges` as a
hypothesis, as Day 4's theorem takes `h: parseGrid lines = Some grid`
(`Day04/Proofs/Parse.sw:29`). A general law, `Fail.toOption p =
(Fail.toResult p).toOption` for every computation `p`, would need induction on
the translated computation tree. It's welcome if stage 1 finds it easy, but it
isn't required.

## 4. Worked example: day 2

`Range.read` goes next to `Range.parse` in `Aoc.Common`. `Range.parse` stays,
defined as `Fail.toOption (() => Range.read t)`. Day 5 uses it until that day
is converted.

```
-- "11-22" is `{ from = 11, to = 22 }`. Spaces around either number are
-- allowed: " 11 - 22 " reads the same.
def Range.read (t: Text): {Fail} Range :=
  match (t.split '-').map (part => part.trim.toNat) with
    | [Some from, Some to] =>
      ensure (from <= to) "the range '${t}' ends before it starts"
      { from, to }
    | _ => fail "expected a range like 11-22, got '${t}'"
```

Day 2:

```
import Std (Each, Fail, Int, List, Nat)
import Std.Fail (fail, ensure)

def main(): {IO, Fail} () :=
  let ranges := parseRanges IO.readAll()
  IO.print "Part 1: ${solvePart1 ranges}"
  IO.print "Part 2: ${solvePart2 ranges}"

-- Ranges separated by commas. Spaces and a final line ending are allowed;
-- anything else fails, naming the text that isn't a range.
def parseRanges (t: Text): {Fail} (List Range) := t.trim.split ',' |> .mapIn Range.read
```

```
$ echo '11-22,bad' | stitchwort run Aoc.Day02.main
error: expected a range like 11-22, got 'bad'
$ echo $?
1
```

Tests (`Day02/Tests/Examples.sw`). The two inputs from the review are the first
two:

```
def parsed (t: Text): Result (List Range) Text := Fail.toResult (() => parseRanges t)

test "a field that isn't a range" := parsed "11-22,bad" == Err "expected a range like 11-22, got 'bad'"
test "a space after a comma" := parsed "11-22, 33-33" == Ok [range 11 22, range 33 33]
test "spaces around the numbers" := parsed " 11 - 22 \n" == Ok [range 11 22]
test "a missing number" := parsed "11-" == Err "expected a range like 11-22, got '11-'"
test "three numbers" := parsed "1-2-3" == Err "expected a range like 11-22, got '1-2-3'"
test "a trailing comma" := parsed "11-22," == Err "expected a range like 11-22, got ''"
test "no input" := parsed "" == Err "expected a range like 11-22, got ''"
test "backwards" := parsed "22-11" == Err "the range '22-11' ends before it starts"
test "parse" := parsed "4-14,1490-3407\n" == Ok [
  range 4 14,
  range 1490 3407
]
```

The existing tests that use `parseRanges example` as a list of ranges
(`exampleRanges`, `Tests/Input.sw`) change to
`Fail.orElse [] (() => parseRanges example)`. Because the expected answers
can't come from an empty list, a parse failure still fails these tests. None of
day 2's proofs mention `parseRanges` (`grep` over `aoc/src`), so no proof has
to change.

## 5. Staged plan

Each stage is one lane. A stage starts only after the one before it has merged.

| Stage | Work | Tier | Gate |
|---|---|---|---|
| 1. Std | `Std.Fail` (§3.1, §3.3), `Result` in the prelude with `DecEq` and the functions in §3.2, `List.mapIn`, `Text.toNatOrFail`/`toIntOrFail`, the theorems in §3.7. A `Fail` section in `docs/syntax.md` next to `Abort` (`:556`), and `examples/accept/fail.sw` (with `IO` passing through, as `examples/accept/abort.sw` does). An `examples/extract/` test that a `Result` crosses to TypeScript as in §3.6 | Opus (the theorems, the prelude change, and the row typing of `mapIn` and `context`) | `cargo test` for the workspace. All §3.7 theorems check. Std hash snapshots accepted on purpose (the rt lowering test has one, commit `1810af95`). AoC unchanged and green |
| 2. Running `main` | Accept `{IO, Fail}` and `{IO, Fail, Partial}` (`run.rs` `MAIN_CALL`, `E-MAIN-TYPE` message). Report `Err` in the reference evaluator, `stitchwort-rt`, the JS runner and the playground (§3.5). Update `text-and-io.md`'s exit-code paragraph | Sonnet | CLI tests: the same stdout, stderr and exit code from `run`, `run --reference` and `run --js` for a failing `main`, with output printed before the failure kept. Playground test in `crates/web`. Existing `run_js.rs` tests unchanged |
| 3. AoC | Day 2 as in §4, then 1, 3, 5, 8 (parsers to `Fail`, with `Fail.context "line N"`), and 4 and 7 (`main` only: `parseX lines` then `.orFail "…"`, which keeps day 4's parse proofs and day 7's `Option` tests). Day 6 unchanged (D1053) | Sonnet for day 2 and day 5 (day 5 splits on the blank line). DeepSeek for days 1, 3, 8, 4 and 7, which are mechanical once day 2 sets the pattern | `cd aoc && stitchwort test` green. Real-input answers unchanged. A malformed-input test for each converted day. `docs/aoc-2025.md` gets a short entry |
| later | `{Fail}` exports throwing `StitchwortFailure` (D1049). Typed `Throw e` if a program needs it (D1045) | — | — |

Stage 3 for day 5 needs care. Its input is a list of ranges, a blank line, then
a list of ids, and `filterMap` picks the two lists apart by trying each line as
both (`Day05.sw:30-33`). The new parser splits at the blank line, reads the
lines above it with `Range.read` and the lines below it with
`Text.toNatOrFail`, and fails with a message if there's no blank line.

**Stage 1 as built (23 October 2026).** `Result` is in the core
(`std/core/Result.sw`) and the prelude, with `Result.decEq`, a `DecEq`
instance and a `Show` instance (`Ok 2`, `Err "no"`). Its other functions are
in `std/Result/Result.sw`: §3.2's list, plus `Result.traverse` and
`Result.errorOrElse`. `Std.Fail` (`std/Fail/Fail.sw`) has §3.1 and §3.3 as
written, `Text.toNatOrFail` and `Text.toIntOrFail` with D1051's message for
both (the text is quoted as given, before trimming), and eight of §3.7's
theorems, each by `rfl` on each case. `List.mapIn` is in
`std/List/Toolkit.sw`. `docs/syntax.md` has a `Fail` section,
`examples/accept/fail.sw` has a `main` with `IO` passing through, and
`examples/extract/results.sw` shows a `Result` crossing to TypeScript as
§3.6 says. The existing std hashes didn't change; the new names were added
to the snapshot. Deviations:

- `Fail.context`'s parameter is `label`, not `where`, which is a keyword.
- `Result` is a core type, so a dot call such as `.map` in a library file
  may mean `Result.map`, and `Result/Result.sw` now loads with
  `List/Toolkit.sw` (the expectation in `std_library.rs` is updated).
- `Fail.toResultMapIn` isn't built. At first `Fail.toResultNeedThen` wasn't
  built either: an equation between calls of a handler with an open row
  (`{e}`, as `toResult` has) was elaborated as a computation over the empty
  row, `runPure (bind (toResult …) (r => Done (r = …)))`, and was only an
  equation once the handled computation computed. With an unknown `k x` it
  doesn't, so `rfl` was refused; the same happened to `Abort.toOption c =
  Abort.toOption c` for any `c`. D1055 (b) fixed the cause: at the empty row
  such a call is run in place (abilities.md, "Effectful calls at the empty
  row"), and `NeedThen` is in `Fail.sw`. `MapIn` still doesn't go through:
  its `Cons` case needs `toResult` of a `bind` over an unknown `f x` to
  split into cases, which needs induction on the computation tree, and no
  proof can take apart a `{Fail}` computation. Open for Matt.
  Effect-polymorphism stage 0 (SW-405) removed one of the two obstacles: a
  computation passed where a `Comp` is expected is no longer run in place,
  and `Effect.foldCompBind` exists. The other remains: the case split on
  `f x` needs a binder whose type is a `{Fail}` computation, and that type
  can't be written (effect-polymorphism.md, "As built (stage 0)").
  **Closed (SW-419, 24 Oct 2026):** D1141 (d) kept abilities on arrows, and
  proof-only reification (proof-reification.md, stage R1) gives proofs the
  split: `match reify (() => f x) with | return y => … | Fail.stop msg, _ =>
  …`. `Fail.toResultMapIn` is in `Fail.sw` as stated in §3.7, by induction
  on the list with a split on `f x` and then on `xs.mapIn f`, where the
  induction hypothesis (generalised with it) says what the rest gives. Its
  axiom report is empty. The general law welcome above,
  `Fail.toOptionToResult` (`Fail.toOption t = (Fail.toResult t).toOption`),
  is there too, with `Fail.toResultThen`, `Fail.toOptionThen` and
  `Abort.toOptionThen`.
- A dot call ending a handled lambda, `Fail.toResult (() => " 4".toNatOrFail)`,
  isn't run there, so the handler's result type is `{Fail} Nat` (and
  `==` asks for `DecEq ({Fail} Nat)`). `Abort` behaves the same
  (`Abort.toOption (() => "4".toNat.orAbort)`); the full name,
  `Text.toNatOrFail " 4"`, works.

**Stage 2 as built (23 October 2026).** `main` may have the type `() -> {IO, Fail} ()` or `() -> {Fail} ()`. The driver (`crates/driver/src/run.rs`, `main_calls`) elaborates the call once, for every runner: it tries the old call first, and if `main` has `Fail` it elaborates `Std.Fail.recover (m => Some m) ((u => Pair.snd (main (), None)) : () -> {IO, Fail} (Option Text))`, lifted into `{IO, Partial}` as before. The runner gets `Some msg` or `None` as the final value, instead of `()`. Each runner looks at that value in one place: the reference evaluator (`run_loop`) and `stitchwort-rt` (`Runner::finished`) return `RunError::Failed msg`, and the JS runner leaves with the new `EXIT_FAIL` (72), the message in the error file. The CLI prints `error: <msg>` and exits with 1 (an `E-IO` or `E-RESOURCE` still exits with 2); the playground shows `error: <msg>` below the output it had streamed. No new built-in operation was needed, and programs whose `main` has no `Fail` elaborate exactly as before (the existing hashes didn't change). Tests: `an_unhandled_failure_is_reported_alike` in `run_reference.rs` and `run_js.rs` (stdout, stderr and exit code equal across `run`, `--reference` and `--js`, for `examples/accept/main-fail.sw`, `main-fail-ok.sw` and a `{Fail}`-only `main`), and a playground test in `web/tests/browser.mjs`. Deviations:

- `{IO, Fail, Partial}` isn't accepted yet: `Fail.recover` takes a total computation, and a handler can't wrap a `Partial` one (`E-PARTIAL`). A `Fail` `main` that needs `Partial` has to handle `Fail` itself. A handler over `Partial` is a later question.
- The message for `E-MAIN-TYPE` names the three types.

## 6. Decisions for Matt

**Decided (Matt, 23 Oct 2026):** D1045–D1049 and D1051–D1053 as recommended below. D1050: (a), a new `List.mapIn` now, plus a separate experiment lane that tries generalising `List.map` itself the Unison way (`(f: a -> {e} b)`) and reports what breaks; if it goes cleanly, `mapIn` is folded into `map` and the convention extends to the other list functions.

**Decided later (Matt, 23 Oct 2026):** D1055 (b): fix the cause in the elaborator, so a handler call whose ability row is empty after instantiation is a plain value and equations about it are ordinary propositions (no proof-only twin). D1056 (a): fix the dot-call-in-handled-lambda bug before stage 3.

**D1045. What does a failure carry?**
(a) Only a message (`Fail`, `Text`).
(b) Only a value of a type the program chooses (Unison's `Throw e`). Messages
are then `Throw Text`.
(c) Both, as two abilities with conversions between them.
**[Recommend (a) now.]** Unison's everyday error is a message, and so is Koka's.
Every AoC case is a message. (c) doubles the handlers and theorems before any
program needs them. `Result a e` already allows any error type, so `Throw e`
can be added later without breaking anything.

**D1046. The ability's name.**
(a) `Fail`, with `fail msg`.
(b) `Exception`, with `raise msg` (Unison's name).
(c) `Error`, with `throw msg`.
**[Recommend (a).]** It's short and reads well next to `Abort` (`{IO, Fail}`).
"Exception" makes people expect a crash that can be caught anywhere, which this
isn't.

**D1047. The data type.**
(a) `Result a e = Ok (value: a) | Err (error: e)`, in the prelude.
(b) The same with the error first, `Result e a` (Haskell's `Either e a`
order).
(c) `Either e a = Left | Right` (Unison, Haskell).
**[Recommend (a).]** The names say which side failed, and the order matches
Rust and Roc, which readers are most likely to know. It's in the prelude because
`Ok`/`Err` are as common as `Some`/`None`.

**D1048. An unhandled `Fail` in `main`.**
(a) Print `error: <msg>` on stderr and exit with 1.
(b) The same, but exit with 2, like the runtime's own errors.
(c) Don't allow it: `main` must handle `Fail` itself.
**[Recommend (a).]** This is what Rust and Lean do. It keeps 2 for "the runtime
gave up", and it's Unison's rule that `main` may leave errors unhandled.

**D1049. JavaScript.**
(a) Exported functions return `Result`, which crosses as
`{ $tag: "Ok"; value } | { $tag: "Err"; error }`. Nothing else for now.
(b) Also allow `{Fail}` exports that throw a `StitchwortFailure`.
**[Recommend (a) now, (b) later.]** (a) costs nothing, and a TS caller can
check it with a type test. (b) is the first ability allowed across the boundary
and should come with the host-abilities work.

**D1050. Mapping with a function that can fail.**
(a) A new `List.mapIn (f: a -> {e} b)`. `List.map` stays pure.
(b) Generalise `List.map` itself, as Unison does.
**[Recommend (a).]** `List.map` has many lemmas that proofs use (for example
`List.mapMap`, `Toolkit.sw:589`). Changing its type risks all of them. A
separate name is cheap, and could be merged into `List.map` later.

**D1051. Messages and helpers.**
(a) A convention (lowercase, `expected X, got 'text'`) plus
`Text.toNatOrFail`/`Text.toIntOrFail` in std.
(b) The convention only: programs write `t.toNat.orFail "…"`.
**[Recommend (a).]** Reading a number is the most common step in every AoC
parser, so it should give the same message everywhere.

**D1052. A `bug`/panic that handlers can't catch.**
(a) Don't have one.
(b) Add one, as Unison's `bug`.
**[Recommend (a).]** It would make "`toResult` catches every failure" false. A
program that thinks it's in an impossible state can `fail` with a message.

**D1053. How strict the AoC parsers are.**
(a) Allow spaces around fields and a final line ending. Fail on everything
else, blank lines included, except where the puzzle uses a blank line as a
separator (day 5). Leave day 6's layout parser alone.
(b) Strict: no extra spaces at all.
(c) Lenient: also skip blank lines everywhere.
**[Recommend (a).]** It accepts what a person might paste, and says why it
rejects anything else. Day 6's parser is part of its proved spec
(`Day06/Proofs/Correct.sw:136`). It can't fail, so it has nothing to report.
