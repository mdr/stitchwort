# Entry points: how a program says where it starts

**Status:** decided, 10 November 2026. Ticket SW-2550 (D3451), updated for
D3452 and D3456 by SW-2561. Still open: D3453 and D3454 ([§9](#9-questions-for-matt)).
Written against `lane/SW-2550` from `main` at `3cf9aa769`. Paper lane:
nothing was built or run.

Claims about Stitchwort cite `file:line` and were read in the source.
Claims about other languages are **[cited]** (read in the source linked in
[Sources](#sources) while writing this) or **[unverified]** (from memory,
not re-checked).

## Contents

0. [Summary](#0-summary)
1. [The problem](#1-the-problem)
2. [What happens today](#2-what-happens-today)
3. [Prior art](#3-prior-art)
4. [The options](#4-the-options)
5. [Which types can be run](#5-which-types-can-be-run)
6. [Errors and their wording](#6-errors-and-their-wording)
7. [Hello world, and how it reads to a newcomer](#7-hello-world-and-how-it-reads-to-a-newcomer)
8. [The work for each option (dropped)](#8-the-work-for-each-option)
9. [Questions for Matt](#9-questions-for-matt)
10. [Calls I made](#10-calls-i-made)
11. [What follows, and what already works](#11-what-follows-and-what-already-works)
- [Sources](#sources)

## 0. Summary

**Decided.** D3452 (Matt, 9 Nov 2026): any function of a runnable type can be
run by name, Unison-style. There is no annotation. `main` is a style
convention (SW-2549: name a definition `main` only when it is a program entry
point) and the default name `run` looks for. D3456 (Matt, 9 Nov 2026): no
warning on a `main` that can't run, for now.

**Rejected** (§4): `@[entry]` (a), a reserved `main` checked at its
definition (b), and both (c). The earlier recommendation of (b) is replaced
by this.

**Open:** D3453 (does `main` without `()` count as runnable?) and D3454 (does
`run NS` run `NS.main`?), each with its trade-off in §9.

**Already true:** in a project, `run` runs any runnable function by its full
name; a loose file runs only its `main`. What is left to implement is small
(§11).

## 1. The problem

A newcomer writes this, which looks right and passes `stitchwort check`:

```stitchwort
def main: {IO, Partial} () := IO.print (Nat.toText (List.sum (stepsOfAll [3, 7, 27])))
```

Only `stitchwort run` says it's wrong (`E-MAIN-TYPE`): `main` must be a
function from `()`. This exact line is in the repo,
`examples/accept/partial-map-main.sw:16`, which has been "accepted" for
weeks without ever running. The editor showed no squiggle, and its "▶ Run"
icon (`crates/lsp/src/lens.rs:91-101`) sat above a `main` that couldn't run.

The opposite mistake passes too: `examples/accept/fin-eq.sw:8` has
`def main: Bool` and `examples/accept/mutual.sw:7` has `def main: Nat`,
plain values that happen to be called `main`. Nothing says "this isn't a
program". Matt's style rule (SW-2549, 9 Nov 2026): call something `main`
only when it is an entry point.

What we want: a `main` that can't run is an error **where it's written**,
seen by `check`, `test`, the editor and the playground's Check tab, and the
rule for what counts as an entry point is the same in every tool.

Matt's answer (D3452, D3456) was not to add that rule: a bad `main` is
still reported only by `run`, and the "▶ Run" icon can still sit above one.
The goal above is kept as the problem statement; §4 says which options it
led to and why they were rejected.

## 2. What happens today

**The type check is in the runner, not the checker.** `Session::main`
(`crates/driver/src/run.rs:150-176`) looks up the last definition whose
name is `main` (or `NS.main` in a file with a `namespace` line) and only
then checks it, by elaborating a call `((u => main ()) : () -> {Std.IO,
Partial} ()) ()` and, if that fails, the same in `{Std.IO, Std.Fail,
Partial}` (`main_calls`, `run.rs:130-135`; `main_call`, `run.rs:180-225`).
A failure is `E-MAIN-TYPE`; no `main` is `E-NO-MAIN`. Nothing in the
elaborator knows the name `main`: the only `"main"` strings in `crates/elab`,
`crates/driver`, `crates/js` and `crates/native` are in `run.rs:155,163`.

**How each tool finds the entry point:**

| Tool | Today | Code |
|---|---|---|
| `run file.sw` | the file's `main`, checked when run (`E-NO-MAIN`, `E-MAIN-TYPE`) | `crates/cli/src/main.rs:1682-1698`, `run.rs:150` |
| `run Day05.main` (project) | any definition by full name; must have a runnable type, checked when run (`E-RUN-UNKNOWN`, `E-RUN-TYPE`). `run` in a project always takes a name | `main.rs:1699-1739`, `run.rs:231-271` |
| `build dir/` | the project's one namespace that **declares** `main`, found from the syntax (a `Decl::Signature` named `main`); none or several is an error naming them | `crates/cli/src/build.rs:243-285` |
| `build file.sw`, `build Rogue.main` | as `run` | `build.rs:92-130` |
| Playground, single file | Run button: `main`, via `Session::main` | `crates/web/src/lib.rs:484` |
| Playground, projects (AoC, rogue) | the manifest's `"main": "Day05.main"`, written by the bundler; `main_named` | `web/bundle-projects.sh:91,138`, `crates/web/src/project.rs:390` |
| `test` | nothing: tests that run a program call it, `IO.simulate input main` | `docs/guide/01-getting-started.md`, `web/index.html:717` |
| LSP | "▶ Run" lens above a top-level `def` whose written name is `main`, read from the syntax alone; it runs `stitchwort run file.sw` | `crates/lsp/src/lens.rs:59-107`, `editors/vscode/runs.js:80-91` |
| `--js`, `--native`, bench | after `Session::main` / `main_named` | `crates/js/src/run.rs:13-14`, `crates/bench/src/programs.rs:474,577` |

**Runnable types.** A function from `()` to `()` whose abilities are among
`IO`, `Fail` and `Partial` (`MAIN_TYPE`, `run.rs:39`): `() -> ()`,
`() -> {IO} ()`, `() -> {Fail} ()`, `() -> {IO, Fail} ()`,
`() -> {IO, Partial} ()`, `() -> {IO, Fail, Partial} ()` and so on
(`docs/projects.md:295-304`; `docs/syntax.md:908` for `Fail`). Command-line
arguments come from `IO.args()`, not a parameter (`docs/syntax.md:823`),
and the exit code from `Fail` (1) or a runtime error (2), not a result.

**How `main`s are written in the repo** (grep of `def main` in `.sw`
files): 73 `def main(): {IO, Fail} ()`, about 36 `{IO}`, 7 `{IO, Partial}`,
1 `{IO, Fail, Partial}`, and the three broken ones above. 71 are AoC days
(`aoc/src/Aoc/YearN/DayN`), 47 accepting examples, 5 in the guide's
examples. A second entry point in one namespace happened once:
`Aoc.Year2024.Day14.mainExample` and `Day18.mainExample`
(`aoc/NOTES-2024.md:4050-4054`, `:5615`), since replaced by `IO.args`
(`grep mainExample aoc/src` finds nothing).

## 3. Prior art

Two families. Most languages find the entry point **by name** and check
its type when the program is compiled; a few **annotate** it. A third
approach, Unison's, runs **any** term of the right type by name, checked
when run, which is what Stitchwort's `run NS.name` does today.

| Language | How the entry point is found | Allowed types | When it's checked | Several in one program |
|---|---|---|---|---|
| **Rust** | `fn main` by name in a binary crate; it may even be an import (`use foo::bar as main`) **[cited]** | no arguments, return type implements `Termination`: `()`, `!`, `ExitCode`, `Result<T, E>` **[cited]** | when the crate is compiled, `cargo check` included: wrong type is E0580, none is E0601 **[unverified]** | one per binary crate; a package has many binaries (`src/bin/*.rs`), each with its own `main` |
| **Rust `#[tokio::main]`** | not an entry-point marker: a macro that rewrites an `async fn` into a sync one that starts a runtime; "can be used on any function and not just the `main` function" **[cited]** | — | — | — |
| **Swift `@main`** | an attribute on a **type** that provides `static func main()`, possibly from a protocol extension, so frameworks can supply the start-up code **[cited]** | `main()`, may `throw` **[cited]** | at compile time; "only one entry point": one `@main` type or one `main.swift`, and `@main` in `main.swift` is an error **[cited]** | no |
| **Scala 3 `@main`** | an annotation on any method; "the name of the program is in each case the name of the method" **[cited]** | parameters of any type with a `FromString` parser; the generated program parses the command line **[cited]** | at compile time | yes: each `@main` method becomes its own class, run by name **[cited]** |
| **Haskell** | `Main.main` by name: "one of which, by convention, must be called Main and must export the value main" **[cited]**; a module without a header is `module Main(main) where` **[cited]** | "a computation of type `IO τ` for some type `τ`"; the result is discarded **[cited]** | when module `Main` is type-checked **[unverified, but standard GHC behaviour]** | GHC's `-main-is A.foo` picks another, "when testing, it is often convenient to change which function is the main one" **[cited]** |
| **Lean 4** | `def main` by name; `lean --run` "invokes the program's `main` definition" **[cited]**; Lake's `lean_exe` names the root module **[unverified]** | `IO Unit`, `IO UInt32`, `List String → IO UInt32` **[cited]**; note `IO Unit` is not a function | when compiled to an executable **[unverified]** | one per executable; a Lake package has many |
| **Unison** | any term, named at the prompt: `run myMain a b c`; "the entry point can be called anything" **[cited]** | "a delayed computation returning any type", run with handlers for `IO` and `Exception` **[cited]** | when run (every term in the codebase is already type-checked) | any number; `compile myMain out` makes an executable **[cited]** |
| **Go** | `func main` in `package main` **[cited]** | "takes no arguments and returns no value" **[cited]** | at compile time | one per `main` package; a module has many under `cmd/` |
| **C#** | static `Main` by name, or top-level statements **[cited]** | `void`/`int`/`Task`/`Task<int>`, with or without `string[] args` **[cited]** | at compile time | "If you have more than one class with a `Main` method, you must use the **StartupObject** compiler option" **[cited]** |
| **Koka** | `fun main` by name; `koka -e file.kk` compiles and runs it **[unverified]** | its effect must be within `io` (inferred `() -> <console,div> ()` in a typical program, per a tutorial) **[unverified]** | when compiled as a program **[unverified]** | — |
| **Effekt** | `def main()`: "a main function that serves as the entry point to the program" **[cited]**; `effekt hello.effekt` runs it **[cited]** | `() => Unit` with effects the runtime handles **[unverified]** | at compile time **[unverified]** | — |
| **OCaml** | no `main`: "an executable OCaml file's entry point is its first line"; `let () = …` is the idiom **[cited]**; dune's `(executable (name main))` names the module **[cited]** | — | — | one per `executable` stanza |

**What this says for Stitchwort.**

- **By name and checked at compile time is the norm**, in exactly the
  languages closest to Stitchwort (Lean, Haskell, Koka, Effekt) and in the
  mainstream (Rust, Go, C#). In each, the check happens when the program is
  compiled, and an editor running the compiler sees it. Stitchwort's `check`
  is its compile step, so "check where defined" is the same thing.
- **Annotations exist for a reason Stitchwort doesn't have yet.** Swift's
  `@main` is on a *type* so a framework (UIKit, SwiftUI, ArgumentParser) can
  supply `main()`; it replaced `@UIApplicationMain` and friends **[cited]**.
  Scala 3's `@main` buys any name, several per project, and command-line
  parsing from the parameters. Stitchwort has no frameworks that own
  start-up, and arguments come from `IO.args()`.
- **Every by-name language has an escape hatch for "run this other one"**:
  GHC's `-main-is`, C#'s `StartupObject`, Cargo's separate binaries, Unison
  running anything. Stitchwort's `run NS.name` already is one.
- **Lean accepts a non-function `main : IO Unit`**, and so do Haskell and
  Unison's delayed computations in their own way. That bears on §5.

## 4. The options

**D3452 (Matt, 9 Nov 2026) chose a fourth way, (d), which this section
didn't consider.** It is Unison's: any function of a runnable type can be run
by name, with no annotation and no reserved name. `main` is a style
convention and the default name `run` looks for. It is today's `run NS.name`
and `run file.sw` unchanged. (a), (b) and (c) are kept below as the record.

### (a) The annotation: `@[entry]` (rejected, D3452)

```stitchwort
@[entry]
def main(): {IO} () :=
  IO.print "Hello"
```

**The rule.** A definition marked `@[entry]` is an entry point, whatever
its name; its type is checked where it's defined (`E-ENTRY-TYPE`). The
name `main` means nothing special. A namespace (or file) may have several
entry points.

**Syntax.** The attribute machinery exists: a closed registry,
`crates/elab/src/attributes.rs:81-138`, where bare names are "reserved for
language-level attributes" (`attributes.rs:79-80`) and `noReceiver` and
`tailrec` are the precedents (`attributes.rs:58-62`). `@[entry]` would be a
new `Spec` with targets `Definition` and `Export`, no argument. The
existing check gives "`entry` can't be used on a theorem" (`E-ATTRIBUTE`,
`attributes.rs:200-240`) for free. Alternatives considered: `@[main]`
(Swift's and Scala's word, but it reads as the name rather than a role),
and a keyword (`entry def main`), which is more syntax for one feature.

**How each tool finds it.** `run file.sw`: the file's one `@[entry]`;
several need a way to choose (`run file.sw demo`, a new argument form).
`run NS.name`: must name an entry point, or keep running anything. `build
dir/`: the project's one entry point, found from the syntax (attributes are
in the AST). Playground manifests: unchanged (they name the function).
LSP lens: above each `@[entry]`, from the syntax. `test`: unchanged.

**What it does well.** Intent is explicit and greppable; any name works;
several checked entry points per namespace (a `mainExample` would get a
run icon and a static check); no name is reserved.

**What it costs.** Every program pays a line, the first thing a newcomer
types (§7). And the trap it creates is the one it was meant to remove:
`def main(): {IO} ()` without the attribute, which is what someone coming
from any other language writes, is silently not a program, and `run` says
`E-NO-ENTRY` about a file that plainly has a `main`. Closing that trap
needs a warning on an unmarked `main`, at which point `main` is special by
name again: that's option (c).

### (b) `main` by name, checked where it's defined (rejected, D3452 and D3456)

```stitchwort
def main(): {IO} () :=
  IO.print "Hello"
```

**The rule.** A top-level declaration whose written name is `main` (no
dots; `def`, or `export def`) is its namespace's entry point, `main` or
`NS.main`. Where it's defined, after the kernel admits it, its type must be
runnable (§5), or it's `E-MAIN-TYPE`, pointing at the definition. Any other
top-level declaration called `main` (a theorem, a type synonym or an
instance) is
`E-MAIN-TYPE` too, with the note that `main` is the name of a program's
entry point. Local definitions and parameters called `main`, and `main`
inside a type's namespace (`def Grid.main`), are ordinary names. (Calls:
§10.)

**How each tool finds it.** All as today (§2): the name is the rule, and
it's already the rule in `Session::main`, `build.rs`'s project scan, the
LSP lens and the playground manifests. What changes is only *when* the type
is checked: `check`, `test`, the LSP's diagnostics and the playground's
Check tab now report a bad `main`, because they run the elaborator. The
runner's own check stays as a defence and for `run NS.other`.

`run NS.name` keeps running any function of a runnable type, checked when
run (`E-RUN-TYPE`): the escape hatch, like `-main-is`. Whether `run Day05`
(a namespace) should mean `run Day05.main` is D3454.

**What it does well.** Nothing new to learn or write; the 120-odd existing
`main`s are already right; the editor, `check` and CI catch the bug; one
rule everywhere. **What it costs:** the name `main` is taken (which Matt's
style rule already wants), and an extra entry point in the same namespace
gets no static check or run icon.

### (c) Both (rejected, D3452)

`main` is an entry point by name and checked as in (b); `@[entry]` marks
others, any name, checked the same way, each with a run icon. `@[entry]`
on `main` is redundant: a warning, or allowed silently (another call to
make). `run file.sw` runs `main`, and a new form picks another
(`run file.sw --entry demo`, say). `build dir/` counts `main`s only, or
all entry points (another call).

**What it does well.** The newcomer's path is (b)'s; the occasional second
entry point gets checked. **What it costs:** two ways to say one thing, and
the rules for how they interact (redundancy, which one `run file.sw` and
`build dir/` pick, whether `run NS.name` still runs unmarked functions).
All for a need the repo has met once, and solved another way.

### Comparison

| | (a) `@[entry]` | (b) `main`, checked | (c) both |
|---|---|---|---|
| A wrong `main` is reported by `check` and the editor | yes (if marked) | **yes** | yes |
| An unmarked `def main(): {IO} ()` | silently not a program (unless a warning, which is (c)) | **the entry point** | the entry point |
| Hello world | 2 lines + an attribute in chapter 1 | **as today** | as today |
| Several checked entry points per namespace | yes | no (`run NS.f` checks at run time) | yes |
| Reserved names | none | `main` | `main` |
| New CLI forms | choosing among several in a file | none (D3454 optional) | choosing among several |
| Matches | Swift, Scala 3 | Rust, Haskell, Lean, Go, C#, Koka, Effekt | Rust + `#[test]`-style markers, roughly |
| Can grow into (c) later | already (c) minus the name rule | **yes, additively** | — |

## 5. Which types can be run

**Keep today's set** (`run.rs:36-39`, `docs/projects.md:295-304`): a
function from `()` to `()` whose abilities are among `IO`, `Fail` and
`Partial`, including the pure `() -> ()`. It covers everything programs
do: arguments come from `IO.args()`, the exit status from `Fail` (1) and
runtime errors (2) (`docs/syntax.md:908`). There's no need for Lean's
`IO UInt32` or `List String → IO UInt32` forms, and no ticket asks for an
exit code.

**The check** stays in the runner (`run.rs:180-225`), shared by `main` and
`run NS.name`, including sub-rows and the pure case, which a plain annotation
wouldn't accept (`docs/proposals/text-and-io.md:70`). Moving it into the
elaborator so `check` could report it was the idea of option (b), which D3452
and D3456 declined.

**`def main: {IO} ()`, without `()`.** In Stitchwort this is legal and
means something: a top-level computation, like
`def firstIsA: {IO} Option Nat` (`examples/accept/abort-constant.sw:9`),
performed where it's used. Lean's `def main : IO Unit` is the same idea.
Should it be an entry point?

- *For:* it's what `partial-map-main.sw`'s author wrote; Lean and Haskell
  newcomers will write it; the runner could support it by trying `main`
  as well as `main ()`.
- *Against:* it gives two ways to write the same program, which the
  formatter can't unify (they're different types). It doesn't fit the way
  the guide tests a program: `IO.simulate input main` passes `main` as a
  function (`docs/guide/01-getting-started.md`, `web/index.html:717`), so a
  constant `main` would be runnable but not testable the same way. And every
  doc, example and lens would have to say "or".

**Open** (D3453). It is not decided whether to accept this, or keep
refusing it with a note that says what to add. The trade-off is in §9.

## 6. Errors and their wording

**Not taken up.** This section words errors for a `main` checked where it is
defined, which D3456 declines for now. The wording is kept for when that
changes; the codes are as they are today.
scripts and snapshots keep working; wording follows `run.rs`'s current
messages.

**A `main` of the wrong type, where it's defined** (`E-MAIN-TYPE`, now
from `check`):

```
[E-MAIN-TYPE] Error: `main` is this program's entry point, so it must be a function from `()` to `()`
   ╭─[ partial-map-main.sw:16:1 ]
16 │ def main: {IO, Partial} () := IO.print …
   │ ───────────┬────────────
   │            ╰── this has type `{IO, Partial} ()`, which isn't a function
   │ Note: write `def main(): {IO, Partial} () := …`
```

The note depends on what's wrong; the label always gives the type:

| What's wrong | Note |
|---|---|
| no `()` (a computation) | ``write `def main(): {IO, Partial} () := …` `` (the same row, with `()` added) |
| a result other than `()` (`def main(): {IO} Nat`) | ``a program's result is what it prints: `IO.print "${…}"` `` |
| another ability left unhandled (`{IO, Abort}`) | ``it may use `IO`, `Fail` and `Partial`; handle `Abort` inside `main` `` (today's note, `run.rs:172`) |
| not a function or computation at all (`def main: Nat`) | ``if this isn't a program's entry point, give it another name`` |
| a theorem, synonym or instance called `main` | ``a theorem can't be run; give it another name`` |

The headline names the rule, not the list of four types the current
message spells out (`run.rs:168`); the list moves to the syntax reference,
and the note gives the one fix that applies.

**No entry point when run.** `run file.sw` with no `main`: `E-NO-MAIN`, as
now, "there's no `main` to run in hello.sw", note "a program starts at
`def main(): {IO} () := …`". In a project, `run` always names its target,
so "none" is `E-RUN-UNKNOWN` as now; `build dir/` keeps its "no namespace
of project aoc/ declares `main`" (`build.rs:263-272`).

**Several entry points.** One namespace can't have two `main`s (it's
`E-DUPLICATE`). Several namespaces with one each is normal (AoC), and only
`build dir/` (and `run Day05` if D3454 says yes) has to pick: the existing
message lists them and says how to name one (`build.rs:273-281`).

**An attribute on something not runnable** only exists under (a) and (c):
`@[entry]` on a theorem, instance or synonym is `E-ATTRIBUTE` from the
existing registry check ("`entry` can't be used on a theorem"); on a
definition of the wrong type, `E-ENTRY-TYPE`, worded as the table above.

**`run NS.name` of a function that can't run** keeps `E-RUN-TYPE`
(`run.rs:262-270`), since it's not a definition-time rule.

## 7. Hello world, and how it reads to a newcomer

| | Lines | What a newcomer meets first |
|---|---|---|
| (b) | `def main(): {IO} () := IO.print "Hello"` | a function called `main`, as in Rust, Go, Haskell, Lean, Koka, C, Java |
| (a) | `@[entry]` and the same line | an attribute, the guide's first; attributes are otherwise introduced in chapter 11 for the JS boundary (`docs/guide/11-running-and-shipping.md:152-158`) |
| (c) | as (b) | as (b); `@[entry]` appears only when someone needs a second program |

Under the decided approach (D3452) the newcomer's path is (b)'s: `main`, no
attribute.

The guide's first sentence about programs is "A program is a `.sw` file
with a `main` function" (`docs/guide/01-getting-started.md:19`). Under (b)
it stays true and becomes enforced; one sentence can be added: "If `main`'s
type isn't one a program can have, `stitchwort check` says so." Under (a)
chapter 1 would have to explain attributes before the reader has seen a
type.

## 8. The work for each option

Dropped. It sized options (a), (b) and (c), which D3452 rejected. What is
left to do is in [§11](#11-what-follows-and-what-already-works).

## 9. Questions for Matt

**Decided**

- **D3452 (Matt, 9 Nov 2026): any function of a runnable type can be run by
  name, Unison-style.** No annotation. `main` is a style convention, and the
  default name `run` looks for. This rejects options (a), (b) and (c) of §4
  (all three give `@[entry]` or a reserved `main` checked at its definition).
- **D3456 (Matt, 9 Nov 2026): no warning on a `main` that can't run, for
  now.** So `check`, `test` and the editor stay silent about it, and only
  `run` reports it.

**Open**

**D3453: does `def main: {IO} ()` (no `()`) count as runnable?** Today it
doesn't: `run` reports `E-MAIN-TYPE` (§5).
- *Accept it* (Lean's way): newcomers from Lean and Haskell write it, and
  `partial-map-main.sw`'s author did. But there would be two spellings of a
  program that the formatter can't unify, and `IO.simulate input main` in the
  guide only works with the function form.
- *Keep refusing it*: one form, the guide's tests keep working, and the
  error says to add `()`. But it is only seen when the program is run (D3456).

**D3454: does `stitchwort run Day05` (a namespace) run `Day05.main`?** Today
`run` in a project takes a full function name and anything else is
`E-RUN-UNKNOWN`.
- *Yes* (as GHC's `-main-is Day05`): saves typing for the 71 AoC days, and
  makes `main`'s role as the default name real. A name with dots could be
  both a namespace and a function (`def Day07` in `Aoc.Year2025`), which would
  be an error naming both.
- *No*: nothing new to explain, and `run Day05.main` is already short enough
  next to the file form.

## 10. Calls I made

- **A theorem, synonym or instance called `main`** gets no error either: with
  no definition-time rule (D3456), the only report is `run`'s `E-NO-MAIN` or
  `E-RUN-TYPE`.
- **Error codes stay** (`E-MAIN-TYPE`, `E-NO-MAIN`, `E-RUN-TYPE`).
- **`@[entry]` is not reserved.** D3452 says no annotation, so the name is
  free.

## 11. What follows, and what already works

**Already works** (read in `crates/cli/src/main.rs:1760-1818` and
`crates/driver/src/run.rs:150-271`; `stitchwort run --help` from the main
checkout's release binary; nothing was built or run):

- `stitchwort run Day05.anything` in a project runs any function by its full
  name, if its type is runnable (§2); otherwise `E-RUN-TYPE` (`run.rs:262`),
  or `E-RUN-UNKNOWN` for a name that isn't there (`run.rs:237`). `--help`
  says: "A file, or the full name of a function in the project". So D3452 is
  already true in a project.
- `stitchwort run file.sw` runs the file's `main` only (`Session::main`,
  `run.rs:150`), checked when run (`E-MAIN-TYPE`, `E-NO-MAIN`).
- `build Rogue.main` and the playground manifests name a function, so they
  already take any runnable function.
- Nothing checks `main` at its definition. D3456 keeps it so.

**What implementation is left** (small; each runs only its own targeted tests):

1. **Say it in the docs** (Sonnet or DeepSeek, about 20 min): `docs/syntax.md`
   "Entry points" (the rule from SW-2549: `main` only for an entry point; any
   runnable function runs by name; the runnable types; that `main` is the
   default name), a sentence in `docs/guide/01-getting-started.md`, and
   `docs/projects.md` "Running and testing". No tour page: nothing new to
   enjoy.
2. **Run a named function in a loose file** (a gap in D3452; see below): today
   a file target can only run its `main`. If wanted, a form such as
   `run file.sw --entry demo`, in `load_main`'s file branch and
   `Session::main`.
3. **D3453**, if it is answered yes: `Session::main` tries `main` as a
   computation as well as `main ()`.
4. **D3454**, if it is answered yes: in `load_main`, a target that names a
   namespace means `NS.main`; the same in `build`. Tests:
   `crates/driver/tests/projects/run.rs`, `crates/cli/tests/tools/project.rs`.

**Unclear in the decisions:** D3452 says "by name" but the file form can't
name a function, so a loose file's second program can't be run. Whether that
needs a form (item 2), or the answer is "put it in a project", is not decided.
The editor's "▶ Run" lens appears only above a definition called `main`
(`crates/lsp/src/lens.rs:91-101`, read from the syntax, which has no types);
lenses on other runnable functions would need type information, so they are
left alone. Both could wait for someone to want them.

## Sources

- Swift: [SE-0281, `@main`: Type-Based Program Entry Points](https://github.com/swiftlang/swift-evolution/blob/main/proposals/0281-main-attribute.md).
- Rust: [The Rust Reference, Crates and source files, "Main functions"](https://doc.rust-lang.org/reference/crates-and-source-files.html); [`#[tokio::main]`](https://docs.rs/tokio/latest/tokio/attr.main.html).
- Scala 3: [Main methods](https://docs.scala-lang.org/scala3/book/methods-main-methods.html).
- Haskell: [Haskell 2010 Report, chapter 5, Modules](https://www.haskell.org/onlinereport/haskell2010/haskellch5.html); [GHC User's Guide, `-main-is`](https://downloads.haskell.org/ghc/latest/docs/users_guide/phases.html).
- Lean 4: [Functional Programming in Lean, Running a Program](https://lean-lang.org/functional_programming_in_lean/Hello___-World___/Running-a-Program/); [its chapter summary, the three types of `main`](https://github.com/leanprover/fp-lean/blob/60624372e1b7f85967de2f9f2c906fb351e0469a/functional-programming-lean/src/hello-world/summary.md?plain=1).
- Unison: [Running programs](https://www.unison-lang.org/docs/usage-topics/running-programs/).
- Go: [The Go Programming Language Specification, Program execution](https://go.dev/ref/spec#Program_execution).
- C#: [Main() and command-line arguments](https://learn.microsoft.com/en-us/dotnet/csharp/fundamentals/program-structure/main-command-line).
- Effekt: [Tour, Hello World](https://effekt-lang.org/tour/hello-world); [Getting Started](https://effekt-lang.org/docs/getting-started).
- OCaml: [Your First OCaml Program](https://ocaml.org/docs/your-first-program).
- Koka: [The Koka book](https://koka-lang.github.io/koka/doc/book.html) (its entry-point section wasn't readable by my fetch; the Koka claims are marked unverified).
