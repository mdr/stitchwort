# `Std.Args`: a command-line library (SW-3378)

**Status:** draft 1, 15 November 2026. Stage A1 built (§11); A2 dropped (D3614). Open
decisions: D3614, D3615 ([§9](#9-questions-for-matt)). Claims are marked
**[ran]** (probed with the release CLI, scratchpad `sw3378/`), **[read]**
(in this repo's code or docs), **[cited]** (another library's docs, linked).

## 1. In plain words

**The problem.** Every Stitchwort program that takes options parses
`IO.args()` by hand. toyfmt's `Cli.sw` is about 15 lines of list patterns for three
options, and still has no `--width=80`, no `--` (so it can't format a file
called `-x`), no `--help`, and a usage line kept in step with the code by
hand [read]. The self-hosted formatter needs `stitchwort fmt`'s options next,
and every later tool will write the same loop with its own error wording.

**The change.** A standard library module, `Std.Args`. A program describes
its options once, as a record whose fields are the options (their names,
types, defaults and help), and gets from that: the parser, the usage line,
`--help`, and exact error messages as values. Underneath is a small set of
combinators that the record form is built from, which can also be used
directly. Parsing is a pure function of a `List Text`, so tests need no IO.

**What it should do.** toyfmt's command line drops from about 15 lines of
parsing plus a hand-kept usage string to a 9-line record [estimated, §6]; it
gains `--width=80`, `--`, `--help` and suggestions for misspelt options for
free; every Stitchwort tool answers a bad command line in the same words.

## 2. The command line it accepts

GNU-style long options, the convention `stitchwort` itself follows (clap):

- `--check` (a flag); `--width 80` and `--width=80` (an option with a value);
  `--keep A --keep B` (repeated, for a list field); options and positional
  arguments in any order.
- `--` ends the options: everything after it is a positional argument,
  verbatim. A lone `-` is a positional argument (standard input, as `fmt -`
  uses it).
- `--help` (and `-h`) prints the help on standard output and runs nothing.
- Short names (`-w 80`, `-w80`, bundled `-cq`) only where an option asks for
  one (stage 3). No prefix abbreviations (argparse allows unambiguous ones by default,
  [cited: `allow_abbrev`](https://docs.python.org/3/library/argparse.html)): adding an option could break a script.
- A non-repeating option given twice is an error, not "last wins": nothing
  is dropped silently. `--check=yes` is an error too.

## 3. How a program declares its options

### 3.1 The record form (the one people write)

```
--| Formats Sprig files in place.
@[args.command "toyfmt"]
type Options = {
  --| Write nothing; list the files that would change, and fail if any would.
  check: Bool := False,
  --| The widest a line may be.
  @[args.metavar "N"] width: Nat := defaultWidth,
  --| Files or folders to format.
  @[args.positional] paths: NonEmptyList Path,
}
```

The field's **name** is the option (`fieldName` becomes `--field-name`), its
**type** says what kind of option it is, its **default** makes it optional,
and its `--|` doc is its **help**:

| Field type | Option | Without the option |
|---|---|---|
| `Bool` | a flag | its default (must be `False`; a `True` default gives `--no-x`, stage 3) |
| `T` (an `Args.Value T`) | `--x VALUE` | its default, or "missing --x" |
| `Option T` | `--x VALUE` | `None` |
| `List T` | repeatable `--x VALUE` | `[]` |
| `@[args.positional] T`, `Option T`, `List T`, `NonEmptyList T` | positional | required one, optional one, any number, at least one |
| `@[args.subcommand] C` (C a data type of records) | a subcommand (stage 3) | "missing command" |

`Args.Value` is an interface, `{ read: Text → Result a Text, show: a → Text,
metavar: Text }`, with instances for `Text`, `Nat`, `Int`, `Float` and
`Path`, and `Args.choice` (a named alternative) for any type with derived
`Finite` and `Show`, so `type Colour = | Auto | Always | Never` reads
`--colour always` and lists the choices in help and errors. The record's
own doc is the help's description; `@[args.command "NAME"]` opts it in.
Other attributes: `args.metavar`, `args.name "in"` (`search --in`: `in` is
a keyword), `args.short "w"`, `args.hidden`.

**This needs language support** [read: `crates/elab/src/derive*.rs`].
Stitchwort has no reflection over a record's fields, and isn't getting it
here. Instead the compiler derives an instance `Args.Command Options` from
the declaration, the same way it derives `Show` today: it generates source
that calls the combinators of §3.2, so the derived code is ordinary,
inspectable and provable. Opt-in by attribute, not automatic as D3609 makes
`==`: almost no record is a command line. One catch: help from `--|` docs
means docs reach a program's output, and today docs are outside
elaboration, hashes and the check cache's key [read: docs/syntax.md, "Doc
comments"]. The generated instance's hash would follow the help text, but
the cache key must then cover those records' docs too (D3615).

### 3.2 The combinators (the layer underneath)

```
def options: Args.Spec Options :=
  Args.start ((check: Bool) (width: Nat) (paths: List Path) => ({ check, width, paths }: Options))
    |> .and (Args.flag "check" (help := "Write nothing; list the files that would change"))
    |> .and (Args.option "width" (default := defaultWidth) (metavar := "N") (help := "The widest a line may be"))
    |> .and (Args.arguments "PATH" (atLeast := 1) (help := "Files or folders to format"))
```

`Args.Spec a` is a record, `{ options: List Args.Info, read: Args.Found →
Result a Args.Error }`, and `.and` is applicative application, as in
optparse-applicative and cmdliner (§7). No existential types are needed: a
prototype of this shape checks and its tests pass [ran: `Probe.sw`,
`P2.sw`]. Its weakness is the one optparse-applicative has: the lambda's
parameters must be in the same order as the `.and`s, which is easy to get
wrong past five options, and the names and help sit apart from the record.
The lambda's parameter types must be written today: an unannotated lambda
there is `E-TYPE-MISMATCH` ("this is a function, but the expected type is
`?0`") [ran], a finding for the postponement work (§10).

**Why not on `Parse`.** `Parse.tokens` (generic-parse.md stage 2) reads
tokens in sequence; a command line is options in any order plus positionals,
which on `Parse` is a permutation parser: more machinery, worse errors.
`Args` makes one pass: each argument becomes `Long name (Option value) |
Short chars | Plain text` (all `Plain` after `--`), matched against the spec
into `Args.Found`, then `read` runs. A `Value` may use `Parse` on one value.

## 4. Results, errors and exit codes

```
type Args.Outcome (a: Type) = | Run a | Help Text | Wrong Args.Error
def Args.parse [auto c: Args.Command a] (arguments: List Text): Args.Outcome a
def Args.parseWith (spec: Args.Spec a) (arguments: List Text): Args.Outcome a
def Args.run [auto Args.Command a] (body: a → {IO, Fail | e} ()): {IO, Fail | e} ()
```

`Args.run` reads `IO.args()`; for `Help` it prints to standard output and
returns (exit 0); for `Wrong` it prints to standard error and fails; for
`Run` it calls `body`. `Args.Error` is a data type, so tests compare values:

| Constructor | `describe` (after `toyfmt: `) |
|---|---|
| `Unknown "--widht" (Some "--width")` | `unknown option --widht (did you mean --width?)` |
| `NeedsValue "--width" "N"` | `--width needs a value (N)` |
| `BadValue "--width" "x" "a whole number"` | `--width wants a whole number, got 'x'` |
| `TakesNoValue "--check" "yes"` | `--check takes no value, got '--check=yes'` |
| `Repeated "--width"` | `--width is given twice` |
| `Missing "PATH"` / `Missing "--name"` | `missing PATH` / `missing --name` |
| `Unexpected "b.sw"` | `unexpected argument 'b.sw'` |
| `UnknownCommand "chek" ["check", "fmt"]` | `unknown command 'chek' (commands: check, fmt)` |

Printed as three lines: the message, the usage line, `Run 'toyfmt --help'
for more.` **Exit codes:** clap, argparse and Go's `flag` all exit 2 for a
bad command line and 0 for help [cited: §7]; cmdliner uses 124 for command-line errors ([Cmd.Exit](https://erratique.ch/software/cmdliner/doc/Cmdliner/Cmd/Exit/index.html): "cli_error is 124").
Stitchwort programs can exit only 0 or 1 today (SW-3345), so `Wrong` exits
1 until SW-3345 lands, then 2. Nothing else in `Args` waits on it.

Help, generated from the spec, wrapped to 80 columns:

```
usage: toyfmt [--check] [--width N] PATH...
Formats Sprig files in place.

arguments:
  PATH...     Files or folders to format.
options:
  --check     Write nothing; list the files that would change, and fail if any would.
  --width N   The widest a line may be. (default: 80)
  -h, --help  Show this help.
```

Defaults are shown with the value's `show`. `Args.Spec.problems` lists a
spec's mistakes (a name used twice, a list positional before another); the
derived instance reports them at compile time (`E-ARGS`).

## 5. Testability and proofs

`Args.parse` is pure, so a program's command line is tested with plain
`test`s on lists of text, as toyfmt's are today [read:
`Tests/Driver.sw:108-115`]. Proofs worth having, in std, about every spec:

- **Help lists every option:** `info ∈ spec.options → (Args.help
  spec).contains info.long`. Cheap, and it is the promise users rely on.
- **`--` passes through:** everything after the first `--` reaches the
  positionals unchanged, in order (so a file named `-x` is always reachable).
- **Round trip** (stage 4, harder): `Args.render [Options] x` writes a
  command line (each value as `--name=show v`, positionals after `--`), and
  `Args.parse (Args.render x) = Run x`, given each field's `Args.Value`
  round-trips (`read (show v) = Ok v`; a separate theorem per instance,
  since `Path`'s holds only for normal paths). It needs the derived form:
  the combinators can't take a value apart again. Useful for tools that
  start each other, and for fuzzing.

## 6. toyfmt with `Args`, and `fmt`'s options

toyfmt: the record of §3.1 replaces `usage`, `parseArguments` and
`Options.start` (`Options` moves from `Driver.sw` to `Cli.sw`; `paths`
becomes `NonEmptyList Path`, so "no paths given" can't happen past parsing):

```
def run (options: Options): {Files, IO, Fail} () :=
  let outcomes := formatPaths options options.paths.toList
  …                                         -- unchanged
def main(): {Files, IO, Fail} () := Args.run run

test "a bad width" := Args.parse [a := Options] ["--width", "x", "a"]
  == Wrong (BadValue "--width" "x" "a whole number")
```

The self-hosted formatter's `fmt` (crates/cli `Command::Fmt` [read]):

```
--| Formats source files in place: indentation, spacing, blank lines and
--| brackets, in the house style. Prints the files it changed.
@[args.command "fmt"]
type FmtOptions = {
  --| Files (`.sw`) or folders to format; `-` reads standard input and
  --| writes standard output. None: the project's sources.
  @[args.positional, args.metavar "FILE"] files: List Path,
  --| Write nothing; list the files that would change, and fail if any would.
  check: Bool := False,
  --| The project folder, if not the folder you're in or the nearest one above it.
  project: Option Path := None,
}
```

All of `stitchwort`'s shape fits once subcommands exist: a data type
`Command = | Check CheckOptions | Fmt FmtOptions | …` marked
`args.subcommand` in a top record holding the global options (`--std-dir`).
`check --only A,B` wants a separator on a list (`args.separator ","`);
clap's `conflicts_with`/`requires` ([`Arg`](https://docs.rs/clap/latest/clap/struct.Arg.html)) have no equivalent here: a program
checks those itself after parsing, or models them as a data type field.

## 7. Other libraries [cited]

| Library | Declared by | Notes |
|---|---|---|
| Rust clap, derive | struct fields; `bool` is a flag, `Option<T>` optional, `Vec<T>` repeated; doc comments are help; `default_value_t` | [docs.rs/clap/latest/clap/_derive](https://docs.rs/clap/latest/clap/_derive/index.html). Usage errors exit 2, help 0 ([Error::exit](https://docs.rs/clap/latest/clap/error/struct.Error.html)) |
| Rust clap, builder | values built in code; the derive generates them | same crate: the derive API sits on the builder, and raw attributes are forwarded to builder methods ([derive docs](https://docs.rs/clap/latest/clap/_derive/index.html)) |
| Python argparse | `add_argument` calls | `--foo=bar` and `--foo bar`; `--` ends options; unambiguous prefixes by default; invalid arguments exit 2 ([docs](https://docs.python.org/3/library/argparse.html)); `-h` exits 0 (`_HelpAction` calls `parser.exit()`, whose status defaults to 0: [`Lib/argparse.py`](https://github.com/python/cpython/blob/main/Lib/argparse.py)) |
| Haskell optparse-applicative | applicative `<$>`/`<*>`; `help`, `value`, `showDefault` | options "parsed in whatever order they appear" ([README](https://github.com/pcapriotti/optparse-applicative)) |
| Go flag | one call per flag | `-flag`/`--flag`, `-flag=x`, `-flag x` except booleans; parsing stops at the first non-flag; exit 2, help 0 ([pkg.go.dev/flag](https://pkg.go.dev/flag)) |
| Swift ArgumentParser | a type's properties with `@Option`/`@Flag`/`@Argument(help:)`; defaults are initial values; `subcommands: [...]` | [README](https://github.com/apple/swift-argument-parser), [math example](https://github.com/apple/swift-argument-parser/blob/main/Examples/math/Math.swift) |
| OCaml cmdliner | terms combined with `let+ … and+`; `Arg.info ~doc ~docv` | generates help and man pages ([tutorial](https://erratique.ch/software/cmdliner/doc/tutorial.html)); CLI errors exit 124 ([Cmd.Exit](https://erratique.ch/software/cmdliner/doc/Cmdliner/Cmd/Exit/index.html)) |

Two families, the shapes of §3: declarations on a type (clap derive, Swift)
and applicative values (optparse-applicative, cmdliner, clap's builder).
clap has both, the declared form generated into the other.

## 8. Stages

| Stage | What | Model | Estimate |
|---|---|---|---|
| A1 | `Std.Args` combinators: `Spec`, `flag`, `option`, `many`, `optional`, `arguments`, `Value` and its instances, `choice`; the parser (`--x=v`, `--`, `-`, `--help`); `Outcome`, `Error.describe`, usage and help; `Args.run`; tests; guide page and docs/syntax.md | Sonnet | 3–4 h |
| A2 | Derived `Args.Command` for `@[args.command]` records: `derive_args`, the `args.*` attributes, help from `--|` docs and the cache key (D3615), `E-ARGS`; toyfmt moved onto it | Opus | 4–6 h |
| A3 | Subcommands (combinator and derived), short names and bundling, `--no-x`, did-you-mean (needs a `Text.editDistance` in std; none exists [read]) | Sonnet | 3 h |
| A4 | Proofs: help lists every option, `--` passes through; `Args.render` and the round-trip theorem | Sonnet, Opus for round trip | 2–4 h |

If D3614 is combinators only, A2 is dropped and toyfmt moves in A1. The
self-hosted formatter can use `Args` from A1 (it needs no subcommands).

## 9. Questions for Matt

**D3614: do people declare options as a record (generated by the
compiler), with the combinators underneath?** *The problem:* the
combinators alone work today with no language change, but the user lists
the options twice (a constructor lambda, then one `.and` per option, in the
same order), with the help apart from the field. *The change:* the compiler
derives the combinator code from a record marked `@[args.command]`: field
name, type, default and doc become the option. This is new compiler work (a
derived instance and an attribute family, about 5 h of Opus) rather than a
library. *What it should do:* a command line is one record that reads like
its `--help`; toyfmt's 15 lines become 9 [estimated]; the record form can
round-trip (§5), which the combinators can't. **[rec: yes, both: combinators
in A1, records in A2]**

**D3615 (only if D3614 is yes): does a record option's help come from its
`--|` doc?** *The problem:* help text has to be written somewhere; docs are
today never part of what a program does or of its cache key. *The change:*
for `@[args.command]` records only, the field's `--|` doc is its help (as
clap and the record's own reader expect), and the check cache's key covers
those docs; the alternative is an `@[args.help "…"]` attribute on every
field, which doubles the text. *What it should do:* help is written once, in
the place `stitchwort doc` already shows it; editing it reruns the tests
that print it. **[rec: yes]**

## 10. Findings

- An unannotated lambda passed to a generic parameter that only a later
  pipe fixes (`Spec.pure (a b => …) |> .and …`) is `E-TYPE-MISMATCH`
  against `?0`, where a record literal in the same place waits
  (postponement.md stage 2) [ran]. Worth a ticket: lambdas could wait too.
- SW-3263 (`IO.args` to its own ability) changes only `Args.run`'s row.

## 11. As built, stage A1 (SW-3381, 15 November 2026)

D3614 (Matt): the combinators only, as pure library code; the record form
(A2), D3615 and attributes are dropped for now (the general mechanism is
SW-3382). `crates/elab/src/std/Args/Args.sw` is `Std.Args`; its tests are
in the same file.

**Differences from §3 and §4:**

- `Args.start` is `Args.Spec.start`, so that `.and` finds `Args.Spec.and`.
  `Args.Spec` holds `items: List Args.Info` (not `options`; positionals are
  items too) and `read`. The lambda given to `Spec.start` needs its
  parameter types written (SW-3379), as the design said; the guide and the
  doc comment say so.
- The combinators: `flag`, `option` (needs a `default`), `required`,
  `optional`, `many`, `arguments metavar (atLeast := n)`. `option`'s
  `metavar` defaults to the type's own (`N`, `TEXT`, `PATH`, `CHOICE`).
- `Args.parse` takes a `Args.Program` (`{ name, about := "" }`), because the
  help it returns names the program: `Args.parse program spec arguments`.
  There is no `Args.parseWith`/`[auto Args.Command]` (that was the derived
  form). `Args.runOn program spec arguments body` is `Args.run`'s core with
  the list given, so a program's `run` can be tested; `Args.run` passes
  `IO.args()`.
- `Args.Value` has instances for `Text`, `Nat`, `Int` and `Path`;
  `Args.choice` builds one for a `Finite` and `Show` type (the error lists
  the choices: `--colour wants one of Red, Green, Blue, got 'Pink'`). There
  is no `Float` instance yet.
- Constructors of `Args.Error`, `Args.Outcome` and the rest are written in
  full or imported (`import Std.Args.Outcome (Run, Help, Wrong)`). `Unknown`
  clashes with `Terminal.Key`'s constructor inside std, so std itself writes
  `Args.Error.Unknown`; a program may import it.
- `Unknown`'s suggestion is only the one option the mistyped name is a prefix
  of (`--wid` gives `--width`); there is no edit distance (A3).
- `Wrong` exits 1: `Args.run` fails with the whole complaint, three lines:
  `NAME: message`, `usage: ...`, `Run 'NAME --help' for more.` The runner
  prefixes `error: `.
- `--help`/`-h` is recognised where an option would be (not as the value of
  an option, and not after `--`) and wins over a mistake that comes after
  it, as a mistake before it wins. The first mistake in the command line is
  reported; then missing or bad values, in the order of the spec.
- Help wraps descriptions at 80 columns under the description column, so a
  long help line is two lines (the §4 sample had one 85 characters long).
  A help text is written with its full stop; `(default: X)` follows it.
- A spec may have one positional item (`arguments`); a second is reported by
  `Args.problems`, not refused when it is built. `problems` also reports an
  option name used twice and `help`/`h`. It isn't checked by `parse`: a
  program's tests assert `Args.problems spec == []`.
- Proofs: `Args.scanAfterDashes` (everything after `--` reaches the
  positionals unchanged, in order) and `Args.Spec.andItems`, both by `rfl`.
  "Help lists every option" is not proved: it needs lemmas about
  `Text.contains` over `joinWith` and the wrapping that std doesn't have yet;
  the tests check it on the example specs.

**toyfmt** (`tools/toyfmt/src/Toy/Fmt/Cli.sw`) is now one spec of 4 lines
and `Args.runOn`; `Options` stays in `Driver.sw`. It gains `--width=N`, `--`
and `--help`. What changed in its messages: "no paths given" is
`missing PATH`, "unknown flag --wide" is `unknown option --wide`, "--width
needs a number" is `--width needs a value (N)`, and each is followed by the
usage line and the `Run 'toyfmt --help' for more.` line instead of being
prefixed by the usage line. Its unit tests and the end-to-end test (which
checks that stderr has `usage: toyfmt`) hold.
