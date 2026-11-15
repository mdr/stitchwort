# Exit statuses: how a program says 0, 1, 2 or 42

**Status:** design note, 15 November 2026 (SW-3345, after SW-3339's toy
formatter). Paper lane: nothing is built. It stops for Matt's decision
([§7](#7-question-for-matt)).

Claims are marked **[ran]** (a throwaway probe with the main checkout's
release binary), **[source]** (read in Stitchwort's code) or **[cited]**
(the language's or platform's own docs, linked in [§4](#4-other-languages)).

## 1. The problem

A Stitchwort program can end in only two ways that it chooses: it finishes
(status 0) or `main` fails through `Fail` (status 1). The runner adds a
third that the program doesn't choose: a runtime error, `E-IO` or
`E-RESOURCE`, is 2 [source: `run_main` in `crates/cli/src/main.rs`,
`report` in `crates/standalone/src/lib.rs`; `docs/guide/11-running-and-shipping.md`].
A `main` that returns anything but `()` is `E-MAIN-TYPE` [ran].

Real tools need more. `stitchwort fmt` itself exits 0 when everything is
formatted, 1 when `--check` finds a file it would change, and 2 when a file
can't be read or parsed [source: `fmt_command`]. The toy formatter can't
say that: both cases read 1, and only the message tells them apart
(`tools/toyfmt/NOTES.md`, friction 1). `Args.run` fails with status 1 on a
bad command line, where Unix programs conventionally use 2 [cited: Python's
`sys.exit` docs: "Unix programs generally use 2 for command line syntax
errors and 1 for all other kinds of errors"].

## 2. The options

**(a) `main` returns a status.** `def main(): {IO} ExitStatus`. The status
is a value, so it is just the program's result.

- *Nat, or a checked type?* POSIX passes only the low 8 bits to a parent
  that uses `wait` [cited]; Windows' `ExitProcess` takes a 32-bit `UINT`
  [cited]. So a plain `Nat` 256 means success on Linux and failure on
  Windows (Rust's docs give exactly this example for `exit(0x0100)`
  [cited]). A program that computes `256` and silently "succeeds" is the
  worst outcome. The fix is a type that only holds 0 to 255:

  ```
  type ExitStatus = { code: Nat, fits: code < 256 }
  def ExitStatus.of (code: Nat) [auto fits: code < 256]: ExitStatus := { code, fits }
  ```

  `ExitStatus.of 2` checks with no proof written; `ExitStatus.of 300` is a
  compile-time error; a computed code needs `if h: n < 256` [ran: `p1.sw`,
  `p2.sw`]. Today's message for 300 is ``[E-AUTO-FALSE] `False = True` is
  false``, which needs a better note (§6). The range is the same on every
  target, so a program's status doesn't depend on where it runs.
- Named values: `ExitStatus.success` (0), `.failure` (1), `.usage` (2, the
  command-line convention above).

**(b) An operation that ends the program:** an ability `Exit` with
`exit: ExitStatus → {Exit} Empty`, like `Fail.stop`. Any code can end the
program from deep inside. It is a library ability: a handler
`Exit.toStatus: (() → {Exit | e} ()) → {e} ExitStatus` turns it back into a
value, and it works today under `Files.simulate` [ran: `p1.sw`, test
"exit through Files.simulate"]. Its costs: `Exit` joins the row of every
function on the path ([ability-granularity.md](ability-granularity.md),
fact 5), and with a runner that performs it directly, the runners each need
a new bottom-of-run operation.

**(c) `Fail` carries a code**, `Fail.failWith 2 "can't parse"`. Changing
`Fail.stop`'s type, or adding an operation to `Fail`, breaks every handler
of `Fail` and every proof that takes a failing program apart
(ability-granularity.md, fact 1). It also mixes two things: "would change"
under `--check` is a verdict, not an error with a message.

**(d) A combination:** `main` returns `()` (status 0) or `ExitStatus`,
with `Fail` still giving 1; `Exit` from (b) as an optional library helper
on top, not known to the runner.

## 3. How each reads in the two motivating programs

The toy formatter with (a)/(d). Its loop already collects outcomes and
decides at the end, so the status is the last expression:

```
def formatAll (options: Options): {Files, IO} ExitStatus :=
  let outcomes := formatPaths options options.paths
  …print the report…
  if hasProblem outcomes then ExitStatus.of 2
  else if wouldChange options outcomes then ExitStatus.failure
  else ExitStatus.success

def main(): {Files, IO} ExitStatus := Args.run program options formatAll
```

`Args.run`'s body returns `ExitStatus`; `--help` gives `success`, a bad
command line prints the complaint to standard error and gives `usage` (2).
`Fail` drops out of the formatter's row: it was only there to make 1.

With (b) the same program writes `Exit.exit (ExitStatus.of 2)` where it
finds the problem, which stops at the first bad file. That is not what a
formatter wants (it reports every file), and neither motivating program
needs to stop early: both decide at the top. With (c), `Fail.failWith 1
"toyfmt: not formatted"` prints an `error:` line for what isn't an error.

## 4. Other languages

| | How a program sets its status | Ending early | Range noted |
|---|---|---|---|
| Rust | `main` returns a `Termination` type: `()`, `ExitCode`, `Result` | `process::exit`, which runs no destructors; the docs recommend returning `ExitCode` instead | `ExitCode::from(u8)`; "only the eight least-significant bits" on most Unix |
| Haskell | `exitWith (ExitFailure n)` | throws an exception that `Control.Exception` can catch; `bracket` clean-up runs | "operating-system dependent"; 0 may be prohibited for `ExitFailure` |
| Go | `os.Exit(code)` | immediate; deferred functions don't run | "should be in the range [0, 125]" for portability |
| Python | `sys.exit(arg)` | raises `SystemExit`; `finally` runs; can be intercepted | "most systems require it to be in the range 0–127" |
| Lean 4 | `main : IO UInt32` or `List String → IO UInt32` | — | — |
| Node.js | `process.exitCode = n` (preferred) or `process.exit(n)` | `exit` forces exit, pending output may be lost | not stated; Node itself uses 1 for an uncaught exception |
All [cited]. Swift, OCaml and Koka are left out: I couldn't verify their
forms in their docs in the time. The pattern: the languages that care about
clean-up and testing (Rust, Lean) make the status `main`'s result; the
early-exit forms are either abrupt (Go, Rust's `exit`) or an exception
(Haskell, Python), which in Stitchwort is an ability, i.e. (b).

Sources: Rust [`process::exit`](https://doc.rust-lang.org/std/process/fn.exit.html),
[`ExitCode`](https://doc.rust-lang.org/std/process/struct.ExitCode.html);
Haskell [`System.Exit`](https://hackage-content.haskell.org/package/base-4.22.0.0/docs/System-Exit.html);
Go [`os.Exit`](https://pkg.go.dev/os#Exit);
Python [`sys.exit`](https://docs.python.org/3/library/sys.html#sys.exit);
Lean, [Functional Programming in Lean, chapter summary](https://github.com/leanprover/fp-lean/blob/60624372e1b7f85967de2f9f2c906fb351e0469a/functional-programming-lean/src/hello-world/summary.md?plain=1);
Node [`process.exitCode`](https://nodejs.org/api/process.html#processexitcode_1);
POSIX [`exit`](https://pubs.opengroup.org/onlinepubs/9799919799/functions/exit.html);
Windows [`ExitProcess`](https://learn.microsoft.com/en-us/windows/win32/api/processthreadsapi/nf-processthreadsapi-exitprocess).

## 5. Recommendation: (d)

`main` may return `()` or `ExitStatus`; `Fail` unhandled stays 1, runtime
errors stay 2. Reasons:

- **Tests and proofs get it for free.** The status is the program's result,
  so every existing handler already reports it: `IO.simulate input prog`
  gives `(output, status)`, `Files.simulate disk prog` gives
  `(disk, status)`. "Exits 2 on unreadable input" is a test today's
  machinery states directly, and `theorem: (IO.simulate [] prog).snd.code
  = 2 := rfl` checks [ran]. Since `main` reads `IO.args()`, which the
  simulators leave empty, tests call the `run (arguments)` function that
  toyfmt already has.
- **No abrupt ending.** `docs/syntax.md` has no `finally`-style clean-up, but handlers between
  an operation and `main` are dropped when an unhandled operation reaches
  the runner, as `Fail` is today. A returned status drops nothing: a
  `Files.simulate` around the program still hands back its disk.
- **The type catches the 256 trap** at compile time, and the 0–255 range
  means the same on POSIX, Windows, Node and the playground.
- **Nothing breaks.** `()`-returning mains keep their meaning; no ability
  changes, so no handler or proof does.
- **(b) stays available** as a library helper when someone wants to stop
  from deep inside: `def main(): {IO} ExitStatus := Exit.toStatus body`.
  It needs no runner support, so it can wait for a program that asks.

**What each runner does** with a returned status:

| Runner | Today [source] | With (d) |
|---|---|---|
| `run` (machine, `--reference`, `--native`) | `Ok(())` → 0, `Failed` → 1, other errors → 2 | the status's code |
| `build`, `build --native` | the same, in `stitchwort_standalone::report` | the same |
| `run --js` | worker exits 72/71/70 to tell the CLI what happened, CLI maps them | the worker writes the status to the error file (codes 70–72 are taken), the CLI exits with it |
| Playground | prints `error: msg` for `Fail` | a nonzero status shows a line `exit status 2` below the output |

`stitchwort run` itself also exits 1 when the program doesn't check, so
under `run` a status of 1 is ambiguous; a built executable has no such
case. That is the same as today with `Fail`.

**The runner's own 2.** A program's chosen 2 and a runtime error's 2 look
the same to the shell. For a formatter both mean "couldn't do the job", so
I would leave it; moving runtime errors to a code of their own (say 70)
can be decided later if a program needs to tell them apart.

**The `main` check.** `main_calls` [source: `crates/driver/src/run.rs`]
tries each row with result `()`; it would also try `Std.ExitStatus`, and
`MainRow` (or `Main`) records which. `E-MAIN-TYPE`'s message becomes "…
returning `()` or `ExitStatus`".

## 6. Stages

1. **`ExitStatus` and the runners** (Sonnet, about 2.5 h): the std type in
   its own namespace, with `success`, `failure`, `usage`, `of`, `Show` and
   `==`; `main` returning it under `run`, `--reference`, `--native`,
   `--js`, `build` (both) and the playground; `E-MAIN-TYPE`'s message; a
   better note when `ExitStatus.of n` gets a code over 255 ("exit statuses
   are 0 to 255"); examples (`examples/accept/main-exit-status.sw`, a
   CLI test per runner that a program exits 3); `docs/syntax.md`, the
   guide's chapter 11 and its exit-code paragraph. Sonnet, not DeepSeek:
   it touches six runners in five crates.
2. **`Args.run` and toyfmt** (Sonnet or DeepSeek, about 1 h): `Args.run`'s
   body returns `ExitStatus`, a bad command line is `usage` (2) with the
   complaint on standard error; the guide's `args.sw`; toyfmt exits 0/1/2
   with a test per status through `run`, and NOTES friction 1 closed.
3. **`Exit` in std** (DeepSeek, about 45 min), only when a program wants to
   stop early: the ability and `Exit.toStatus`, with a test under
   `Files.simulate`.

## 7. Question for Matt

**D3616: should `main` be able to return an exit status, as a checked
`ExitStatus` (0 to 255) rather than a plain `Nat`? [rec: yes]**

- **The problem.** A program can only exit 0 or 1 (through `Fail`). Tools
  need more: the toy formatter can't say "would change" (1) apart from
  "couldn't read the file" (2) as `stitchwort fmt` does, and a bad command
  line should be 2.
- **The change.** `def main(): {Files, IO} ExitStatus := …` alongside
  today's `()`. `ExitStatus.of 2`, `ExitStatus.success` and so on; a code
  over 255 is refused when the program is checked, because a plain number
  256 would mean success on Linux and failure on Windows. `Fail` still
  gives 1. An `Exit.exit` operation for stopping from deep inside can be a
  library helper later.
- **What it should do.** The toy formatter's `main` ends with a three-way
  `if` and exits 0, 1 or 2, as the Rust formatter does; `Args.run` exits 2
  on a bad command line; a test states "exits 2 on unreadable input" as
  `(…simulate… (run ["missing.sw"])).snd == ExitStatus.of 2`, with no new
  test machinery. Estimated 3.5 h in two Sonnet lanes; no existing program
  changes.

## Decision (D3616, Matt, 15 Nov 2026)

"Yes, with Fin and just success and failure." `ExitStatus` wraps std's
`Fin 256` instead of a hand-rolled bound: `type ExitStatus = { code: Fin 256 }`,
with `ExitStatus.of` through `Fin.ofNat`'s automatic proof (`Fin` runs as a
machine number, nat-shaped-types.md stages 1-2). std names only
`ExitStatus.success` (0) and `ExitStatus.failure` (1): 0 is the one rule
([POSIX exit](https://pubs.opengroup.org/onlinepubs/9799919799/functions/exit.html)
gives other values no meaning), while 2 for misuse is a convention
([Bash](https://www.gnu.org/software/bash/manual/html_node/Exit-Status.html),
argparse, Go `flag`) with a deprecated rival, `EX_USAGE` 64
([sysexits(3)](https://man.freebsd.org/cgi/man.cgi?query=sysexits&sektion=3)).
Programs name their own codes; `Args.run` documents its 2. Stages: SW-3402, SW-3403.
