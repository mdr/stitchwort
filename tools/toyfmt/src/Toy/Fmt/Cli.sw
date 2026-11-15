--| The `toyfmt` command line: `toyfmt [--check] [--width N] PATH...`.

namespace Toy.Fmt
import Std (Args, Fail, Files, IO, List, Nat, Path, Result, Text)

--| What the command line asks for, and what `--help` says about it.
def program: Args.Program := { name = "toyfmt", about = "Formats Sprig files in place." }

--| The options: `--check`, `--width N`, and the paths to format.
def options: Args.Spec Options :=
  Args.Spec.start ((check: Bool) (width: Nat) (paths: List Path) => ({ check, width, paths }: Options))
    |> .and (Args.flag "check" (help := "Write nothing; list the files that would change, and fail if any would."))
    |> .and (Args.option "width" (default := defaultWidth) (metavar := "N") (help := "The widest a line may be."))
    |> .and (Args.arguments "PATH" (atLeast := 1) (help := "Files or folders to format."))

--| What a run says: on standard output, the paths it changed (or, with
--| `--check`, would); on standard error, every problem and each file with
--| declarations left as written.
type Report = { changed: List Text, problems: List Text }

--| What the outcomes say.
def report (outcomes: List Outcome): Report := {
  changed = outcomes.filterMap (match
    | Formatted path Rewritten _ => Some "${path}"
    | Formatted path WouldChange _ => Some "${path}"
    | _ => None),
  problems = outcomes.filterMap (match
    | Problem message => Some message
    | Formatted path _ asWritten =>
      if asWritten == 0 then None else Some "${path}: ${asWritten} declarations left as written")
}

--| Whether any path couldn't be formatted.
def hasProblem (outcomes: List Outcome): Bool := outcomes.any (match
  | Problem _ => True
  | _ => False)

--| Whether the exit status should say so: something went wrong, or
--| `--check` found a file to change. (A program can exit with 0 or 1 only.)
def failed (options: Options) (outcomes: List Outcome): Bool := outcomes.any (match
  | Problem _ => True
  | Formatted _ WouldChange _ => options.check
  | _ => False)

--| Formats the paths the options name: prints the report, and fails (exit
--| status 1) for a problem or a file `--check` would change.
def formatAll (options: Options): {Files, IO, Fail} () :=
  let outcomes := formatPaths options options.paths
  let said := report outcomes
  said.changed.forEach IO.print
  said.problems.forEach IO.printError
  Fail.ensure (!failed options outcomes) (if hasProblem outcomes then "toyfmt: problems" else "toyfmt: not formatted")

--| Runs `toyfmt` on a command line: prints the help for `--help`, fails
--| (exit status 1) with the usage for a bad command line, and otherwise
--| formats.
def run (arguments: List Text): {Files, IO, Fail} () := Args.runOn program options arguments formatAll

def main(): {Files, IO, Fail} () := Args.run program options formatAll
