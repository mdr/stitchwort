--| The `toyfmt` command line: `toyfmt [--check] [--width N] PATH...`.

namespace Toy.Fmt
import Std (Args, ExitStatus, Files, IO, List, Nat, Path, Result, Text)

--| What the command line asks for, and what `--help` says about it.
def program: Args.Program := { name = "toyfmt", about = "Formats Sprig files in place." }

--| The options: `--check`, `--width N`, and the paths to format.
def options: Args.Spec Options :=
  Args.Spec.start ((check: Bool) (width: Nat) (paths: List Path) => ({ check, width, paths }: Options))
    |> .and (Args.flag "check" (help := "Write nothing; list the files that would change, and fail if any would."))
    |> .and (Args.option "width" (default := defaultWidth) (metavar := "N") (help := "The widest a line may be."))
    |> .and (Args.arguments "PATH" (atLeast := 1) (help := "Files or folders to format."))

--| What a run says: on standard output, the paths it changed (or, with
--| `--check`, would); on standard error, every problem.
type Report = { changed: List Text, problems: List Text }

--| What the outcomes say.
def report (outcomes: List Outcome): Report := {
  changed = outcomes.filterMap (match
    | Formatted path Rewritten => Some "${path}"
    | Formatted path WouldChange => Some "${path}"
    | _ => None),
  problems = outcomes.filterMap (match
    | Problem message => Some message
    | _ => None)
}

--| Whether any path couldn't be formatted.
def hasProblem (outcomes: List Outcome): Bool := outcomes.any (match
  | Problem _ => True
  | _ => False)

--| The exit status of a run that wrote what it should and found nothing
--| wrong: 0.
def clean: ExitStatus := ExitStatus.success

--| The exit status of `--check` finding a file that would change: 1, as
--| `stitchwort fmt --check` does.
def wouldChange: ExitStatus := ExitStatus.failure

--| The exit status of a run where a path couldn't be read or parsed: 2, as
--| `stitchwort fmt` does (and as `Args.misuse` does for a bad command line).
def couldNotFormat: ExitStatus := ExitStatus.of 2

--| What the run exits with: a problem is 2, whatever else was found; else
--| `--check` finding a file to change is 1; else 0.
def status (options: Options) (outcomes: List Outcome): ExitStatus :=
  if hasProblem outcomes then couldNotFormat
  else if options.check
    && outcomes.any (match
      | Formatted _ WouldChange => True
      | _ => False) then
    wouldChange
  else clean

--| Formats the paths the options name: prints the report, and gives the
--| exit status `status` says.
def formatAll (options: Options): {Files, IO} ExitStatus :=
  let outcomes := formatPaths options options.paths
  let said := report outcomes
  said.changed.forEach IO.print
  said.problems.forEach IO.printError
  status options outcomes

--| Runs `toyfmt` on a command line: prints the help for `--help` (status 0),
--| exits 2 with the usage for a bad command line, and otherwise formats.
def run (arguments: List Text): {Files, IO} ExitStatus := Args.runStatusOn program options arguments formatAll

def main(): {Files, IO} ExitStatus := Args.runStatus program options formatAll
