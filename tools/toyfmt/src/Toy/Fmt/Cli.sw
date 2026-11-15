--| The `toyfmt` command line: `toyfmt [--check] [--width N] PATH…`.

namespace Toy.Fmt
import Std (Fail, Files, IO, List, Nat, Path, Result, Text)

--| The usage line, which every bad command line is answered with.
def usage: Text := "usage: toyfmt [--check] [--width N] PATH..."

--| The options the arguments give, or what is wrong with them.
def parseArguments: (arguments: List Text) → (options: Options) → Result Options Text
  | [], options => if options.paths.isEmpty then Err "${usage}: no paths given" else Ok options
  | ["--check", ..rest], options => parseArguments rest { options | check = True }
  | ["--width"], options => Err "${usage}: --width needs a number"
  | ["--width", number, ..rest], options =>
    match number.toNat with
      | Some width => parseArguments rest { options | width }
      | None => Err "${usage}: --width wants a whole number, got '${number}'"
  | [flag, ..rest], options =>
    if flag.startsWith "-" then Err "${usage}: unknown flag ${flag}"
    else parseArguments rest { options | paths = options.paths ++ [flag.toPath] }

--| The options for a command line, before any path is given.
def Options.start: Options := { check = False, width = defaultWidth, paths = [] }

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

--| Runs `toyfmt` on a command line: prints the report, and fails (exit
--| status 1) for a bad command line, a problem, or a file `--check` would
--| change.
def run (arguments: List Text): {Files, IO, Fail} () := match parseArguments arguments Options.start with
  | Err message => Fail.fail message
  | Ok options =>
    let outcomes := formatPaths options options.paths
    let said := report outcomes
    said.changed.forEach IO.print
    said.problems.forEach IO.printError
    Fail.ensure (!failed options outcomes) (if hasProblem outcomes then "toyfmt: problems" else "toyfmt: not formatted")

def main(): {Files, IO, Fail} () := run IO.args()
