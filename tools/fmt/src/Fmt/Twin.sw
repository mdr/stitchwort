--| The stage 0 stub of the self-hosted formatter
--| (docs/proposals/self-hosted-fmt.md §6, §8): the command line `task fmt:twin`
--| drives, `fmt --stage STAGE FILE`, with every stage's answer being the file as
--| it is. Under `--stage text` that is a formatter that changes nothing, so it
--| is right on a formatted file and wrong on any other. The real stages replace
--| it one by one.
namespace Fmt.Twin
import Std (Args, ExitStatus, Files, IO, List, Path, Text)

--| What the command line asks for: the stage whose answer to print, and the
--| file to read.
type Options = { stage: Text, files: List Path }

def program: Args.Program :=
  { name = "fmt", about = "The comparison harness's formatter: prints a stage's answer for a file." }

def options: Args.Spec Options :=
  Args.Spec.start ((stage: Text) (files: List Path) => ({ stage, files }: Options))
    |> .and
      (Args.option "stage" (default := "text") (metavar := "STAGE") (help := "tokens, tree, refusal, passes or text."))
    |> .and (Args.arguments "FILE" (atLeast := 1) (help := "The files to answer for, one after another."))

--| The answer of the stub for one file: its text, for every stage.
def answer (path: Path): {Files, IO} Bool := match Files.read path with
  | Ok source =>
    IO.write source
    True
  | Err error =>
    IO.printError "${path}: ${error}"
    False

--| Prints each file's answer; exits 2 if any file couldn't be read.
def run (options: Options): {Files, IO} ExitStatus :=
  if options.files.map answer |> .all (ok => ok) then ExitStatus.success else ExitStatus.of 2

def main(): {Files, IO} ExitStatus := Args.runStatus program options run
