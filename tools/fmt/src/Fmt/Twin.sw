--| The self-hosted formatter's command line for the comparison harness
--| (docs/proposals/self-hosted-fmt.md §6, §8), `fmt --stage STAGE FILE`,
--| which `task fmt:twin` drives. Each stage prints its answer in the Rust
--| side's form:
--|
--| - `tokens`: the tokens with trivia after rule N, as `stitchwort dev
--|   tokens` prints them, or for a file that doesn't lex, `error: MESSAGE`
--|   on standard error and status 1.
--| - the later stages are still the stage 0 stub: the file as it is.
--|
--| `--batch LIST` answers for every path in LIST (one per line) in one run,
--| each block being `\u{1e}PATH` on its own line, then
--| `\u{1f}STATUS\u{1f}LENGTH\u{1f}MESSAGE` on the next, then exactly LENGTH
--| characters of standard output. STATUS is the status single-file mode would
--| exit with, and MESSAGE the first line it would write to standard error.
namespace Fmt.Twin
import Std (Args, ExitStatus, Files, IO, List, Nat, Option, Path, Result, Text)
import Syntax (Lexed, lex)

--| What the command line asks for: the stage whose answer to print, the file
--| to read, or a LIST of files to answer for in one run.
type Options = { stage: Text, batch: Option Path, files: List Path }

def program: Args.Program :=
  { name = "fmt", about = "The comparison harness's formatter: prints a stage's answer for a file." }

def options: Args.Spec Options :=
  Args.Spec.start ((stage: Text) (batch: Option Path) (files: List Path) => ({ stage, batch, files }: Options))
    |> .and
      (Args.option "stage" (default := "text") (metavar := "STAGE") (help := "tokens, tree, refusal, passes or text."))
    |> .and
      (Args.optional "batch" (metavar := "LIST") (help := "A file of paths, one per line, to answer for in one run."))
    |> .and (Args.arguments "FILE" (atLeast := 0) (help := "The files to answer for, one after another."))

--| A stage's answer for one file: its standard output, the status single-file
--| mode exits with, and the first line it writes to standard error (if any).
type Answer = { out: Text, status: Nat, message: Text }

--| A stage's answer for a file's text.
def stageAnswer (stage source: Text): Answer := match stage with
  | "tokens" =>
    match lex source with
      | Ok lexed => { out = lexed.settled.dump, status = 0, message = "" }
      | Err message => { out = "", status = 1, message = "error: ${message}" }
  | _ => { out = source, status = 0, message = "" }

--| A stage's answer for one file.
def answerOf (stage: Text) (path: Path): {Files} Answer := match Files.read path with
  | Ok source => stageAnswer stage source
  | Err error => { out = "", status = 2, message = "${path}: ${error}" }

--| Prints one file's answer by itself: standard output, or the message on
--| standard error, and whether it succeeded.
def answer (stage: Text) (path: Path): {Files, IO} Bool :=
  let answer := answerOf stage path
  if answer.status == 0 then IO.write answer.out else IO.printError answer.message
  answer.status == 0

--| One batch block: the path's own line, the metadata line, then the answer.
def block (path: Path) (answer: Answer): Text :=
  "\u{1e}${path}\n\u{1f}${answer.status}\u{1f}${answer.out.length}\u{1f}${answer.message}\n"

--| Prints one file's answer as a batch block. A refusal is in the block, not
--| the process's exit status, so it doesn't stop the files after it.
def batchAnswer (stage: Text) (path: Path): {Files, IO} () :=
  let answer := answerOf stage path
  IO.write (block path answer)
  IO.write answer.out

--| Answers for every path in LIST, one per line. Blank lines are ignored.
def runBatch (stage: Text) (list: Path): {Files, IO} ExitStatus := match Files.read list with
  | Err error =>
    IO.printError "${list}: ${error}"
    ExitStatus.of 2
  | Ok text =>
    let paths := text.lines.filter (line => !line.trim.isEmpty) |> .map (line => line.toPath)
    paths.forEach (batchAnswer stage)
    ExitStatus.success

--| Prints each file's answer; exits 2 if any file couldn't be read. With
--| `--batch`, one process answers for every path in the list.
def run (options: Options): {Files, IO} ExitStatus := match options.batch with
  | Some list => runBatch options.stage list
  | None =>
    if options.files.isEmpty then
      IO.printError "fmt: missing FILE (or --batch LIST)"
      ExitStatus.of 2
    else
      let answers := options.files.map (answer options.stage)
      if answers.all (ok => ok) then ExitStatus.success
      else if options.stage == "tokens" then ExitStatus.of 1
      else ExitStatus.of 2

def main(): {Files, IO} ExitStatus := Args.runStatus program options run
