--| The self-hosted formatter's command line for the comparison harness
--| (docs/proposals/self-hosted-fmt.md §6, §8), `fmt --stage STAGE FILE`,
--| which `task fmt:twin` drives. Each stage prints its answer in the Rust
--| side's form:
--|
--| - `tokens`: the tokens with trivia after comment placement, as `stitchwort dev
--|   tokens` prints them, or for a file that doesn't lex, `error: MESSAGE`
--|   on standard error and status 1.
--| - `expr` (stage 2a): the file read as one expression, its tree as
--|   `stitchwort dev tree --expression` prints it, or `error: MESSAGE` on
--|   standard error and status 1 if it doesn't parse.
--| - `tree` (stage 2b): the file's tree as `stitchwort dev tree --print`
--|   prints it, without its header and totals. A file with a declaration
--|   that doesn't parse (an `Error` node there) is answered with status 1
--|   and nothing else, as `dev tree` exits 1 on it: the harness compares
--|   the exit status, not a message.
--| - `refusal` (stage 2b): nothing if the file parses, or status 2 and
--|   `fmt -`'s first line, `[CODE] Error: MESSAGE`.
--| - `passes` (stage 4a): the tree after each of the four tidy passes, `==
--|   P1 ==`, its dump, `== P2 ==` and so on, as `stitchwort dev passes`
--|   prints them; a file the Rust formatter refuses is answered as in
--|   `refusal`.
--| - `tidied`: the tree after the last pass alone, for timing the passes
--|   against `tree`.
--| - `meaning` (stage 4b): `kept` if the four passes keep the file's
--|   `meaning`, as the dump shows it, or where they don't. No Rust side.
--| - `meaningdump`: the file's `meaning`, as the dump shows it, for
--|   `dev/fmt-meaning-oracle` to compare two files' meanings. No Rust side.
--| - `engine`: the file is a `stitchwort dev doc` dump, not a
--|   source: each declaration's layout document is built as a `Doc`,
--|   printed in 120 columns and compared with Rust's text; the answer is a
--|   line a declaration (`Fmt.DocDump.answer`). `dev/fmt-twin engine` writes
--|   the dumps and reads the answers.
--| - `text` (slices 1 to 5a, 4b, 4c and 6a): the file
--|   formatted (`formatWithin`), for a file within the slices; any other is
--|   answered with status 3 and `outside slice 6a`, or the refusal as in
--|   `refusal`.
--| - `s1` (slice 1): a line a declaration, `decl N within` and a
--|   line `text ESCAPED` with the declaration formatted, as `stitchwort dev
--|   doc`'s `text` line has Rust's, or `decl N outside`; or the refusal as
--|   in `refusal`. `dev/fmt-twin s1` compares the declarations within the
--|   slice with Rust's.
--| - `s2` (slices 1 and 2): as `s1`, for the declarations within
--|   slices 1 and 2; `dev/fmt-twin s2` compares them with Rust's.
--| - `s3` (slices 1 to 3): the same for slices 1 to 3.
--| - `s4a` (slices 1 to 4a): the same for slices 1 to 4a.
--| - `s5a` (slices 1 to 5a): the same for slices 1 to 5a.
--| - `s4b` (slices 1 to 5a and 4b): the same with slice 4b's
--|   patterns.
--| - `s4c` (slices 1 to 5a, 4b and 4c): the same with slice 4c's
--|   records and membership.
--| - `s6a` (slices 1 to 5a, 4b, 4c and 6a): the same with slice
--|   6a's `rewrite`, `cases then`, facts and `↔`.
--| - `hangs`: a line a declaration, `decl N hangs` or `decl N
--|   breaks`, its leaves after comment placement against `hangs`, the line rule the
--|   read-back proofs assume (`dev/hangs.py` checks the same in Python).
--| - the later stages are still the stage 0 stub: the file as it is.
--|
--| `--batch LIST` answers for every path in LIST (one per line) in one run,
--| each block being `\u{1e}PATH` on its own line, then
--| `\u{1f}STATUS\u{1f}LENGTH\u{1f}MESSAGE` on the next, then exactly LENGTH
--| characters of standard output. STATUS is the status single-file mode would
--| exit with, and MESSAGE the first line it would write to standard error.
namespace Fmt.Twin
import Std (Args, ExitStatus, Files, IO, List, Nat, Option, Path, Result, Text)
import Fmt (..)
import Fmt.Later (..)
import Syntax (Decl, Expr, Leaf, Lexed, SourceFile, codeOf, groupsOf, lex, parseExpression, parseFile)

--| What the command line asks for: the stage whose answer to print, the file
--| to read, or a LIST of files to answer for in one run.
type Options = { stage: Text, batch: Option Path, files: List Path }

def program: Args.Program :=
  { name = "fmt", about = "The comparison harness's formatter: prints a stage's answer for a file." }

def options: Args.Spec Options :=
  Args.Spec.start ((stage: Text) (batch: Option Path) (files: List Path) => ({ stage, batch, files }: Options))
    |> .and
      (Args.option "stage"
        (default := "text")
        (metavar := "STAGE")
        (help := "tokens, expr, tree, refusal, passes, meaning, meaningdump, engine, s1, s2, s3, s4a, s5a, s4b, s4c, s6a, hangs or text."))
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
  | "expr" =>
    match lex source with
      | Ok lexed =>
        match parseExpression lexed.settled.leaves with
          | Ok tree => { out = "Expression\n${tree.dump 1}", status = 0, message = "" }
          | Err message => { out = "", status = 1, message = "error: ${message}" }
      | Err message => { out = "", status = 1, message = "error: ${message}" }
  | "tree" =>
    match lex source with
      | Ok lexed =>
        match parseFile lexed.settled with
          | Ok file => { out = file.dump, status = 0, message = "" }
          | Err _ => { out = "", status = 1, message = "" }
      | Err _ => { out = "", status = 1, message = "" }
  | "refusal" =>
    match lex source with
      | Ok lexed =>
        match parseFile lexed.settled with
          | Ok _ => { out = "", status = 0, message = "" }
          | Err message => { out = "", status = 2, message = "[${codeOf message}] Error: ${message}" }
      | Err message => { out = "", status = 2, message = "[E-PARSE] Error: ${message}" }
  | "passes" =>
    match lex source with
      | Ok lexed =>
        match lexed.tidied with
          | Ok tidied => { out = passesDump tidied, status = 0, message = "" }
          | Err message => { out = "", status = 2, message = "[${codeOf message}] Error: ${message}" }
      | Err message => { out = "", status = 2, message = "[E-PARSE] Error: ${message}" }
  | "tidied" =>
    match lex source with
      | Ok lexed =>
        match lexed.tidied with
          | Ok tidied => { out = tidied.fourth.dump, status = 0, message = "" }
          | Err message => { out = "", status = 2, message = "[${codeOf message}] Error: ${message}" }
      | Err message => { out = "", status = 2, message = "[E-PARSE] Error: ${message}" }
  | "meaning" =>
    match lex source with
      | Ok lexed => meaningAnswer lexed
      | Err message => { out = "", status = 2, message = "[E-PARSE] Error: ${message}" }
  | "meaningdump" =>
    match lex source with
      | Ok lexed =>
        match parseFile lexed.settled with
          | Ok file => { out = file.meaning.plain.dump, status = 0, message = "" }
          | Err message => { out = "", status = 2, message = "[${codeOf message}] Error: ${message}" }
      | Err message => { out = "", status = 2, message = "[E-PARSE] Error: ${message}" }
  | "engine" =>
    match Fmt.DocDump.answer source with
      | Ok out => { out, status = 0, message = "" }
      | Err message => { out = "", status = 1, message = "error: ${message}" }
  | "text" =>
    match formatWithin source with
      | Ok out => { out, status = 0, message = "" }
      | Err message =>
        if message.startsWith "outside slice" then { out = "", status = 3, message }
        else { out = "", status = 2, message = "[${codeOf message}] Error: ${message}" }
  | "s1" => sliceAnswer Decl.printed1 source
  | "s2" => sliceAnswer Decl.printed2 source
  | "s3" => sliceAnswer Decl.printed3 source
  | "s4a" => sliceAnswer Decl.printed4a source
  | "s5a" => sliceAnswer Decl.printed5a source
  | "s4b" => sliceAnswer Decl.printed4b source
  | "s4c" => sliceAnswer Decl.printed4c source
  | "s6a" => sliceAnswer Decl.printed6a source
  | "hangs" =>
    match lex source with
      | Ok lexed => { out = hangsAnswer 1 (groupsOf lexed.settled.leaves), status = 0, message = "" }
      | Err message => { out = "", status = 1, message = "error: ${message}" }
  | _ => { out = source, status = 0, message = "" }

--| A slice stage's answer: each declaration's line, printed by `printed`
--| when it is within the slice.
def sliceAnswer (printed: Decl → Option Text) (source: Text): Answer := match lex source with
  | Ok lexed =>
    match lexed.tidied with
      | Ok tidied => { out = declarationsWithin printed 1 tidied.fourth.decls, status = 0, message = "" }
      | Err message => { out = "", status = 2, message = "[${codeOf message}] Error: ${message}" }
  | Err message => { out = "", status = 2, message = "[E-PARSE] Error: ${message}" }

--| Each declaration's leaves against `hangs` (K3a), numbered from `number`:
--| `decl N hangs` or `decl N breaks`.
def hangsAnswer (number: Nat): List (List Leaf) → Text
  | [] => ""
  | [group, ..rest] =>
    let answer := if hangs group then "decl ${number} hangs\n" else "decl ${number} breaks\n"
    answer ++ hangsAnswer (number + 1) rest

--| Each declaration's answer for a slice stage, numbered from `number`.
def declarationsWithin (printed: Decl → Option Text) (number: Nat): List Decl → Text
  | [] => ""
  | [decl, ..rest] =>
    let answer := match printed decl with
      | Some text => "decl ${number} within\ntext ${Fmt.DocDump.escape text}\n"
      | None => "decl ${number} outside\n"
    answer ++ declarationsWithin printed (number + 1) rest

def meaningAnswer (lexed: Lexed): Answer := match parseFile lexed.settled with
  | Err message => { out = "", status = 2, message = "[${codeOf message}] Error: ${message}" }
  | Ok file =>
    match lexed.tidied with
      | Ok tidied => { out = meaningKept file tidied, status = 0, message = "" }
      | Err message => { out = "", status = 2, message = "[${codeOf message}] Error: ${message}" }

--| Whether `tidy`, and the tidied tree the driver uses, keep the file's
--| `meaning`, as the dump shows it (the dump has no comments): `kept`, or
--| the first line where the meanings' dumps differ.
def meaningKept (file: SourceFile) (tidied: Tidied): Text :=
  let want := file.meaning.plain.dump
  match firstDifference want.lines file.tidy.meaning.plain.dump.lines, firstDifference want.lines
      tidied.fourth.meaning.plain.dump.lines with
    | None, None => "kept\n"
    | Some line, _ => "tidy changed it at: ${line}\n"
    | None, Some line => "tidied changed it at: ${line}\n"

def firstDifference: List Text → List Text → Option Text
  | [], [] => None
  | [first, ..rest], [other, ..others] =>
    if first == other then firstDifference rest others else Some "${first.trim} / ${other.trim}"
  | [first, .._], [] => Some "${first.trim} / nothing"
  | [], [other, .._] => Some "nothing / ${other.trim}"

--| The tree after each tidy pass, each under its `== Pn ==` line.
def passesDump (tidied: Tidied): Text :=
  "== P1 ==\n${tidied.first.dump}== P2 ==\n${tidied.second.dump}== P3 ==\n${tidied.third.dump}== P4 ==\n${tidied.fourth.dump}"

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
      else if options.stage == "tokens" || options.stage == "expr" || options.stage == "tree" then ExitStatus.of 1
      else ExitStatus.of 2

def main(): {Files, IO} ExitStatus := Args.runStatus program options run
