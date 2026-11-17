--| Spike K1 (docs/proposals/self-hosted-fmt-proof-plan.md §2): does rule
--| N's result depend on where the lines break? Takes a file's settled
--| leaves, writes them out again in two layouts with the same tokens and
--| comments, lexes and settles each, and compares the result with the
--| first, columns and line starts left out. `Wide` is a line a token;
--| `Tight` breaks a line only where a comment forces one; `Kept` is
--| `Tight` with a line started at each closer or bar holding a comment,
--| and each trailing comment after the closers and commas that follow its
--| token (`Lexed.laid`): the layout `settledAnyLayout` is about.
--|
--| `relay FILE...` prints a line a file and layout; `relay --emit wide
--| FILE` (or `tight`, `kept`) prints the re-laid text, to give to
--| `stitchwort dev tokens`.
namespace Fmt.Sketch.Relay
import Std (Args, Bool, ExitStatus, Files, IO, List, Nat, Option, Path, Result, Text)
import Fmt.Sketch.Settled (..)
import Syntax (Comment, Leaf, Lexed, Tok, Trivia, lex, quoted)

type Layout = | Wide | Tight | Kept

def Layout.name: Layout → Text
  | Wide => "wide"
  | Tight => "tight"
  | Kept => "kept"

--| Whether the lexer needs `next` to follow `previous` with nothing
--| between: the pieces of an interpolated text, and a name after a dot
--| (where a keyword is read as a field), and `@[`.
def glued (previous next: Tok): Bool :=
  next == Tok.InterpOpen || previous == Tok.InterpClose || previous == Tok.Dot || previous == Tok.At

def newlines (count: Nat): Text := Text.repeat "\n" count

def ownLines (comments: List Comment): Text :=
  comments.map (comment => "${newlines comment.blankLines}${comment.text}\n") |> Text.concat

--| The text so far, newest piece first; `fresh` when nothing is on the
--| current line; `depth` counts the `${` open, inside which no line breaks.
type Writer = {
  pieces: List Text,
  previous: Option Tok,
  depth: Nat,
  fresh: Bool
}

def Writer.add (writer: Writer) (layout: Layout) (leaf: Leaf): Writer :=
  let kind := leaf.token.kind
  let glue := writer.previous.map (previous => glued previous kind) |> .getOrElse False
  let breaks := match layout with
    | Wide => !glue && writer.depth == 0
    | Tight => False
    | Kept => leaf.token.lineStart && !glue && writer.depth == 0
  let above := "${ownLines leaf.trivia.leading}${newlines leaf.trivia.blankLines}"
  let before :=
    if writer.fresh then above
    else if !leaf.trivia.leading.isEmpty || breaks then "\n${above}"
    else if glue then ""
    else " "
  let after := match leaf.trivia.trailing with
    | Some comment => " ${comment.text}\n"
    | None => ""
  let depth := match kind with
    | Tok.InterpOpen => writer.depth + 1
    | Tok.InterpClose => writer.depth - 1
    | _ => writer.depth
  {
    pieces = [after, leaf.token.text, before, ..writer.pieces],
    previous = Some kind,
    depth,
    fresh = leaf.trivia.trailing.isSome
  }

--| The leaves as the lexer should read them back from the layout's text.
def Layout.leaves (layout: Layout) (settled: Lexed): Lexed := match layout with
  | Kept => settled.laid True []
  | _ => settled

--| The leaves as source text in a layout.
def relay (layout: Layout) (settled: Lexed): Text :=
  let lexed := layout.leaves settled
  let start: Writer := { pieces = [], previous = None, depth = 0, fresh = True }
  let writer := lexed.leaves.foldLeft start (writer leaf => writer.add layout leaf)
  let last := "${if writer.fresh then "" else "\n"}${ownLines lexed.end.leading}"
  Text.concat [last, ..writer.pieces].reverse

-- What is compared: a line a leaf, without columns or line starts.

def Comment.sig (comment: Comment) (strict: Bool): Text :=
  if strict then "${comment.blankLines}:${quoted comment.text}" else quoted comment.text

def leadingSig (strict: Bool) (trivia: Trivia): Text :=
  trivia.leading.map (comment => comment.sig strict) |> .joinWith " "

def Leaf.sig (leaf: Leaf) (strict: Bool): Text :=
  let trailing := leaf.trivia.trailing.map (comment => comment.sig False) |> .getOrElse "none"
  "${leaf.token.kind.name} ${quoted leaf.token.text} leading=[${leadingSig strict leaf.trivia}] trailing=${trailing}"

def Lexed.sigs (lexed: Lexed) (strict: Bool): List Text :=
  lexed.leaves.map (leaf => leaf.sig strict) ++ ["EOF leading=[${leadingSig strict lexed.end}]"]

def tokenSigs (lexed: Lexed): List Text :=
  lexed.leaves.map (leaf => "${leaf.token.kind.name} ${quoted leaf.token.text}")

--| The first place two lists differ, with both lines.
def firstDifference (left right: List Text) (index: Nat): Option Text := match left, right with
  | [], [] => None
  | [a, ..more], [b, ..others] =>
    if a == b then firstDifference more others (index + 1) else Some "at ${index}: ${a} <> ${b}"
  | [a, .._], [] => Some "at ${index}: ${a} <> (nothing)"
  | [], [b, .._] => Some "at ${index}: (nothing) <> ${b}"

--| How many closers and bars hold a trailing comment: the leaves rule 1's
--| limits kept one on.
def kept (lexed: Lexed): Nat :=
  lexed.leaves.filter (leaf => leaf.trivia.trailing.isSome && (leaf.token.kind.isCloser || leaf.token.kind == Tok.Pipe))
    |> .length

def comments (lexed: Lexed): Nat := lexed.leaves.foldLeft lexed.end.leading.length (count leaf =>
  count + leaf.trivia.leading.length + (if leaf.trivia.trailing.isSome then 1 else 0))

--| One layout's verdict for a settled file: the status, and the first
--| difference if there is one.
def verdict (layout: Layout) (settled: Lexed): Text := match lex (relay layout settled) with
  | Err message => "relex-failed\t${message}"
  | Ok again =>
    match firstDifference (tokenSigs settled) (tokenSigs again) 0 with
      | Some difference => "tokens-differ\t${difference}"
      | None =>
        match firstDifference ((layout.leaves settled).sigs False) (again.sigs False) 0 with
          | Some difference => "attach-differs\t${difference}"
          | None =>
            match firstDifference (settled.sigs False) (again.settled.sigs False) 0 with
              | Some difference => "settle-differs\t${difference}"
              | None =>
                match firstDifference (settled.sigs True) (again.settled.sigs True) 0 with
                  | Some difference => "blanks-differ\t${difference}"
                  | None => "same\t"

def report (path: Path): {Files, IO} () := match Files.read path with
  | Err error => IO.write "${path}\t-\tunreadable\t${error}\n"
  | Ok source =>
    match lex source with
      | Err message => IO.write "${path}\t-\tno-lex\t${message}\n"
      | Ok lexed =>
        let settled := lexed.settled
        let counts := "comments=${comments settled} kept=${kept settled} leaves=${settled.leaves.length}"
        [Wide, Tight, Kept].forEach (layout =>
          IO.write "${path}\t${layout.name}\t${verdict layout settled}\t${counts}\n")

def emit (layout: Layout) (path: Path): {Files, IO} () := match Files.read path with
  | Err error => IO.printError "${path}: ${error}"
  | Ok source =>
    match lex source with
      | Err message => IO.printError "${path}: ${message}"
      | Ok lexed => IO.write (relay layout lexed.settled)

type Options = { emit: Option Text, batch: Option Path, files: List Path }

def program: Args.Program := { name = "relay", about = "Re-lays settled leaves two ways and settles again (spike K1)." }

def options: Args.Spec Options :=
  Args.Spec.start ((emit: Option Text) (batch: Option Path) (files: List Path) => ({ emit, batch, files }: Options))
    |> .and (Args.optional "emit" (metavar := "LAYOUT") (help := "Print the re-laid text instead: wide or tight."))
    |> .and (Args.optional "batch" (metavar := "LIST") (help := "A file of paths, one per line."))
    |> .and (Args.arguments "FILE" (atLeast := 0) (help := "The files to try."))

def run (options: Options): {Files, IO} ExitStatus :=
  let listed := match options.batch with
    | None => []
    | Some list =>
      match Files.read list with
        | Ok text => text.lines.filter (line => !line.trim.isEmpty) |> .map (line => line.toPath)
        | Err _ => []
  let files := listed ++ options.files
  match options.emit with
    | Some "wide" => files.forEach (emit Wide)
    | Some "kept" => files.forEach (emit Kept)
    | Some _ => files.forEach (emit Tight)
    | None => files.forEach report
  ExitStatus.success

def main(): {Files, IO} ExitStatus := Args.runStatus program options run
