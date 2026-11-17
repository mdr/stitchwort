--| The printer: it walks a document with a work list, deciding each group's
--| line breaks as it reaches it, and never leaves a chunk of spaces at the
--| end of a line (indentation is written only before text).
--|
--| It is total by fuel: every node of the document is pushed on the work
--| list at most twice, so three times the document's size is more steps
--| than any print needs, and running out is unreachable.

namespace Fmt.Doc
import Std (List, Nat, Option, Text)

--| How a group is being printed: all its breaks as spaces (`Flat`), or each as
--| a line break (`Break`).
type Mode = | Flat | Break

--| Whether the mode is `Flat`.
def Mode.isFlat: Mode → Bool := matches | Flat

--| Whether the `IdGroup` with this id printed broken, by the record
--| `modes` (the latest first). A group not printed yet counts as flat.
def brokenIn (modes: List (Nat, Mode)) (id: Nat): Bool := match modes.lookup id with
  | Some Break => True
  | _ => False

--| The branch of an `IfBroken` the record `modes` picks.
def pickBranch (modes: List (Nat, Mode)) (id: Nat) (broken flat: Doc): Doc := if brokenIn modes id then broken else flat

--| One step of the printer's work.
type Cmd =
  | Print (indent: Nat) (mode: Mode) (doc: Doc)
  --| Before the next item of a broken `Fill`: a space if the item fits on
  --| the line, otherwise a line break.
  | FillSep (indent: Nat) (item: Doc)

--| The printer's state: what it has written, and the line it is on.
type Printer = {
  width: Nat,
  --| What is printed so far, in pieces, the last first.
  out: List Text,
  --| The column the next character goes in.
  column: Nat,
  --| Indentation owed before the next text on a fresh line.
  owed: Option Nat,
  --| Nothing but indentation written on this line yet.
  atLineStart: Bool,
  --| Trailing comments waiting for the end of the line, in order.
  suffixes: List Text,
  --| The indentation of the line being printed.
  lineIndent: Nat,
  --| How many line breaks `out` ends with, for `Blank`.
  newlinesAtEnd: Nat,
  started: Bool,
  --| How each `IdGroup` printed so far, by id, the latest first.
  modes: List (Nat, Mode)
}

--| `doc` printed in `width` columns.
def print (doc: Doc) (width: Nat): Text :=
  let fuel := 3 * doc.size + 3
  let done := (Printer.start width).run fuel fuel [Print 0 Break doc] |> .flushSuffixes
  done.out.reverse.joinWith ""

--| The printer before anything is printed.
def Printer.start (width: Nat): Printer := {
  width,
  out = [],
  column = 0,
  owed = None,
  atLineStart = True,
  suffixes = [],
  lineIndent = 0,
  newlinesAtEnd = 0,
  started = False,
  modes = []
}

--| Runs the work list for at most `fuel` steps; `total` is the budget given to
--| each `fits` question.
def Printer.run (printer: Printer) (total fuel: Nat) (stack: List Cmd): Printer := match fuel, stack with
  | 0, _ => printer
  | _, [] => printer
  | Succ more, [cmd, ..rest] =>
    let (next, stack) := printer.step total cmd rest
    next.run total more stack

--| One step of the printer: the first command on the work list, and what it
--| leaves of the list.
def Printer.step (printer: Printer) (total: Nat) (cmd: Cmd) (rest: List Cmd): (Printer, List Cmd) := match cmd with
  | FillSep indent item =>
    if printer.suffixes.isEmpty
      && fitsFrom total printer.width printer.modes
        [(indent, Flat, item)]
        rest
        (printer.left - 1)
        printer.lineIndent
        False then
      (printer.write indent " " 1, [Print indent Flat item, ..rest])
    else (printer.newline indent, [Print indent Break item, ..rest])
  | Print indent mode doc => printer.printDoc total indent mode doc rest

--| The step for a `Print` command: writes or breaks at a leaf, and replaces a
--| composite by its parts.
def Printer.printDoc (printer: Printer) (total indent: Nat) (mode: Mode) (doc: Doc) (rest: List Cmd):
    (Printer, List Cmd) :=
  match doc with
    | Empty => (printer, rest)
    | BreakParent => (printer, rest)
    | Chunk text width => (printer.write indent text width, rest)
    | Closing text => (printer.close text, rest)
    -- A trailing comment that is waiting ends its line at a `Line` or
    -- `SoftLine` even in a flat group. `fits` already keeps such a group
    -- from being flat; breaking here too makes "no code after a comment on
    -- its line" hold of the printer by these two lines alone, without a
    -- proof about `fits`.
    | Line =>
      if mode.isFlat && printer.suffixes.isEmpty then (printer.write indent " " 1, rest)
      else (printer.newline indent, rest)
    | SoftLine => if mode.isFlat && printer.suffixes.isEmpty then (printer, rest) else (printer.newline indent, rest)
    | HardLine => (printer.newline indent, rest)
    | LineStart => (printer.lineStart indent, rest)
    | CommentEnd => (printer.newline printer.lineIndent, rest)
    | LineStartHere =>
      if printer.atLineStart then ({ printer | owed = Some indent, lineIndent = indent }, rest)
      else (printer.newline indent, rest)
    | Blank => (printer.blank, rest)
    | Nest more inner => (printer, [Print (indent + more) mode inner, ..rest])
    | OneLineBelow inner => (printer, [Print (indent + 2) mode HardLine, Print (indent + 2) mode inner, ..rest])
    | Flatten inner => (printer, [Print indent Flat inner, ..rest])
    | Group inner hard =>
      let flat := mode.isFlat || (not hard && printer.fitsHere total [(indent, Flat, inner)] rest)
      (printer, [Print indent (if flat then Flat else Break) inner, ..rest])
    | IdGroup id inner hard =>
      let flat := mode.isFlat || (not hard && printer.fitsHere total [(indent, Flat, inner)] rest)
      let decided := if flat then Flat else Break
      (printer.record id decided, [Print indent decided inner, ..rest])
    | IfBroken id broken flat => (printer, [Print indent mode (pickBranch printer.modes id broken flat), ..rest])
    | Concat docs => (printer, docs.map (Print indent mode) ++ rest)
    | Fill items =>
      match items with
        | [] => (printer, rest)
        | [first, ..others] =>
          if mode.isFlat then (printer, Doc.joinLines items |> .map (Print indent Flat) |> (cmds => cmds ++ rest))
          else
            let stack := others.map (FillSep indent) ++ rest
            let firstMode := if printer.fitsHere total [(indent, Flat, first)] stack then Flat else Break
            (printer, [Print indent firstMode first, ..stack])
    | Choice options =>
      let chosen := if mode.isFlat then options.headOr Empty else printer.choose total indent rest options
      (printer, [Print indent mode chosen, ..rest])
    | LineSuffix comment => ({ printer | suffixes = printer.suffixes ++ [comment] }, rest)

--| The printer with `mode` recorded as how the `IdGroup` `id` printed.
def Printer.record (printer: Printer) (id: Nat) (mode: Mode): Printer :=
  { printer | modes = [(id, mode), ..printer.modes] }

--| The first option that fits, as `Choice` takes it; the last if none does.
def Printer.choose (printer: Printer) (total indent: Nat) (rest: List Cmd): (options: List Doc) → Doc
  | [] => Empty
  | [last] => last
  | [option, ..others] =>
    let fitting := match option with
      | OneLineBelow inner =>
        printer.width >= indent + 2
          && fitsFrom total printer.width []
            [(indent + 2, Flat, inner)]
            []
            (printer.width - indent - 2)
            (indent + 2)
            False
      | _ => printer.fitsHere total [(indent, Break, option)] rest
    if fitting then option else printer.choose total indent rest others

--| Whether `next`, then the rest of the work list, fits on this line, as
--| `fitsFrom` measures it, with any trailing comment already waiting
--| counted.
def Printer.fitsHere (printer: Printer) (total: Nat) (next: List (Nat, Mode, Doc)) (rest: List Cmd): Bool :=
  fitsFrom total printer.width printer.modes next rest printer.left printer.lineIndent (not printer.suffixes.isEmpty)

--| The items with a `Line` between each two.
def Doc.joinLines: List Doc → List Doc
  | [] => []
  | [only] => [only]
  | [item, ..items] => [item, Line, ..Doc.joinLines items]

--| Columns left on this line.
def Printer.left (printer: Printer): Nat := printer.width - printer.owed.getOrElse printer.column

--| Writes the indentation owed, if any, before text on a fresh line.
def Printer.payIndent (printer: Printer): Printer := match printer.owed with
  | None => printer
  | Some 0 => { printer | owed = None, column = 0 }
  | Some indent => { printer | out = [" ".repeat indent, ..printer.out], owed = None, column = indent }

--| `text`, `width` columns wide, in a construct indented `indent`. Text
--| after a trailing comment waiting on its line starts the next line (a
--| comment break), and spaces there are dropped: no code follows a comment
--| on its line.
def Printer.write (printer: Printer) (indent: Nat) (text: Text) (width: Nat): Printer :=
  if text.isEmpty then printer
  else if printer.suffixes.isEmpty then printer.put text width
  else if text.all (char => char == ' ') then printer
  else (printer.newline (printer.continuation indent)).put text width

--| A closing bracket or comma: on the line as it stands, before any
--| trailing comment waiting there.
def Printer.close (printer: Printer) (text: Text): Printer :=
  if text.isEmpty then printer else printer.put text text.length

--| Writes `text`, `width` columns wide, on the current line, after any
--| indentation owed.
def Printer.put (printer: Printer) (text: Text) (width: Nat): Printer :=
  let paid := printer.payIndent
  { paid |
    out = [text, ..paid.out],
    column = paid.column + width,
    atLineStart = False,
    newlinesAtEnd = 0,
    started = True
  }

--| The indentation of a comment break in a construct indented `indent`:
--| deeper than the line being broken, so what follows continues it.
def Printer.continuation (printer: Printer) (indent: Nat): Nat := Nat.max indent (printer.lineIndent + 2)

--| A comment break before an own-line comment, unless a line starts here.
def Printer.lineStart (printer: Printer) (indent: Nat): Printer :=
  if printer.atLineStart then printer else printer.newline (printer.continuation indent)

--| Writes the trailing comments that wait, each after a space, ending their
--| line.
def Printer.flushSuffixes (printer: Printer): Printer :=
  printer.suffixes.foldLeft { printer | suffixes = [] } Printer.flushOne

--| A waiting trailing comment written: after one space, or at the line's
--| indentation if nothing else is on the line.
def Printer.flushOne (printer: Printer) (comment: Text): Printer :=
  let spaced := if printer.atLineStart then printer.payIndent else { printer | out = [" ", ..printer.out] }
  { spaced | out = [comment, ..spaced.out], atLineStart = False, newlinesAtEnd = 0, started = True }

--| Ends the line: drops the spaces at its end, writes the waiting comments and
--| a line break, and owes `indent` columns on the next.
def Printer.newline (printer: Printer) (indent: Nat): Printer :=
  let flushed := { printer | out = trimSpaces printer.out }.flushSuffixes
  { flushed |
    out = ["\n", ..flushed.out],
    column = 0,
    owed = Some indent,
    atLineStart = True,
    lineIndent = indent,
    newlinesAtEnd = flushed.newlinesAtEnd + 1,
    started = True
  }

--| The pieces printed (the last first) without the pieces of spaces at
--| their end: a space the layout put before a break it didn't plan, a
--| comment break, would end its line.
def trimSpaces (out: List Text): List Text := match out with
  | [last, ..earlier] if last.all (char => char == ' ') => trimSpaces earlier
  | _ => out

--| An empty line, if the printer is at a line start after some output and the
--| line before isn't already empty.
def Printer.blank (printer: Printer): Printer :=
  if printer.atLineStart && printer.started && printer.newlinesAtEnd < 2 then
    { printer | out = ["\n", ..printer.out], newlinesAtEnd = printer.newlinesAtEnd + 1 }
  else printer

--| Whether `next`, then the rest of the work list, fits in `left` columns
--| up to the first line break the work would make, on a page `width` wide
--| whose current line is indented `lineIndent`. Each piece of work carries
--| the indentation of its construct. Groups are measured in the mode of
--| what holds them unless they must break, as Prettier's `fits` does: a
--| group that won't fit flat breaks at its first line, so measuring up to
--| there is enough.
--|
--| `suffix` says a trailing comment is waiting for the end of the line.
--| Code text after it starts a new line (a comment break, as
--| `Printer.write` makes), at `max indent (lineIndent + 2)`, and the
--| measure goes on from there with the whole width less that
--| indentation, as SW-3447's Rust printer measures; spaces there are
--| dropped, so they take no room. A closer after it stays on the line and
--| counts towards its width. A line break in a flat group after it
--| doesn't fit: the printer would break it, where the measure assumed
--| none.
--|
--| `modes` is how each `IdGroup` printed so far, for the `IfBroken`s
--| measured. A broken `Fill`'s first item and a `OneLineBelow` option are
--| measured with none recorded, as Rust's `fits_flat` measures them, so
--| an `IfBroken` there counts as flat.
def fitsFrom (fuel width: Nat) (modes: List (Nat, Mode)) (stack: List (Nat, Mode, Doc)) (rest: List Cmd)
    (left lineIndent: Nat) (suffix: Bool):
    Bool :=
  match fuel with
    | 0 => True
    | Succ more =>
      match stack with
        | [] =>
          match rest with
            | [Print indent mode doc, ..others] =>
              fitsFrom more width modes [(indent, mode, doc)] others left lineIndent suffix
            -- The next fill item starts with a separator that may break.
            | _ => True
        | [(indent, mode, doc), ..stack] =>
          match doc with
            | Empty => fitsFrom more width modes stack rest left lineIndent suffix
            | Blank => fitsFrom more width modes stack rest left lineIndent suffix
            | LineSuffix _ => fitsFrom more width modes stack rest left lineIndent True
            | BreakParent => not mode.isFlat && fitsFrom more width modes stack rest left lineIndent suffix
            | Chunk text textWidth =>
              if not suffix then
                textWidth <= left && fitsFrom more width modes stack rest (left - textWidth) lineIndent False
              else if text.all (char => char == ' ') then fitsFrom more width modes stack rest left lineIndent True
              else
                let broken := Nat.max indent (lineIndent + 2)
                broken + textWidth <= width
                  && fitsFrom more width modes stack rest (width - broken - textWidth) broken False
            -- It joins the line of a waiting comment, which still waits.
            | Closing text =>
              text.length <= left && fitsFrom more width modes stack rest (left - text.length) lineIndent suffix
            | Line =>
              not mode.isFlat
                || (not suffix && 1 <= left && fitsFrom more width modes stack rest (left - 1) lineIndent suffix)
            | SoftLine => not mode.isFlat || (not suffix && fitsFrom more width modes stack rest left lineIndent suffix)
            | HardLine => not mode.isFlat
            | LineStart => not mode.isFlat
            | CommentEnd => not mode.isFlat
            | LineStartHere => not mode.isFlat
            | Nest extra inner =>
              fitsFrom more width modes [(indent + extra, mode, inner), ..stack] rest left lineIndent suffix
            | Flatten inner => fitsFrom more width modes [(indent, Flat, inner), ..stack] rest left lineIndent suffix
            | Group inner hard =>
              if hard && mode.isFlat then False
              else
                fitsFrom more width modes
                  [(indent, if hard then Break else mode, inner), ..stack]
                  rest
                  left
                  lineIndent
                  suffix
            | IdGroup _ inner hard =>
              if hard && mode.isFlat then False
              else
                fitsFrom more width modes
                  [(indent, if hard then Break else mode, inner), ..stack]
                  rest
                  left
                  lineIndent
                  suffix
            -- A group not printed yet is measured as flat.
            | IfBroken id broken flat =>
              fitsFrom more width modes
                [(indent, mode, pickBranch modes id broken flat), ..stack]
                rest
                left
                lineIndent
                suffix
            | Concat docs =>
              fitsFrom more width modes (docs.map (inner => (indent, mode, inner)) ++ stack) rest left lineIndent suffix
            | Fill items =>
              if mode.isFlat then
                fitsFrom more width modes
                  (Doc.joinLines items |> .map (inner => (indent, mode, inner)) |> (inners => inners ++ stack))
                  rest
                  left
                  lineIndent
                  suffix
              -- Only the first item is sure to be on this line; the separator
              -- after it may break.
              else
                match items with
                  | [] => True
                  | [first, .._] => fitsFrom more width [] [(indent, Flat, first)] [] left lineIndent suffix
            | OneLineBelow _ => True
            | Choice options =>
              match (if mode.isFlat then options.head else options.last) with
                | None => fitsFrom more width modes stack rest left lineIndent suffix
                | Some option => fitsFrom more width modes [(indent, mode, option), ..stack] rest left lineIndent suffix
