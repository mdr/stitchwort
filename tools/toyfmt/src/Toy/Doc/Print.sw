--| The printer: it walks a document with a work list, deciding each group's
--| line breaks as it reaches it, and never leaves spaces at the end of a
--| line (indentation is written only before text).
--|
--| It is total by fuel: every node of the document is pushed on the work
--| list at most twice, so three times the document's size is more steps
--| than any print needs, and running out is unreachable.

namespace Toy.Doc
import Std (List, Option, Text)

type Mode = | Flat | Break

def Mode.isFlat: Mode → Bool := matches | Flat

--| One step of the printer's work.
type Cmd =
  | Print (indent: Nat) (mode: Mode) (doc: Doc)
  --| Before the next item of a broken `Fill`: a space if the item fits on
  --| the line, otherwise a line break.
  | FillSep (indent: Nat) (item: Doc)

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
  --| How many line breaks `out` ends with, for `Blank`.
  newlinesAtEnd: Nat,
  started: Bool
}

--| `doc` printed in `width` columns.
def print (doc: Doc) (width: Nat): Text :=
  let start: Printer :=
    { width, out = [], column = 0, owed = None, atLineStart = True, suffixes = [], newlinesAtEnd = 0, started = False }
  let fuel := 3 * doc.size + 3
  let done := start.run fuel fuel [Print 0 Break doc] |> .flushSuffixes
  done.out.reverse.joinWith ""

def Printer.run (printer: Printer) (total fuel: Nat) (stack: List Cmd): Printer := match fuel, stack with
  | 0, _ => printer
  | _, [] => printer
  | Succ more, [cmd, ..rest] =>
    let (next, stack) := printer.step total cmd rest
    next.run total more stack

def Printer.step (printer: Printer) (total: Nat) (cmd: Cmd) (rest: List Cmd): (Printer, List Cmd) := match cmd with
  | FillSep indent item =>
    if printer.suffixes.isEmpty && fits total [(Flat, item)] rest (printer.left - 1) then
      (printer.write " " 1, [Print indent Flat item, ..rest])
    else (printer.newline indent, [Print indent Break item, ..rest])
  | Print indent mode doc => printer.printDoc total indent mode doc rest

def Printer.printDoc (printer: Printer) (total indent: Nat) (mode: Mode) (doc: Doc) (rest: List Cmd):
    (Printer, List Cmd) :=
  match doc with
    | Empty => (printer, rest)
    | BreakParent => (printer, rest)
    | Chunk text width => (printer.write text width, rest)
    | Line => if mode.isFlat then (printer.write " " 1, rest) else (printer.newline indent, rest)
    | SoftLine => if mode.isFlat then (printer, rest) else (printer.newline indent, rest)
    | HardLine => (printer.newline indent, rest)
    | Blank => (printer.blank, rest)
    | Nest more inner => (printer, [Print (indent + more) mode inner, ..rest])
    | OneLineBelow inner => (printer, [Print (indent + 2) mode HardLine, Print (indent + 2) mode inner, ..rest])
    | Flatten inner => (printer, [Print indent Flat inner, ..rest])
    | Group inner hard =>
      let flat := mode.isFlat || (not hard && fits total [(Flat, inner)] rest printer.left)
      (printer, [Print indent (if flat then Flat else Break) inner, ..rest])
    | Concat docs => (printer, docs.map (Print indent mode) ++ rest)
    | Fill items =>
      match items with
        | [] => (printer, rest)
        | [first, ..others] =>
          if mode.isFlat then (printer, Doc.joinLines items |> .map (Print indent Flat) |> (cmds => cmds ++ rest))
          else
            let stack := others.map (FillSep indent) ++ rest
            let firstMode := if fits total [(Flat, first)] stack printer.left then Flat else Break
            (printer, [Print indent firstMode first, ..stack])
    | Choice options =>
      let chosen := if mode.isFlat then options.headOr Empty else printer.choose total indent rest options
      (printer, [Print indent mode chosen, ..rest])
    | LineSuffix comment => ({ printer | suffixes = printer.suffixes ++ [comment] }, rest)

--| The first option that fits, as `Choice` takes it; the last if none does.
def Printer.choose (printer: Printer) (total indent: Nat) (rest: List Cmd): (options: List Doc) → Doc
  | [] => Empty
  | [last] => last
  | [option, ..others] =>
    let fitting := match option with
      | OneLineBelow inner => printer.width >= indent + 2 && fitsFlat total inner (printer.width - indent - 2)
      | _ => fits total [(Break, option)] rest printer.left
    if fitting then option else printer.choose total indent rest others

--| The items with a `Line` between each two.
def Doc.joinLines: List Doc → List Doc
  | [] => []
  | [only] => [only]
  | [item, ..items] => [item, Line, ..Doc.joinLines items]

--| Columns left on this line.
def Printer.left (printer: Printer): Nat := printer.width - printer.owed.getOrElse printer.column

def Printer.payIndent (printer: Printer): Printer := match printer.owed with
  | None => printer
  | Some 0 => { printer | owed = None, column = 0 }
  | Some indent => { printer | out = [" ".repeat indent, ..printer.out], owed = None, column = indent }

def Printer.write (printer: Printer) (text: Text) (width: Nat): Printer :=
  if text.isEmpty then printer
  else
    let paid := printer.payIndent
    { paid |
      out = [text, ..paid.out],
      column = paid.column + width,
      atLineStart = False,
      newlinesAtEnd = 0,
      started = True
    }

def Printer.flushSuffixes (printer: Printer): Printer :=
  printer.suffixes.foldLeft { printer | suffixes = [] } (at comment =>
    let spaced := if at.atLineStart then at.payIndent else { at | out = [" ", ..at.out] }
    { spaced | out = [comment, ..spaced.out], atLineStart = False, newlinesAtEnd = 0, started = True })

def Printer.newline (printer: Printer) (indent: Nat): Printer :=
  let flushed := printer.flushSuffixes
  { flushed |
    out = ["\n", ..flushed.out],
    column = 0,
    owed = Some indent,
    atLineStart = True,
    newlinesAtEnd = flushed.newlinesAtEnd + 1,
    started = True
  }

def Printer.blank (printer: Printer): Printer :=
  if printer.atLineStart && printer.started && printer.newlinesAtEnd < 2 then
    { printer | out = ["\n", ..printer.out], newlinesAtEnd = printer.newlinesAtEnd + 1 }
  else printer

--| Whether `next`, then the rest of the work list, fits in `left` columns
--| up to the first line break the work would make. Groups are measured in
--| the mode of what holds them unless they must break, as Prettier's `fits`
--| does: a group that won't fit flat breaks at its first line, so measuring
--| up to there is enough.
def fits (fuel: Nat) (next: List (Mode, Doc)) (rest: List Cmd) (left: Nat): Bool := fitsFrom fuel next rest left False

--| `fits`, where `suffix` says a trailing comment is waiting for the end of
--| the line: anything but closing brackets and commas after it would move
--| it.
def fitsFrom (fuel: Nat) (stack: List (Mode, Doc)) (rest: List Cmd) (left: Nat) (suffix: Bool): Bool := match fuel with
  | 0 => True
  | Succ more =>
    match stack with
      | [] =>
        match rest with
          | [Print _ mode doc, ..others] => fitsFrom more [(mode, doc)] others left suffix
          -- The next fill item starts with a separator that may break.
          | _ => True
      | [(mode, doc), ..stack] =>
        match doc with
          | Empty => fitsFrom more stack rest left suffix
          | Blank => fitsFrom more stack rest left suffix
          | LineSuffix _ => fitsFrom more stack rest left True
          | BreakParent => not mode.isFlat && fitsFrom more stack rest left suffix
          | Chunk text width =>
            if suffix && not (text.all isCloser) then False
            else width <= left && fitsFrom more stack rest (left - width) suffix
          | Line => not mode.isFlat || (not suffix && 1 <= left && fitsFrom more stack rest (left - 1) suffix)
          | SoftLine => not mode.isFlat || (not suffix && fitsFrom more stack rest left suffix)
          | HardLine => not mode.isFlat
          | Nest _ inner => fitsFrom more [(mode, inner), ..stack] rest left suffix
          | Flatten inner => fitsFrom more [(Flat, inner), ..stack] rest left suffix
          | Group inner hard =>
            if hard && mode.isFlat then False
            else fitsFrom more [(if hard then Break else mode, inner), ..stack] rest left suffix
          | Concat docs => fitsFrom more (docs.map (inner => (mode, inner)) ++ stack) rest left suffix
          | Fill items =>
            if mode.isFlat then
              fitsFrom more
                (Doc.joinLines items |> .map (inner => (mode, inner)) |> (inners => inners ++ stack))
                rest
                left
                suffix
            -- Only the first item is sure to be on this line; the separator
            -- after it may break.
            else
              match items with
                | [] => True
                | [first, .._] => fitsFlat more first left
          | OneLineBelow _ => True
          | Choice options =>
            match (if mode.isFlat then options.head else options.last) with
              | None => fitsFrom more stack rest left suffix
              | Some option => fitsFrom more [(mode, option), ..stack] rest left suffix

def isCloser (char: Char): Bool := char == ')' || char == ']' || char == '}' || char == ','

--| Whether `doc`, printed flat, fits in `left` columns.
def fitsFlat (fuel: Nat) (doc: Doc) (left: Nat): Bool := fits fuel [(Flat, doc)] [] left
