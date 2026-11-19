--| The printer: it walks a document with a work list, deciding each group's
--| line breaks as it reaches it, and never leaves a chunk of spaces at the
--| end of a line (indentation is written only before text).
--|
--| It is total by fuel: every node of the document is pushed on the work
--| list at most twice, so three times the document's size is more steps
--| than any print needs, and running out is unreachable.

import Doc (..)
import Bool (not)

--| How a group is being printed: all its breaks as spaces (`Flat`), or each as
--| a line break (`Break`).
type Doc.Mode = | Flat | Break

--| Whether the mode is `Flat`.
def Doc.Mode.isFlat: Mode → Bool := matches | Flat

--| Whether the `IdGroup` with this id printed broken, by the record
--| `modes` (the latest first). A group not printed yet counts as flat.
def Doc.brokenIn (modes: List (Nat, Mode)) (id: Nat): Bool := match modes.lookup id with
  | Some Break => True
  | _ => False

--| The branch of an `IfBroken` the record `modes` picks.
@[noReceiver]
def Doc.pickBranch (modes: List (Nat, Mode)) (id: Nat) (broken flat: Doc): Doc :=
  if brokenIn modes id then broken else flat

--| One step of the printer's work.
type Doc.Cmd =
  | Print (indent: Nat) (mode: Mode) (doc: Doc)
  --| Before the next item of a broken `Fill`: a space if the item fits on
  --| the line, otherwise a line break.
  | FillSep (indent: Nat) (item: Doc)

--| The printer's state: what it has written, and the line it is on.
type Doc.Printer = {
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
  modes: List (Nat, Mode),
  --| Spaces after a waiting trailing comment, written only if a closer
  --| follows on its line; code there starts the next line instead.
  heldSpaces: Nat,
  --| The comment floor and the open marks.
  carry: Carry
}

--| A `Mark` whose `CloserLine` hasn't come: the indentation of the line
--| it is on, and the least indentation of the lines printed since (none
--| before the next line break).
type Doc.OpenMark = { key: Nat, marked: Nat, least: Option Nat }

--| What the printer carries from line to line.
type Doc.Carry = {
  --| After a comment break before an own-line comment: the least
  --| indentation of the lines up to the next code.
  floor: Option Nat,
  --| The open marks, the latest first.
  marks: List OpenMark
}

--| No comment floor and no open marks.
def Doc.Carry.none: Carry := { floor = None, marks = [] }

--| The open marks after a line indented `at`.
def Doc.lowerMarks (at: Nat): List OpenMark → List OpenMark
  | [] => []
  | [mark, ..marks] => [{ mark | least = Some (lowest mark.least at) }, ..lowerMarks at marks]

--| `at`, or the least so far if that is less.
def Doc.lowest (least: Option Nat) (at: Nat): Nat := match least with
  | None => at
  | Some least => Nat.min least at

--| What is carried to a line broken at `indent`: the line is at the
--| floor if that is deeper, and every open mark has seen it.
def Doc.Carry.breakTo (carry: Carry) (indent: Nat): Carry :=
  { carry | marks = lowerMarks (floored carry indent) carry.marks }

--| What is carried to the line a comment break at `broken` starts: the
--| break's indentation is the floor until the next code.
def Doc.Carry.startFloor (carry: Carry) (broken: Nat): Carry := { carry.breakTo broken | floor = Some broken }

--| A `Mark` with this key, on a line indented `at`.
def Doc.Carry.mark (carry: Carry) (key at: Nat): Carry :=
  { carry | marks = [{ key, marked = at, least = None }, ..carry.marks] }

--| Where a `CloserLine` with this key in a construct indented `indent`
--| starts its line: at `indent`, unless a line since its mark is at or
--| left of that; then at the marked line's indentation, if less.
def Doc.Carry.closerAt (carry: Carry) (key indent: Nat): Nat := match carry.marks.find (mark => mark.key == key) with
  | Some { marked, least = Some least, .. } => if least <= indent then Nat.min marked indent else indent
  | _ => indent

--| The carry before a `CloserLine`'s line break: its mark closed, and no
--| comment floor.
def Doc.Carry.close (carry: Carry) (key: Nat): Carry :=
  { floor = None, marks = carry.marks.filter (mark => mark.key != key) }

--| `doc` printed in `width` columns.
def Doc.print (doc: Doc) (width: Nat): Text :=
  let fuel := 3 * doc.size + 3
  let done := (Printer.start width).run fuel fuel [Print 0 Break doc] |> .flushSuffixes
  done.out.reverse.joinWith ""

--| The printer before anything is printed.
def Doc.Printer.start (width: Nat): Printer := {
  width,
  out = [],
  column = 0,
  owed = None,
  atLineStart = True,
  suffixes = [],
  lineIndent = 0,
  newlinesAtEnd = 0,
  started = False,
  modes = [],
  heldSpaces = 0,
  carry = Carry.none
}

--| Runs the work list for at most `fuel` steps; `total` is the budget given to
--| each `fits` question.
def Doc.Printer.run (printer: Printer) (total fuel: Nat) (stack: List Cmd): Printer := match fuel, stack with
  | 0, _ => printer
  | _, [] => printer
  | Succ more, [cmd, ..rest] =>
    let (next, stack) := printer.step total cmd rest
    next.run total more stack

--| One step of the printer: the first command on the work list, and what it
--| leaves of the list.
def Doc.Printer.step (printer: Printer) (total: Nat) (cmd: Cmd) (rest: List Cmd): (Printer, List Cmd) := match cmd with
  | FillSep indent item =>
    if printer.suffixes.isEmpty
      && fitsFrom total printer.width printer.modes
        [(indent, Flat, item)]
        rest
        (printer.left - 1)
        printer.lineIndent
        Clear then
      (printer.write indent " " 1, [Print indent Flat item, ..rest])
    else (printer.newline indent, [Print indent Break item, ..rest])
  | Print indent mode doc => printer.printDoc total indent mode doc rest

--| The step for a `Print` command: writes or breaks at a leaf, and replaces a
--| composite by its parts.
def Doc.Printer.printDoc (printer: Printer) (total indent: Nat) (mode: Mode) (doc: Doc) (rest: List Cmd):
    (Printer, List Cmd) :=
  match doc with
    | Doc.Nothing | BreakParent => (printer, rest)
    | Chunk text width => (printer.write indent text width, rest)
    | Closing text => (printer.close text, rest)
    -- A flat `Line` after a waiting trailing comment is a held space:
    -- code after it starts the next line (`write`), a closer stays.
    | Line => if mode.isFlat then (printer.write indent " " 1, rest) else (printer.newline indent, rest)
    | SoftLine => if mode.isFlat then (printer, rest) else (printer.newline indent, rest)
    | HardLine => (printer.newline indent, rest)
    | LineStart => (printer.lineStart indent, rest)
    | LineStartHere =>
      if printer.atLineStart then ({ printer | owed = Some indent, lineIndent = indent }, rest)
      else (printer.newline indent, rest)
    | Blank => (printer.blank, rest)
    | Mark key => ({ printer | carry = printer.carry.mark key printer.lineIndent }, rest)
    | CloserLine key => (printer.closerLine key indent, rest)
    | Nest more inner => (printer, [Print (indent + more) mode inner, ..rest])
    | Align inner => (printer, [Print (printer.alignAt indent) mode inner, ..rest])
    | AlignInset inner => (printer, [Print (printer.alignAt (indent + 2)) mode inner, ..rest])
    | Displaced inner => (printer.displace indent, [Print (printer.displacedAt indent) mode inner, ..rest])
    | OneLineBelow inner => (printer, [Print (indent + 2) mode HardLine, Print (indent + 2) mode inner, ..rest])
    | Flatten inner => (printer, [Print indent Flat inner, ..rest])
    | Group inner hard =>
      let flat := mode.isFlat || (not hard && printer.fitsHere total [(indent, Flat, inner)] rest)
      (printer, [Print indent (if flat then Flat else Break) inner, ..rest])
    -- Measured in what is left of the line or up to column `max`,
    -- whichever is less.
    | NarrowGroup max inner hard =>
      let room := Nat.min printer.left (max - printer.owed.getOrElse printer.column)
      let flat :=
        mode.isFlat
          || (not hard
            && fitsFrom total printer.width printer.modes
              [(indent, Flat, inner)]
              rest
              room
              printer.lineIndent
              printer.waiting)
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
      let chosen := if mode.isFlat then options.headOr Doc.Nothing else printer.choose total indent rest options
      (printer, [Print indent mode chosen, ..rest])
    | LineSuffix comment => ({ printer | suffixes = printer.suffixes ++ [comment] }, rest)

--| The indentation of an `Align`'s line breaks: the column it starts at,
--| or `atStart` at a line start.
def Doc.Printer.alignAt (printer: Printer) (atStart: Nat): Nat :=
  if printer.atLineStart then atStart else printer.column

--| The indentation of a `Displaced` element's line breaks, in a construct
--| indented `indent`: where its first line lands. At a line start that is
--| the indentation owed, if deeper; after a waiting comment, the comment
--| break's.
def Doc.Printer.displacedAt (printer: Printer) (indent: Nat): Nat :=
  if printer.atLineStart then Nat.max indent (printer.owed.getOrElse 0)
  else if printer.suffixes.isEmpty then indent
  else printer.continuation indent

--| The printer before a `Displaced` element: a trailing comment waiting
--| ends its line first (a comment break, unless a line starts here), so
--| the element starts the next.
def Doc.Printer.displace (printer: Printer) (indent: Nat): Printer :=
  if printer.suffixes.isEmpty then printer else printer.commentBreak indent

--| The printer with `mode` recorded as how the `IdGroup` `id` printed.
def Doc.Printer.record (printer: Printer) (id: Nat) (mode: Mode): Printer :=
  { printer | modes = [(id, mode), ..printer.modes] }

--| The first option that fits, as `Choice` takes it; the last if none does.
def Doc.Printer.choose (printer: Printer) (total indent: Nat) (rest: List Cmd): (options: List Doc) → Doc
  | [] => Doc.Nothing
  | [last] => last
  | [option, ..others] =>
    let fitting := match option with
      | OneLineBelow inner =>
        printer.width >= indent + 2
          && fitsFrom total printer.width printer.modes
            [(indent + 2, Flat, inner)]
            []
            (printer.width - indent - 2)
            (indent + 2)
            Clear
      | _ => printer.fitsHere total [(indent, Break, option)] rest
    if fitting then option else printer.choose total indent rest others

--| Whether `next`, then the rest of the work list, fits on this line, as
--| `fitsFrom` measures it, with any trailing comment already waiting
--| counted.
def Doc.Printer.fitsHere (printer: Printer) (total: Nat) (next: List (Nat, Mode, Doc)) (rest: List Cmd): Bool :=
  fitsFrom total printer.width printer.modes next rest printer.left printer.lineIndent printer.waiting

--| What a measure from where the printer is knows of a trailing comment
--| waiting there.
def Doc.Printer.waiting (printer: Printer): Trailing :=
  if printer.suffixes.isEmpty then Clear else Pending printer.heldSpaces False

--| What a measure knows of a trailing comment waiting on the line it
--| measures.
type Doc.Trailing =
  | Clear
  --| One waits, with `held` spaces after it, which a closer would write
  --| before itself; `flatBreak` says a flat line break came after it, so
  --| code would start a line the measure didn't plan.
  | Pending (held: Nat) (flatBreak: Bool)

--| The measure's state once a trailing comment starts to wait.
def Doc.Trailing.noted: Trailing → Trailing
  | Clear => Pending 0 False
  | Pending held _ => Pending held False

--| The items with a `Line` between each two.
def Doc.joinLines: List Doc → List Doc
  | [] => []
  | [only] => [only]
  | [item, ..items] => [item, Line, ..Doc.joinLines items]

--| Columns left on this line.
def Doc.Printer.left (printer: Printer): Nat := printer.width - printer.owed.getOrElse printer.column

--| Writes the indentation owed, if any, before text on a fresh line.
def Doc.Printer.payIndent (printer: Printer): Printer := match printer.owed with
  | None => printer
  | Some 0 => { printer | owed = None, column = 0 }
  | Some indent => { printer | out = [" ".repeat indent, ..printer.out], owed = None, column = indent }

--| `text`, `width` columns wide, in a construct indented `indent`. Text
--| after a trailing comment waiting on its line starts the next line (a
--| comment break), and spaces there are held, written only before a
--| closer: no code follows a comment on its line.
--|
--| A comment waits at a line start only in a document no rule builds (a
--| trailing comment follows a word); there the Rust engine writes the
--| text first and the comment after it, and this one keeps the
--| document's order, as `readingWords` states of every document.
def Doc.Printer.write (printer: Printer) (indent: Nat) (text: Text) (width: Nat): Printer :=
  if text.isEmpty then printer
  else if printer.suffixes.isEmpty then printer.put text width
  else if text.all (char => char == ' ') then { printer | heldSpaces = printer.heldSpaces + text.length }
  else (printer.newline (printer.continuation indent)).put text width

--| A closing bracket or comma: on the line as it stands, before any
--| trailing comment waiting there, after the spaces held since it.
def Doc.Printer.close (printer: Printer) (text: Text): Printer :=
  if text.isEmpty then printer
  else if printer.suffixes.isEmpty then printer.put text text.length
  else printer.writeHeld.put text text.length

--| The spaces held after a waiting comment, written. None are held at a
--| line start, where they would move the next word.
def Doc.Printer.writeHeld (printer: Printer): Printer :=
  if printer.atLineStart then printer
  else
    match printer.heldSpaces with
      | 0 => printer
      | held => { printer | out = [" ".repeat held, ..printer.out], column = printer.column + held, heldSpaces = 0 }

--| Writes `text`, `width` columns wide, on the current line, after any
--| indentation owed. Code ends a comment floor; a comment doesn't.
def Doc.Printer.put (printer: Printer) (text: Text) (width: Nat): Printer :=
  let paid := printer.payIndent
  { paid |
    out = [text, ..paid.out],
    column = paid.column + width,
    atLineStart = False,
    newlinesAtEnd = 0,
    started = True,
    carry = floorAfter text paid.carry
  }

--| The carry after `text` is written: a comment keeps the comment floor, code
--| ends it.
def Doc.floorAfter (text: Text) (carry: Carry): Carry :=
  if text.startsWith "--" then carry else { carry | floor = None }

--| A comment leaves the carry as it was: the comment floor stays in force.
theorem Doc.commentKeepsFloor ∀ (text: Text) (carry: Carry)
    (comment: text.startsWith "--" = True):
    floorAfter text carry = carry :=
  rewrite comment

--| An instance of `commentKeepsFloor`, so it isn't vacuous: the audit's
--| random search rarely makes a text that starts with `--`.
theorem Doc.commentKeepsFloorExample: floorAfter "-- c" { floor = Some 4, marks = [] }
      = { floor = Some 4, marks = [] } :=
  commentKeepsFloor "-- c" { floor = Some 4, marks = [] } byComputing

--| The indentation of a comment break in a construct indented `indent`:
--| deeper than the line being broken, so what follows continues it.
def Doc.Printer.continuation (printer: Printer) (indent: Nat): Nat := Nat.max indent (printer.lineIndent + 2)

--| A comment break, unless a line starts here.
def Doc.Printer.commentBreak (printer: Printer) (indent: Nat): Printer :=
  if printer.atLineStart then printer else printer.newline (printer.continuation indent)

--| A comment break before an own-line comment, unless a line starts here.
--| The lines after it, up to the next code, are indented at least as
--| deep (the comment floor).
def Doc.Printer.lineStart (printer: Printer) (indent: Nat): Printer :=
  if printer.atLineStart then printer
  else
    { printer.newline (printer.continuation indent) | carry = printer.carry.startFloor (printer.continuation indent) }

--| A `CloserLine` with this key in a construct indented `indent`: its mark
--| closed and the comment floor ended, a line break to where the closer
--| goes (`Carry.closerAt`). At a line start with no comment waiting,
--| where a break before it has ended the line already, that line moves
--| there instead, as a second break would leave it empty.
def Doc.Printer.closerLine (printer: Printer) (key indent: Nat): Printer :=
  let column := printer.carry.closerAt key indent
  if printer.atLineStart && printer.suffixes.isEmpty then
    { printer | owed = Some column, lineIndent = column, carry = (printer.carry.close key).breakTo column }
  else { printer | carry = printer.carry.close key }.newline column

--| Writes the trailing comments that wait, each after a space, ending their
--| line.
def Doc.Printer.flushSuffixes (printer: Printer): Printer :=
  printer.suffixes.foldLeft { printer | suffixes = [] } Printer.flushOne

--| A waiting trailing comment written: after one space, or at the line's
--| indentation if nothing else is on the line.
def Doc.Printer.flushOne (printer: Printer) (comment: Text): Printer :=
  let spaced := if printer.atLineStart then printer.payIndent else { printer | out = [" ", ..printer.out] }
  { spaced | out = [comment, ..spaced.out], atLineStart = False, newlinesAtEnd = 0, started = True }

--| Ends the line: drops the spaces at its end, writes the waiting comments and
--| a line break, and owes `indent` columns on the next, or the comment
--| floor's if deeper. Spaces held are dropped, and the open marks see
--| the new line.
def Doc.Printer.newline (printer: Printer) (indent: Nat): Printer :=
  let flushed := { printer | out = trimSpaces printer.out }.flushSuffixes
  let at := floored printer.carry indent
  { flushed |
    out = ["\n", ..flushed.out],
    column = 0,
    owed = Some at,
    atLineStart = True,
    lineIndent = at,
    newlinesAtEnd = flushed.newlinesAtEnd + 1,
    started = True,
    heldSpaces = 0,
    carry = printer.carry.breakTo indent
  }

--| `indent`, or the comment floor if there is one and it is deeper.
def Doc.floored (carry: Carry) (indent: Nat): Nat := match carry.floor with
  | None => indent
  | Some least => Nat.max indent least

--| The pieces printed (the last first) without the pieces of spaces at
--| their end: a space the layout put before a break it didn't plan, a
--| comment break, would end its line.
def Doc.trimSpaces (out: List Text): List Text := match out with
  | [last, ..earlier] if last.all (char => char == ' ') => trimSpaces earlier
  | _ => out

--| An empty line, if the printer is at a line start after some output and the
--| line before isn't already empty.
def Doc.Printer.blank (printer: Printer): Printer :=
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
--| `suffix` says whether a trailing comment is waiting for the end of the
--| line. Code text after it starts a new line (a comment break, as
--| `Printer.write` makes), at `max indent (lineIndent + 2)`, and the
--| measure goes on from there with the whole width less that
--| indentation, as SW-3447's Rust printer measures; spaces there are
--| held, taking room only if a closer follows. A closer after it stays on
--| the line and counts towards its width, with the spaces held before
--| it. A line break in a flat group after it is no break where only
--| closers follow; code after it doesn't fit, since the printer would
--| start a line the measure didn't plan.
--|
--| `modes` is how each `IdGroup` printed so far, for the `IfBroken`s
--| measured, a broken `Fill`'s first item and a `OneLineBelow` option
--| included.
def Doc.fitsFrom (fuel width: Nat) (modes: List (Nat, Mode)) (stack: List (Nat, Mode, Doc)) (rest: List Cmd)
    (left lineIndent: Nat) (suffix: Trailing):
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
            | Doc.Nothing | Blank | Mark _ => fitsFrom more width modes stack rest left lineIndent suffix
            | LineSuffix _ => fitsFrom more width modes stack rest left lineIndent suffix.noted
            | BreakParent => not mode.isFlat && fitsFrom more width modes stack rest left lineIndent suffix
            | Chunk text textWidth =>
              match suffix with
                | Clear => textWidth <= left && fitsFrom more width modes stack rest (left - textWidth) lineIndent Clear
                | Pending held flatBreak =>
                  if text.all (char => char == ' ') then
                    fitsFrom more width modes stack rest left lineIndent (Pending (held + textWidth) flatBreak)
                  else
                    let broken := Nat.max indent (lineIndent + 2)
                    not flatBreak
                      && broken + textWidth <= width
                      && fitsFrom more width modes stack rest (width - broken - textWidth) broken Clear
            -- It joins the line of a waiting comment, which still waits.
            | Closing text =>
              match suffix with
                | Clear =>
                  text.length <= left && fitsFrom more width modes stack rest (left - text.length) lineIndent Clear
                | Pending held flatBreak =>
                  held + text.length <= left
                    && fitsFrom more width modes stack rest (left - held - text.length) lineIndent (Pending 0 flatBreak)
            | Line =>
              not mode.isFlat
                || (match suffix with
                  | Clear => 1 <= left && fitsFrom more width modes stack rest (left - 1) lineIndent Clear
                  | Pending held _ => fitsFrom more width modes stack rest left lineIndent (Pending held True))
            | SoftLine =>
              not mode.isFlat
                || (match suffix with
                  | Clear => fitsFrom more width modes stack rest left lineIndent Clear
                  | Pending held _ => fitsFrom more width modes stack rest left lineIndent (Pending held True))
            | HardLine | LineStart | LineStartHere | CloserLine _ => not mode.isFlat
            | Nest extra inner =>
              fitsFrom more width modes [(indent + extra, mode, inner), ..stack] rest left lineIndent suffix
            | Align inner | AlignInset inner | Displaced inner =>
              fitsFrom more width modes [(indent, mode, inner), ..stack] rest left lineIndent suffix
            | Flatten inner => fitsFrom more width modes [(indent, Flat, inner), ..stack] rest left lineIndent suffix
            | Group inner hard | NarrowGroup _ inner hard | IdGroup _ inner hard =>
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
                  | [first, .._] => fitsFrom more width modes [(indent, Flat, first)] [] left lineIndent suffix
            | OneLineBelow _ => True
            | Choice options =>
              match (if mode.isFlat then options.head else options.last) with
                | None => fitsFrom more width modes stack rest left lineIndent suffix
                | Some option => fitsFrom more width modes [(indent, mode, option), ..stack] rest left lineIndent suffix
