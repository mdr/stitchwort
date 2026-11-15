--| The printer's column is where the text is. Through every reading, the
--| `column` the printer keeps (and measures widths against) is the number
--| of characters written on the current line of its output, and a line
--| it says has only indentation has nothing on it yet (`readingTracks`).
--| So where the printer thinks a chunk starts, the indentation it owes or
--| its column, is the chunk's column in the printed text: what the lexer
--| will count for the token there.
--|
--| It holds of documents whose chunks have their texts' widths and are no
--| line breaks (`Measured`), between steps: a line break first writes the
--| waiting comments without counting them, then starts the next line.

namespace Toy.Doc.Proofs
import Toy.Doc (..)
import Std (Bool, Eq, List, Nat, Option, Text, Void)

--| The characters on the last line of the output (its pieces the last
--| first).
def lineWidth: List Text → Nat
  | [] => 0
  | [piece, ..earlier] => if piece == "\n" then 0 else piece.length + lineWidth earlier

--| The printer's place agrees with its output: with indentation owed, the
--| line is empty; otherwise the column is the line's width, and a line
--| marked as only started is empty.
def TracksParts (owed: Option Nat) (column: Nat) (atLineStart: Bool) (out: List Text): Prop := match owed with
  | Some _ => atLineStart = True ∧ lineWidth out = 0
  | None => column = lineWidth out ∧ (atLineStart = False ∨ lineWidth out = 0)

def Tracks (printer: Printer): Prop := TracksParts printer.owed printer.column printer.atLineStart printer.out

theorem startTracks ∀ (width: Nat): Tracks (Printer.start width) := Both rfl (Inr rfl)

--| A line break leaves the printer at the start of an empty line,
--| whatever it was.
theorem newlineTracks ∀ (printer: Printer) (indent: Nat): Tracks (printer.newline indent) := Both rfl rfl

theorem indentLength ∀ (indent: Nat): (" ".repeat indent).length = indent := match indent with
  | Zero => rfl
  | Succ less => Eq.cong Succ (indentLength less)

--| A line marked as only started is empty.
theorem startedEmpty ∀ (printer: Printer)
    (tracks: Tracks printer)
    (start: printer.atLineStart = True):
    lineWidth printer.out = 0 :=
  match owed: printer.owed, tracks with
    | Some indent, Both _ empty => empty
    | None, Both _ (Inr empty) => empty
    | None, Both _ (Inl other) => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym other) start))

--| Once the indentation is paid, the column is the line's width.
theorem paidTracks ∀ (printer: Printer)
    (tracks: Tracks printer):
    printer.payIndent.owed = None ∧ printer.payIndent.column = lineWidth printer.payIndent.out :=
  match owed: printer.owed, tracks with
    | None, Both column _ => Both owed column
    | Some Zero, Both _ empty => Both rfl (Eq.sym empty)
    | Some (Succ less), Both _ empty => Both rfl (rewrite empty, indentLength less in omega)

--| Text put on the line moves the column by its width.
theorem putTracks ∀ (printer: Printer) (text: Text) (width: Nat)
    (tracks: Tracks printer)
    (measured: width = text.length)
    (oneLine: (text == "\n") = False):
    Tracks (printer.put text width) :=
  match paidTracks printer tracks with
    | Both paid column =>
      let parts: TracksParts printer.payIndent.owed (printer.payIndent.column + width) False [
        text,
        ..printer.payIndent.out
      ] :=
        rewrite paid, oneLine, measured, column in Both (omega) (Inl rfl)
      parts

theorem writeTracks ∀ (printer: Printer) (indent: Nat) (text: Text) (width: Nat)
    (tracks: Tracks printer)
    (measured: width = text.length)
    (oneLine: (text == "\n") = False):
    Tracks (printer.write indent text width) :=
  match empty: text.isEmpty with
    | True => tracks
    | False =>
      match waiting: printer.suffixes.isEmpty with
        | True => putTracks printer text width tracks measured oneLine
        | False =>
          match spaces: text.all (char => char == ' ') with
            | True => tracks
            | False =>
              putTracks
                (printer.newline (printer.continuation indent))
                text
                width
                (newlineTracks printer (printer.continuation indent))
                measured
                oneLine

theorem lineStartTracks ∀ (printer: Printer) (indent: Nat)
    (tracks: Tracks printer):
    Tracks (printer.lineStart indent) :=
  match start: printer.atLineStart with
    | True => tracks
    | False => newlineTracks printer (printer.continuation indent)

theorem andTrueLeft ∀ (left right: Bool) (both: (left && right) = True): left = True := match left, both with
  | True, _ => rfl

--| A kept blank line: the line after it is empty too.
theorem blankedTracks ∀ (printer: Printer)
    (tracks: Tracks printer)
    (start: printer.atLineStart = True):
    Tracks { printer | out = ["\n", ..printer.out], newlinesAtEnd = printer.newlinesAtEnd + 1 } :=
  let empty := startedEmpty printer tracks start
  match owed: printer.owed, tracks with
    | Some indent, _ => Both start rfl
    | None, Both column _ => Both (Eq.trans column empty) (Inr rfl)

theorem blankTracks ∀ (printer: Printer) (tracks: Tracks printer): Tracks printer.blank :=
  match blank: printer.atLineStart && printer.started && printer.newlinesAtEnd < 2 with
    | False => tracks
    | True => blankedTracks printer tracks (andTrueLeft _ _ blank)

--| Indentation set at the start of a line: the line is still empty.
theorem hereTracks ∀ (printer: Printer) (indent: Nat)
    (tracks: Tracks printer)
    (start: printer.atLineStart = True):
    Tracks { printer | owed = Some indent, lineIndent = indent } :=
  Both start (startedEmpty printer tracks start)

-- Documents with honest widths.

--| Every chunk is as wide as its text is long, and is no line break.
def Measured: Doc → Prop
  | Chunk text width => width = text.length ∧ (text == "\n") = False
  | Nest _ inner => Measured inner
  | Group inner _ => Measured inner
  | Flatten inner => Measured inner
  | OneLineBelow inner => Measured inner
  | Concat docs => AllMeasured docs
  | Fill items => AllMeasured items
  | Choice options => AllMeasured options
  | _ => True

def AllMeasured: List Doc → Prop
  | [] => True
  | [doc, ..docs] => Measured doc ∧ AllMeasured docs

def CmdMeasured: Cmd → Prop
  | Print _ _ doc => Measured doc
  | FillSep _ item => Measured item

def StackMeasured: List Cmd → Prop
  | [] => True
  | [cmd, ..rest] => CmdMeasured cmd ∧ StackMeasured rest

theorem stackMeasuredAppend ∀ (front back: List Cmd)
    (frontMeasured: StackMeasured front)
    (backMeasured: StackMeasured back):
    StackMeasured (front ++ back) :=
  match front, frontMeasured with
    | [], _ => backMeasured
    | [cmd, ..rest], Both first others => Both first (stackMeasuredAppend rest back others backMeasured)

theorem printsMeasured ∀ (indent: Nat) (mode: Mode) (docs: List Doc)
    (measured: AllMeasured docs):
    StackMeasured (docs.map (Print indent mode)) :=
  match docs, measured with
    | [], _ => rfl
    | [doc, ..rest], Both first others => Both first (printsMeasured indent mode rest others)

theorem fillSepsMeasured ∀ (indent: Nat) (items: List Doc)
    (measured: AllMeasured items):
    StackMeasured (items.map (FillSep indent)) :=
  match items, measured with
    | [], _ => rfl
    | [item, ..rest], Both first others => Both first (fillSepsMeasured indent rest others)

theorem joinLinesMeasured ∀ (items: List Doc) (measured: AllMeasured items): AllMeasured (Doc.joinLines items) :=
  match items, measured with
    | [], _ => rfl
    | [only], given => given
    | [item, next, ..rest], Both first others => Both first (Both rfl (joinLinesMeasured [next, ..rest] others))

theorem optionMeasured ∀ (chosen: Doc) (options: List Doc)
    (isOption: IsOption chosen options)
    (measured: AllMeasured options):
    Measured chosen :=
  match options, isOption, measured with
    | [], picked, _ => rewrite picked in rfl
    | [last], picked, Both first _ => rewrite picked in first
    | [option, next, ..rest], Inl picked, Both first _ => rewrite picked in first
    | [option, next, ..rest], Inr later, Both _ others => optionMeasured chosen [next, ..rest] later others

theorem headOrMeasured ∀ (options: List Doc) (measured: AllMeasured options): Measured (options.headOr Empty) :=
  match options, measured with
    | [], _ => rfl
    | [option, ..others], Both first _ => first

theorem eitherTracks ∀ (condition: Bool) (yes no: (Printer, List Cmd))
    (whenYes: Tracks yes.fst)
    (whenNo: Tracks no.fst):
    Tracks (if condition then yes else no).fst :=
  match condition with
    | True => whenYes
    | False => whenNo

theorem eitherMeasured ∀ (condition: Bool) (yes no: (Printer, List Cmd))
    (whenYes: StackMeasured yes.snd)
    (whenNo: StackMeasured no.snd):
    StackMeasured (if condition then yes else no).snd :=
  match condition with
    | True => whenYes
    | False => whenNo

--| A step of a reading keeps the printer's place in step with its output.
theorem stepTracks ∀ (printer: Printer) (cmd: Cmd) (rest: List Cmd) (result: (Printer, List Cmd))
    (steps: StepsTo printer cmd rest result)
    (tracks: Tracks printer)
    (measured: CmdMeasured cmd):
    Tracks result.fst :=
  match cmd, steps, measured with
    | FillSep indent item, Inl (Both _ flat), _ => rewrite flat in writeTracks printer indent " " 1 tracks rfl rfl
    | FillSep indent item, Inr broken, _ => rewrite broken in newlineTracks printer indent
    | Print indent mode doc, steps, measured =>
      match doc, steps, measured with
        | Empty, steps, _ => rewrite steps in tracks
        | BreakParent, steps, _ => rewrite steps in tracks
        | Chunk text width, steps, Both wide oneLine =>
          rewrite steps in writeTracks printer indent text width tracks wide oneLine
        | Line, steps, _ =>
          rewrite steps in
            eitherTracks _
              (printer.write indent " " 1, rest)
              (printer.newline indent, rest)
              (writeTracks printer indent " " 1 tracks rfl rfl)
              (newlineTracks printer indent)
        | SoftLine, steps, _ =>
          rewrite steps in
            eitherTracks _ (printer, rest) (printer.newline indent, rest) tracks (newlineTracks printer indent)
        | HardLine, steps, _ => rewrite steps in newlineTracks printer indent
        | LineStart, steps, _ => rewrite steps in lineStartTracks printer indent tracks
        | CommentEnd, steps, _ => rewrite steps in newlineTracks printer printer.lineIndent
        | LineStartHere, steps, _ =>
          match start: printer.atLineStart with
            | True => rewrite steps in hereTracks printer indent tracks start
            | False => rewrite steps in newlineTracks printer indent
        | Blank, steps, _ => rewrite steps in blankTracks printer tracks
        | Nest more inner, steps, _ => rewrite steps in tracks
        | OneLineBelow inner, steps, _ => rewrite steps in tracks
        | Flatten inner, steps, _ => rewrite steps in tracks
        | LineSuffix comment, steps, _ => rewrite steps in tracks
        | Group inner hard, Inl (Both _ flat), _ => rewrite flat in tracks
        | Group inner hard, Inr (Both _ broken), _ => rewrite broken in tracks
        | Concat docs, steps, _ => rewrite steps in tracks
        | Fill [], steps, _ => rewrite steps in tracks
        | Fill [first, ..others], Inl (Both _ flat), _ => rewrite flat in tracks
        | Fill [first, ..others], Inr (Both _ (Witness firstMode broken)), _ => rewrite broken in tracks
        | Choice options, Inl (Both _ flat), _ => rewrite flat in tracks
        | Choice options, Inr (Both _ (Witness chosen (Both isOption broken))), _ => rewrite broken in tracks

--| A step of a reading leaves the work list measured.
theorem stepMeasured ∀ (printer: Printer) (cmd: Cmd) (rest: List Cmd) (result: (Printer, List Cmd))
    (steps: StepsTo printer cmd rest result)
    (measured: CmdMeasured cmd)
    (restMeasured: StackMeasured rest):
    StackMeasured result.snd :=
  match cmd, steps, measured with
    | FillSep indent item, Inl (Both _ flat), measured => rewrite flat in Both measured restMeasured
    | FillSep indent item, Inr broken, measured => rewrite broken in Both measured restMeasured
    | Print indent mode doc, steps, measured =>
      match doc, steps, measured with
        | Empty, steps, _ => rewrite steps in restMeasured
        | BreakParent, steps, _ => rewrite steps in restMeasured
        | Chunk text width, steps, _ => rewrite steps in restMeasured
        | Line, steps, _ =>
          rewrite steps in
            eitherMeasured _ (printer.write indent " " 1, rest) (printer.newline indent, rest) restMeasured restMeasured
        | SoftLine, steps, _ =>
          rewrite steps in eitherMeasured _ (printer, rest) (printer.newline indent, rest) restMeasured restMeasured
        | HardLine, steps, _ => rewrite steps in restMeasured
        | LineStart, steps, _ => rewrite steps in restMeasured
        | CommentEnd, steps, _ => rewrite steps in restMeasured
        | LineStartHere, steps, _ =>
          rewrite steps in
            eitherMeasured _
              ({ printer | owed = Some indent, lineIndent = indent }, rest)
              (printer.newline indent, rest)
              restMeasured
              restMeasured
        | Blank, steps, _ => rewrite steps in restMeasured
        | Nest more inner, steps, measured => rewrite steps in Both measured restMeasured
        | OneLineBelow inner, steps, measured => rewrite steps in Both rfl (Both measured restMeasured)
        | Flatten inner, steps, measured => rewrite steps in Both measured restMeasured
        | LineSuffix comment, steps, _ => rewrite steps in restMeasured
        | Group inner hard, Inl (Both _ flat), measured => rewrite flat in Both measured restMeasured
        | Group inner hard, Inr (Both _ broken), measured => rewrite broken in Both measured restMeasured
        | Concat docs, steps, measured =>
          rewrite steps in
            stackMeasuredAppend
              (docs.map (Print indent mode))
              rest
              (printsMeasured indent mode docs measured)
              restMeasured
        | Fill [], steps, _ => rewrite steps in restMeasured
        | Fill [first, ..others], Inl (Both _ flat), measured =>
          rewrite flat in
            stackMeasuredAppend
              ((Doc.joinLines [first, ..others]).map (Print indent Flat))
              rest
              (printsMeasured indent Flat
                (Doc.joinLines [first, ..others])
                (joinLinesMeasured [first, ..others] measured))
              restMeasured
        | Fill [first, ..others], Inr (Both _ (Witness firstMode broken)), Both firstMeasured othersMeasured =>
          rewrite broken in
            Both firstMeasured
              (stackMeasuredAppend
                (others.map (FillSep indent))
                rest
                (fillSepsMeasured indent others othersMeasured)
                restMeasured)
        | Choice options, Inl (Both _ flat), measured =>
          rewrite flat in Both (headOrMeasured options measured) restMeasured
        | Choice options, Inr (Both _ (Witness chosen (Both isOption broken))), measured =>
          rewrite broken in Both (optionMeasured chosen options isOption measured) restMeasured

--| Through every reading of measured documents, however far it gets, the
--| printer's place stays in step with its output: the column it counts is
--| the width of the line it has written.
theorem readingTracks ∀ (printer: Printer) (fuel: Nat) (stack: List Cmd) (final: Printer)
    (reads: Reads printer fuel stack final)
    (tracks: Tracks printer)
    (measured: StackMeasured stack):
    Tracks final :=
  match fuel, stack, reads, measured with
    | Zero, [], reads, _ => rewrite reads in tracks
    | Succ more, [], reads, _ => rewrite reads in tracks
    | Zero, [cmd, ..rest], reads, _ => rewrite reads in tracks
    | Succ more, [cmd, ..rest], Witness next (Witness later (Both steps laterReads)), Both first others =>
      readingTracks next more later final laterReads
        (stepTracks printer cmd rest (next, later) steps tracks first)
        (stepMeasured printer cmd rest (next, later) steps first others)
