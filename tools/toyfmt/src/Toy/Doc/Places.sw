--| Where the printer puts each word. Through every reading, each word
--| written is at the place the document's own predicate (`Lays`) listed
--| for it: after other words on its line, or first on a line indented as
--| the document says (`printLays`). The trace of a print, each word with
--| the column it starts its line at, if it does, is `eventsOf` of the
--| printed pieces, which is what the lexer will see of them: a token
--| starts its line when only spaces come before it there, at the column
--| the line is wide.
--|
--| `Lays` is in continuation style, as `Joins` is: from the place the
--| printer is at and the trace so far, a document hands every place and
--| trace it may leave to what comes after. It doesn't follow modes: a
--| `Line` may be a space or a break wherever it stands.

namespace Toy.Doc.Proofs
import Toy.Doc (..)
import Std (Bool, DecEq, Eq, List, Nat, Option, Text, Void)

--| Whether the last line of the output (its pieces the last first) has
--| nothing but spaces on it.
def lineBlank: List Text → Bool
  | [] => True
  | [piece, ..earlier] => if piece.all (char => char == ' ') then lineBlank earlier else piece == "\n"

--| A word as printed: `start` is the column it starts its line at, or
--| `None` if other words come before it on the line.
type Event = { word: Text, start: Option Nat }

--| The words of the output (its pieces the last first), in the order
--| printed, each with where it starts its line.
def eventsOf: List Text → List Event
  | [] => []
  | [piece, ..earlier] =>
    if isLayout piece then eventsOf earlier
    else eventsOf earlier ++ [{ word = piece, start = if lineBlank earlier then Some (lineWidth earlier) else None }]

--| Where the printer is on its line.
type Place =
  --| Nothing but indentation on the line; the next word starts it at
  --| column `indent`.
  | AtStart (indent: Nat)
  --| Words on the line, which is indented `indent`.
  | Mid (indent: Nat)
  --| As `Mid`, with a trailing comment waiting for the end of the line.
  | Held (indent: Nat)

--| A chunk in a construct indented `indent`: nothing if empty; spaces
--| after words (never at a line start, where they would move the next
--| word); a word where the place says, on a new line after a waiting
--| comment.
def WriteLays (indent: Nat) (text: Text) (place: Place) (trace: List Event) (next: Place → List Event → Prop): Prop :=
  if text.isEmpty then next place trace
  else if text.all (char => char == ' ') then
    match place with
      | AtStart _ => False
      | Mid at => next (Mid at) trace
      | Held at => next (Held at) trace
  else
    (text == "\n") = False
      ∧ (match place with
        | AtStart at => next (Mid at) (trace ++ [{ word = text, start = Some at }])
        | Mid at => next (Mid at) (trace ++ [{ word = text, start = None }])
        | Held at =>
          next (Mid (Nat.max indent (at + 2))) (trace ++ [{ word = text, start = Some (Nat.max indent (at + 2)) }]))

--| A `Line` or a fill's separator: a space or a line break, after words.
def SepLays (indent: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop): Prop := match place with
  | AtStart _ => False
  | Mid at => next (Mid at) trace ∧ next (AtStart indent) trace
  | Held _ => next (AtStart indent) trace

--| A `SoftLine`: nothing or a line break; a line break if a comment waits.
def SoftLays (indent: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop): Prop := match place with
  | AtStart at => next (AtStart at) trace ∧ next (AtStart indent) trace
  | Mid at => next (Mid at) trace ∧ next (AtStart indent) trace
  | Held _ => next (AtStart indent) trace

--| A `LineStart`: a comment break, deeper than the line, unless a line
--| starts here.
def StartLays (indent: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop): Prop := match place with
  | AtStart at => next (AtStart at) trace
  | Mid at => next (AtStart (Nat.max indent (at + 2))) trace
  | Held at => next (AtStart (Nat.max indent (at + 2))) trace

--| A trailing comment: after words on its line, with no other waiting.
def SuffixLays (comment: Text) (place: Place) (trace: List Event) (next: Place → List Event → Prop): Prop := match place with
  | AtStart _ => False
  | Mid at => next (Held at) (trace ++ [{ word = comment, start = None }])
  | Held _ => False

--| From `place` with `trace` printed, every way `doc` may print in a
--| construct indented `indent` puts its words where `next` is told, and
--| every place it may leave satisfies `next`.
def Lays (doc: Doc) (indent: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop): Prop := match doc with
  | Empty => next place trace
  | BreakParent => next place trace
  | Blank => next place trace
  | Chunk text _ => WriteLays indent text place trace next
  | Line => SepLays indent place trace next
  | SoftLine => SoftLays indent place trace next
  | HardLine => next (AtStart indent) trace
  | CommentEnd => next (AtStart place.indent) trace
  | LineStart => StartLays indent place trace next
  | LineStartHere => next (AtStart indent) trace
  | Nest more inner => Lays inner (indent + more) place trace next
  | Group inner _ => Lays inner indent place trace next
  | Flatten inner => Lays inner indent place trace next
  | OneLineBelow inner => Lays inner (indent + 2) (AtStart (indent + 2)) trace next
  | Concat docs => LaysAll docs indent place trace next
  | Fill items => FillLays items indent place trace next
  | Choice options => OptionsLay options indent place trace next
  | LineSuffix comment => isLayout comment = False ∧ SuffixLays comment place trace next

def LaysAll (docs: List Doc) (indent: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop): Prop := match docs with
  | [] => next place trace
  | [doc, ..rest] => Lays doc indent place trace (after later => LaysAll rest indent after later next)

def FillLays (items: List Doc) (indent: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop): Prop := match items with
  | [] => next place trace
  | [first, ..others] => Lays first indent place trace (after later => SepsLay others indent after later next)

def SepsLay (items: List Doc) (indent: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop): Prop := match items with
  | [] => next place trace
  | [item, ..more] =>
    SepLays indent place trace (middle between =>
      Lays item indent middle between (after later => SepsLay more indent after later next))

def OptionsLay (options: List Doc) (indent: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop): Prop := match options with
  | [] => next place trace
  | [last] => Lays last indent place trace next
  | [option, ..others] => Lays option indent place trace next ∧ OptionsLay others indent place trace next

--| The work list, from `place` to the end, where `spec` is asked of the
--| place and the whole trace.
def StackLays (spec: Place → List Event → Prop) (stack: List Cmd) (place: Place) (trace: List Event): Prop := match stack with
  | [] => spec place trace
  | [Print indent _ doc, ..rest] => Lays doc indent place trace (after later => StackLays spec rest after later)
  | [FillSep indent item, ..rest] =>
    SepLays indent place trace (middle between =>
      Lays item indent middle between (after later => StackLays spec rest after later))

-- A weaker continuation still holds.

theorem writeLaysWeaker ∀ (indent: Nat) (text: Text) (place: Place) (trace: List Event)
    (strong weak: Place → List Event → Prop)
    (implies: ∀ (after: Place) (later: List Event) => strong after later → weak after later)
    (lays: WriteLays indent text place trace strong):
    WriteLays indent text place trace weak :=
  match empty: text.isEmpty, lays with
    | True, lays => implies _ _ lays
    | False, lays =>
      match spaces: text.all (char => char == ' '), lays with
        | True, lays =>
          match place, lays with
            | AtStart at, never => never
            | Mid at, lays => implies _ _ lays
            | Held at, lays => implies _ _ lays
        | False, Both oneLine lays =>
          match place, lays with
            | AtStart at, lays => Both oneLine (implies _ _ lays)
            | Mid at, lays => Both oneLine (implies _ _ lays)
            | Held at, lays => Both oneLine (implies _ _ lays)

theorem sepLaysWeaker ∀ (indent: Nat) (place: Place) (trace: List Event)
    (strong weak: Place → List Event → Prop)
    (implies: ∀ (after: Place) (later: List Event) => strong after later → weak after later)
    (lays: SepLays indent place trace strong):
    SepLays indent place trace weak :=
  match place, lays with
    | AtStart at, never => never
    | Mid at, Both same broken => Both (implies _ _ same) (implies _ _ broken)
    | Held at, broken => implies _ _ broken

theorem softLaysWeaker ∀ (indent: Nat) (place: Place) (trace: List Event)
    (strong weak: Place → List Event → Prop)
    (implies: ∀ (after: Place) (later: List Event) => strong after later → weak after later)
    (lays: SoftLays indent place trace strong):
    SoftLays indent place trace weak :=
  match place, lays with
    | AtStart at, Both same broken => Both (implies _ _ same) (implies _ _ broken)
    | Mid at, Both same broken => Both (implies _ _ same) (implies _ _ broken)
    | Held at, broken => implies _ _ broken

theorem startLaysWeaker ∀ (indent: Nat) (place: Place) (trace: List Event)
    (strong weak: Place → List Event → Prop)
    (implies: ∀ (after: Place) (later: List Event) => strong after later → weak after later)
    (lays: StartLays indent place trace strong):
    StartLays indent place trace weak :=
  match place, lays with
    | AtStart at, lays => implies _ _ lays
    | Mid at, lays => implies _ _ lays
    | Held at, lays => implies _ _ lays

theorem suffixLaysWeaker ∀ (comment: Text) (place: Place) (trace: List Event)
    (strong weak: Place → List Event → Prop)
    (implies: ∀ (after: Place) (later: List Event) => strong after later → weak after later)
    (lays: SuffixLays comment place trace strong):
    SuffixLays comment place trace weak :=
  match place, lays with
    | AtStart at, never => never
    | Mid at, lays => implies _ _ lays
    | Held at, never => never

--| What holds with a continuation holds with any it implies.
theorem laysWeaker ∀ (doc: Doc) (indent: Nat) (place: Place) (trace: List Event)
    (strong weak: Place → List Event → Prop)
    (implies: ∀ (after: Place) (later: List Event) => strong after later → weak after later)
    (lays: Lays doc indent place trace strong):
    Lays doc indent place trace weak :=
  match doc, lays with
    | Empty, lays => implies _ _ lays
    | BreakParent, lays => implies _ _ lays
    | Blank, lays => implies _ _ lays
    | Chunk text width, lays => writeLaysWeaker indent text place trace strong weak implies lays
    | Line, lays => sepLaysWeaker indent place trace strong weak implies lays
    | SoftLine, lays => softLaysWeaker indent place trace strong weak implies lays
    | HardLine, lays => implies _ _ lays
    | CommentEnd, lays => implies _ _ lays
    | LineStart, lays => startLaysWeaker indent place trace strong weak implies lays
    | LineStartHere, lays => implies _ _ lays
    | Nest more inner, lays => laysWeaker inner (indent + more) place trace strong weak implies lays
    | Group inner hard, lays => laysWeaker inner indent place trace strong weak implies lays
    | Flatten inner, lays => laysWeaker inner indent place trace strong weak implies lays
    | OneLineBelow inner, lays =>
      laysWeaker inner (indent + 2) (AtStart (indent + 2)) trace strong weak implies lays
    | Concat docs, lays => allLaysWeaker docs indent place trace strong weak implies lays
    | Fill items, lays => fillLaysWeaker items indent place trace strong weak implies lays
    | Choice options, lays => optionsLayWeaker options indent place trace strong weak implies lays
    | LineSuffix comment, Both word lays =>
      Both word (suffixLaysWeaker comment place trace strong weak implies lays)

theorem allLaysWeaker ∀ (docs: List Doc) (indent: Nat) (place: Place) (trace: List Event)
    (strong weak: Place → List Event → Prop)
    (implies: ∀ (after: Place) (later: List Event) => strong after later → weak after later)
    (lays: LaysAll docs indent place trace strong):
    LaysAll docs indent place trace weak :=
  match docs, lays with
    | [], lays => implies _ _ lays
    | [doc, ..rest], lays =>
      laysWeaker doc indent place trace
        (after later => LaysAll rest indent after later strong)
        (after later => LaysAll rest indent after later weak)
        (after later others => allLaysWeaker rest indent after later strong weak implies others)
        lays

theorem fillLaysWeaker ∀ (items: List Doc) (indent: Nat) (place: Place) (trace: List Event)
    (strong weak: Place → List Event → Prop)
    (implies: ∀ (after: Place) (later: List Event) => strong after later → weak after later)
    (lays: FillLays items indent place trace strong):
    FillLays items indent place trace weak :=
  match items, lays with
    | [], lays => implies _ _ lays
    | [first, ..others], lays =>
      laysWeaker first indent place trace
        (after later => SepsLay others indent after later strong)
        (after later => SepsLay others indent after later weak)
        (after later seps => sepsLayWeaker others indent after later strong weak implies seps)
        lays

theorem sepsLayWeaker ∀ (items: List Doc) (indent: Nat) (place: Place) (trace: List Event)
    (strong weak: Place → List Event → Prop)
    (implies: ∀ (after: Place) (later: List Event) => strong after later → weak after later)
    (lays: SepsLay items indent place trace strong):
    SepsLay items indent place trace weak :=
  match items, lays with
    | [], lays => implies _ _ lays
    | [item, ..more], lays =>
      sepLaysWeaker indent place trace
        (middle between => Lays item indent middle between (after later => SepsLay more indent after later strong))
        (middle between => Lays item indent middle between (after later => SepsLay more indent after later weak))
        (middle between inner =>
          laysWeaker item indent middle between
            (after later => SepsLay more indent after later strong)
            (after later => SepsLay more indent after later weak)
            (after later seps => sepsLayWeaker more indent after later strong weak implies seps)
            inner)
        lays

theorem optionsLayWeaker ∀ (options: List Doc) (indent: Nat) (place: Place) (trace: List Event)
    (strong weak: Place → List Event → Prop)
    (implies: ∀ (after: Place) (later: List Event) => strong after later → weak after later)
    (lays: OptionsLay options indent place trace strong):
    OptionsLay options indent place trace weak :=
  match options, lays with
    | [], lays => implies _ _ lays
    | [last], lays => laysWeaker last indent place trace strong weak implies lays
    | [option, second, ..others], Both first rest =>
      Both
        (laysWeaker option indent place trace strong weak implies first)
        (optionsLayWeaker [second, ..others] indent place trace strong weak implies rest)

-- What a step pushes on the work list lays as the document it came from.

theorem printsLay ∀ (spec: Place → List Event → Prop) (indent: Nat) (mode: Mode) (docs: List Doc)
    (rest: List Cmd) (place: Place) (trace: List Event)
    (lays: LaysAll docs indent place trace (after later => StackLays spec rest after later)):
    StackLays spec (docs.map (Print indent mode) ++ rest) place trace :=
  match docs, lays with
    | [], lays => lays
    | [doc, ..others], lays =>
      laysWeaker doc indent place trace
        (after later => LaysAll others indent after later (final last => StackLays spec rest final last))
        (after later => StackLays spec (others.map (Print indent mode) ++ rest) after later)
        (after later more => printsLay spec indent mode others rest after later more)
        lays

theorem linesLay ∀ (first: Doc) (others: List Doc) (indent: Nat) (place: Place) (trace: List Event)
    (next: Place → List Event → Prop)
    (lays: Lays first indent place trace (after later => SepsLay others indent after later next)):
    LaysAll (Doc.joinLines [first, ..others]) indent place trace next :=
  match others, lays with
    | [], lays => lays
    | [second, ..rest], lays =>
      laysWeaker first indent place trace
        (after later => SepsLay [second, ..rest] indent after later next)
        (after later => LaysAll [Line, ..Doc.joinLines [second, ..rest]] indent after later next)
        (after later seps =>
          sepLaysWeaker indent after later
            (middle between => Lays second indent middle between (final last => SepsLay rest indent final last next))
            (middle between => LaysAll (Doc.joinLines [second, ..rest]) indent middle between next)
            (middle between inner => linesLay second rest indent middle between next inner)
            seps)
        lays

theorem fillSepsLay ∀ (spec: Place → List Event → Prop) (indent: Nat) (items: List Doc) (rest: List Cmd)
    (place: Place) (trace: List Event)
    (lays: SepsLay items indent place trace (after later => StackLays spec rest after later)):
    StackLays spec (items.map (FillSep indent) ++ rest) place trace :=
  match items, lays with
    | [], lays => lays
    | [item, ..more], lays =>
      sepLaysWeaker indent place trace
        (middle between =>
          Lays item indent middle between (after later =>
            SepsLay more indent after later (final last => StackLays spec rest final last)))
        (middle between =>
          Lays item indent middle between (after later =>
            StackLays spec (more.map (FillSep indent) ++ rest) after later))
        (middle between inner =>
          laysWeaker item indent middle between
            (after later => SepsLay more indent after later (final last => StackLays spec rest final last))
            (after later => StackLays spec (more.map (FillSep indent) ++ rest) after later)
            (after later seps => fillSepsLay spec indent more rest after later seps)
            inner)
        lays

theorem optionLays ∀ (chosen: Doc) (options: List Doc) (indent: Nat) (place: Place) (trace: List Event)
    (next: Place → List Event → Prop)
    (isOption: IsOption chosen options)
    (lays: OptionsLay options indent place trace next):
    Lays chosen indent place trace next :=
  match options, isOption, lays with
    | [], picked, lays => rewrite picked in lays
    | [last], picked, lays => rewrite picked in lays
    | [option, second, ..others], Inl picked, Both first _ => rewrite picked in first
    | [option, second, ..others], Inr later, Both _ rest =>
      optionLays chosen [second, ..others] indent place trace next later rest

theorem headOrLays ∀ (options: List Doc) (indent: Nat) (place: Place) (trace: List Event)
    (next: Place → List Event → Prop)
    (lays: OptionsLay options indent place trace next):
    Lays (options.headOr Empty) indent place trace next :=
  match options, lays with
    | [], lays => lays
    | [last], lays => lays
    | [option, second, ..others], Both first _ => first

-- The output's side: events, blank lines and widths, a piece at a time.

theorem gapNoBreak ∀ (piece: Text) (gap: piece.all (char => char == ' ') = True): (piece == "\n") = False :=
  match isBreak: piece == "\n" with
    | False => rfl
    | True =>
      let same: piece = "\n" := DecEq.sound isBreak
      let never: "\n".all (char => char == ' ') = True := rewrite <- same in gap
      Void.exfalso (Bool.falseNotTrue never)

theorem gapLayout ∀ (piece: Text) (gap: piece.all (char => char == ' ') = True): isLayout piece = True :=
  Eq.cong ((spaces: Bool) => spaces || piece == "\n") gap

theorem eventsWord ∀ (piece: Text) (earlier: List Text)
    (word: isLayout piece = False):
    eventsOf [piece, ..earlier]
      = eventsOf earlier ++ [{ word = piece, start = if lineBlank earlier then Some (lineWidth earlier) else None }] :=
  match layout: isLayout piece, word with
    | False, _ => rfl
    | True, never => Void.exfalso (Bool.falseNotTrue (Eq.sym never))

theorem eventsLayout ∀ (piece: Text) (earlier: List Text)
    (layout: isLayout piece = True):
    eventsOf [piece, ..earlier] = eventsOf earlier :=
  match is: isLayout piece, layout with
    | True, _ => rfl
    | False, never => Void.exfalso (Bool.falseNotTrue never)

theorem blankWord ∀ (piece: Text) (earlier: List Text)
    (word: isLayout piece = False):
    lineBlank [piece, ..earlier] = False :=
  match gap: piece.all (char => char == ' '), word with
    | True, never => Void.exfalso (Bool.falseNotTrue (Eq.sym never))
    | False, word => word

theorem blankGap ∀ (piece: Text) (earlier: List Text)
    (gap: piece.all (char => char == ' ') = True):
    lineBlank [piece, ..earlier] = lineBlank earlier :=
  match spaces: piece.all (char => char == ' '), gap with
    | True, _ => rfl
    | False, never => Void.exfalso (Bool.falseNotTrue never)

theorem widthPiece ∀ (piece: Text) (earlier: List Text)
    (oneLine: (piece == "\n") = False):
    lineWidth [piece, ..earlier] = piece.length + lineWidth earlier :=
  match isBreak: piece == "\n", oneLine with
    | False, _ => rfl
    | True, never => Void.exfalso (Bool.falseNotTrue (Eq.sym never))

theorem trimKeep ∀ (last: Text) (earlier: List Text)
    (word: last.all (char => char == ' ') = False):
    trimSpaces [last, ..earlier] = [last, ..earlier] :=
  match spaces: last.all (char => char == ' '), word with
    | False, _ => rfl
    | True, never => Void.exfalso (Bool.falseNotTrue (Eq.sym never))

theorem trimDrop ∀ (last: Text) (earlier: List Text)
    (gap: last.all (char => char == ' ') = True):
    trimSpaces [last, ..earlier] = trimSpaces earlier :=
  match spaces: last.all (char => char == ' '), gap with
    | True, _ => rfl
    | False, never => Void.exfalso (Bool.falseNotTrue never)

theorem trimEventsBy ∀ (last: Text) (earlier: List Text) (spaces: Bool)
    (is: last.all (char => char == ' ') = spaces)
    (rest: eventsOf (trimSpaces earlier) = eventsOf earlier):
    eventsOf (trimSpaces [last, ..earlier]) = eventsOf [last, ..earlier] :=
  match spaces, is with
    | True, gap =>
      rewrite trimDrop last earlier gap in
        Eq.trans rest (Eq.sym (eventsLayout last earlier (gapLayout last gap)))
    | False, word => rewrite trimKeep last earlier word in rfl

--| The spaces a line break drops are no words.
theorem trimEvents ∀ (out: List Text): eventsOf (trimSpaces out) = eventsOf out := match out with
  | [] => rfl
  | [last, ..earlier] => trimEventsBy last earlier _ rfl (trimEvents earlier)

theorem trimBlankBy ∀ (last: Text) (earlier: List Text) (spaces: Bool)
    (is: last.all (char => char == ' ') = spaces)
    (rest: lineBlank (trimSpaces earlier) = lineBlank earlier):
    lineBlank (trimSpaces [last, ..earlier]) = lineBlank [last, ..earlier] :=
  match spaces, is with
    | True, gap => rewrite trimDrop last earlier gap in Eq.trans rest (Eq.sym (blankGap last earlier gap))
    | False, word => rewrite trimKeep last earlier word in rfl

theorem trimBlank ∀ (out: List Text): lineBlank (trimSpaces out) = lineBlank out := match out with
  | [] => rfl
  | [last, ..earlier] => trimBlankBy last earlier _ rfl (trimBlank earlier)

-- The printer's side: where it is agrees with its output.

--| The printer is at `place` with `trace` printed: a line start has
--| nothing but the indentation owed; a comment that waits is already in
--| the trace, after the words written.
def AgreesParts (out: List Text) (owed: Option Nat) (atLineStart: Bool) (suffixes: List Text) (lineIndent: Nat)
    (place: Place) (trace: List Event): Prop :=
  match place with
    | AtStart at =>
      atLineStart = True
        ∧ suffixes = []
        ∧ lineBlank out = True
        ∧ lineWidth out = 0
        ∧ owed.getOrElse 0 = at
        ∧ lineIndent = at
        ∧ trace = eventsOf out
    | Mid at =>
      atLineStart = False ∧ suffixes = [] ∧ lineBlank out = False ∧ owed = None ∧ lineIndent = at ∧ trace = eventsOf out
    | Held at =>
      atLineStart = False
        ∧ (∃ (comment: Text) => suffixes = [comment]
          ∧ isLayout comment = False
          ∧ trace = eventsOf out ++ [{ word = comment, start = None }])
        ∧ lineBlank out = False
        ∧ owed = None
        ∧ lineIndent = at

def Agrees (printer: Printer) (place: Place) (trace: List Event): Prop :=
  AgreesParts printer.out printer.owed printer.atLineStart printer.suffixes printer.lineIndent place trace

--| The printer is at a place and trace that `next` holds of.
def Stays (next: Place → List Event → Prop) (printer: Printer): Prop :=
  ∃ (place: Place) => ∃ (trace: List Event) => Agrees printer place trace ∧ next place trace

theorem someNotNone ∀ (value: Nat) (wrong: Some value = None): Void := cases

theorem consNotNil ∀ (first: Text) (more: List Text) (wrong: [first, ..more] = []): Void := cases

--| A word put at a line start starts the line, at the indentation owed.
theorem putStart ∀ (printer: Printer) (text: Text) (width at: Nat) (trace: List Event)
    (agrees: Agrees printer (AtStart at) trace)
    (word: isLayout text = False):
    Agrees (printer.put text width) (Mid at) (trace ++ [{ word = text, start = Some at }]) :=
  match printer, agrees with
    | { width = total, out, column, owed, atLineStart, suffixes, lineIndent, newlinesAtEnd, started },
      Both start (Both none (Both blank (Both empty (Both owes (Both indent same))))) =>
      match owed, owes with
        | None, owes =>
          Both rfl
            (Both none
              (Both (blankWord text out word)
                (Both rfl (Both indent (rewrite <- owes, eventsWord text out word, blank, empty, same in rfl)))))
        | Some Zero, owes =>
          Both rfl
            (Both none
              (Both (blankWord text out word)
                (Both rfl (Both indent (rewrite <- owes, eventsWord text out word, blank, empty, same in rfl)))))
        | Some (Succ less), owes =>
          let lay: isLayout (" ".repeat (Succ less)) = True := gapLayout _ (indentSpaces (Succ less))
          let stillBlank: lineBlank [" ".repeat (Succ less), ..out] = True :=
            Eq.trans (blankGap (" ".repeat (Succ less)) out (indentSpaces (Succ less))) blank
          let sum := widthPiece (" ".repeat (Succ less)) out (gapNoBreak _ (indentSpaces (Succ less)))
          let length := indentLength (Succ less)
          let wide: lineWidth [" ".repeat (Succ less), ..out] = Succ less := omega
          Both rfl
            (Both none
              (Both (blankWord text [" ".repeat (Succ less), ..out] word)
                (Both rfl
                  (Both indent
                    (rewrite <- owes,
                        eventsWord text [" ".repeat (Succ less), ..out] word,
                        eventsLayout (" ".repeat (Succ less)) out lay,
                        stillBlank,
                        wide,
                        same in
                      rfl)))))

--| A word put after words on its line doesn't start the line.
theorem putMid ∀ (printer: Printer) (text: Text) (width at: Nat) (trace: List Event)
    (agrees: Agrees printer (Mid at) trace)
    (word: isLayout text = False):
    Agrees (printer.put text width) (Mid at) (trace ++ [{ word = text, start = None }]) :=
  match printer, agrees with
    | { width = total, out, column, owed, atLineStart, suffixes, lineIndent, newlinesAtEnd, started },
      Both start (Both none (Both blank (Both owes (Both indent same)))) =>
      match owed, owes with
        | Some value, never => Void.exfalso (someNotNone value never)
        | None, _ =>
          Both rfl
            (Both none
              (Both (blankWord text out word)
                (Both rfl (Both indent (rewrite eventsWord text out word, blank, same in rfl)))))

--| Spaces put after words change nothing but the width.
theorem putSpaces ∀ (printer: Printer) (text: Text) (width at: Nat) (trace: List Event)
    (agrees: Agrees printer (Mid at) trace)
    (gap: text.all (char => char == ' ') = True):
    Agrees (printer.put text width) (Mid at) trace :=
  match printer, agrees with
    | { width = total, out, column, owed, atLineStart, suffixes, lineIndent, newlinesAtEnd, started },
      Both start (Both none (Both blank (Both owes (Both indent same)))) =>
      match owed, owes with
        | Some value, never => Void.exfalso (someNotNone value never)
        | None, _ =>
          Both rfl
            (Both none
              (Both (Eq.trans (blankGap text out gap) blank)
                (Both rfl (Both indent (Eq.trans same (Eq.sym (eventsLayout text out (gapLayout text gap))))))))

--| After a line break the printer is at the start of a line indented as
--| asked, and a comment that waited is written where the trace has it.
theorem newlineAgrees ∀ (printer: Printer) (indent: Nat) (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace):
    Agrees (printer.newline indent) (AtStart indent) trace :=
  match printer, place, agrees with
    | { width = total, out, column, owed, atLineStart, suffixes, lineIndent, newlinesAtEnd, started },
      AtStart at,
      Both start (Both none (Both blank (Both empty (Both owes (Both same events))))) =>
      match suffixes, none with
        | [first, ..more], never => Void.exfalso (consNotNil first more never)
        | [], _ =>
          Both rfl (Both rfl (Both rfl (Both rfl (Both rfl (Both rfl (Eq.trans events (Eq.sym (trimEvents out))))))))
    | { width = total, out, column, owed, atLineStart, suffixes, lineIndent, newlinesAtEnd, started },
      Mid at,
      Both start (Both none (Both blank (Both owes (Both same events)))) =>
      match suffixes, none with
        | [first, ..more], never => Void.exfalso (consNotNil first more never)
        | [], _ =>
          Both rfl (Both rfl (Both rfl (Both rfl (Both rfl (Both rfl (Eq.trans events (Eq.sym (trimEvents out))))))))
    | { width = total, out, column, owed, atLineStart, suffixes, lineIndent, newlinesAtEnd, started },
      Held at,
      Both start (Both (Witness comment (Both one (Both word events))) (Both blank (Both owes same))) =>
      let written: eventsOf [comment, " ", ..trimSpaces out] = eventsOf out ++ [{ word = comment, start = None }] :=
        rewrite eventsWord comment [" ", ..trimSpaces out] word, trimBlank out, blank, trimEvents out in rfl
      rewrite one, start in
        Both rfl (Both rfl (Both rfl (Both rfl (Both rfl (Both rfl (Eq.trans events (Eq.sym written)))))))
