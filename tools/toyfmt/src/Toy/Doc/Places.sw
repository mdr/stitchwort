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
--| `None` if other words come before it on the line. A blank line is an
--| event too (`Event.blankLine`).
type Event = { word: Text, start: Option Nat }

--| A blank line: the line break that ends a line with nothing but spaces
--| on it. No word is `"\n"`, so no word's event is this one.
def Event.blankLine: Event := { word = "\n", start = None }

--| The words of the output (its pieces the last first), in the order
--| printed, each with where it starts its line, and its blank lines: a
--| line break on a line with nothing but spaces is one, as it is to the
--| lexer (`Toy.Fmt.Proofs.placePiece`).
def eventsOf: List Text → List Event
  | [] => []
  | [piece, ..earlier] =>
    if isLayout piece then
      if piece == "\n" && lineBlank earlier then eventsOf earlier ++ [Event.blankLine] else eventsOf earlier
    else eventsOf earlier ++ [{ word = piece, start = if lineBlank earlier then Some (lineWidth earlier) else None }]

--| Where the printer is on its line.
type Place =
  --| Nothing but indentation on the line; the next word starts it at
  --| column `indent`.
  | AtStart (indent: Nat)
  --| As `AtStart`, right after the line break that ended a line of
  --| words: the one place a `Blank` leaves a blank line.
  | Broken (indent: Nat)
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
      | Broken _ => False
      | Mid at => next (Mid at) trace
      | Held at => next (Held at) trace
  else
    (text == "\n") = False
      ∧ (match place with
        | AtStart at => next (Mid at) (trace ++ [{ word = text, start = Some at }])
        | Broken at => next (Mid at) (trace ++ [{ word = text, start = Some at }])
        | Mid at => next (Mid at) (trace ++ [{ word = text, start = None }])
        | Held at =>
          next (Mid (Nat.max indent (at + 2))) (trace ++ [{ word = text, start = Some (Nat.max indent (at + 2)) }]))

--| Whether words are on the line: a line break here ends their line, and
--| leaves no blank line.
def Place.midLine: Place → Bool
  | AtStart _ => False
  | Broken _ => False
  | Mid _ => True
  | Held _ => True

--| A `Line` or a fill's separator: a space or a line break, after words.
def SepLays (indent: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop): Prop := match place with
  | AtStart _ => False
  | Broken _ => False
  | Mid at => next (Mid at) trace ∧ next (AtStart indent) trace
  | Held _ => next (AtStart indent) trace

--| A `SoftLine`: nothing or a line break, after words; a line break if a
--| comment waits.
def SoftLays (indent: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop): Prop :=
  match place with
    | AtStart _ => False
    | Broken _ => False
    | Mid at => next (Mid at) trace ∧ next (AtStart indent) trace
    | Held _ => next (AtStart indent) trace

--| A `LineStart`: a comment break, deeper than the line, unless a line
--| starts here.
def StartLays (indent: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop): Prop :=
  match place with
    | AtStart at => next (AtStart at) trace
    | Broken at => next (AtStart at) trace
    | Mid at => next (AtStart (Nat.max indent (at + 2))) trace
    | Held at => next (AtStart (Nat.max indent (at + 2))) trace

--| A trailing comment: after words on its line, with no other waiting.
def SuffixLays (comment: Text) (place: Place) (trace: List Event) (next: Place → List Event → Prop): Prop :=
  match place with
    | AtStart _ => False
    | Broken _ => False
    | Mid at => next (Held at) (trace ++ [{ word = comment, start = None }])
    | Held _ => False

--| A `Blank`: a blank line right after the line break that ended a line
--| of words; nothing after words; at no other line start, where the
--| printer may or may not leave one.
def BlankLays (place: Place) (trace: List Event) (next: Place → List Event → Prop): Prop := match place with
  | AtStart _ => False
  | Broken at => next (AtStart at) (trace ++ [Event.blankLine])
  | Mid at => next (Mid at) trace
  | Held at => next (Held at) trace

--| From `place` with `trace` printed, every way `doc` may print in a
--| construct indented `indent` puts its words where `next` is told, and
--| every place it may leave satisfies `next`. A line break that isn't a
--| `Line` or `SoftLine` comes only after words (at a line start it would
--| leave a blank line); after a `HardLine` the document says whether a
--| `Blank` follows (`Broken`) or not (`AtStart`).
def Lays (doc: Doc) (indent: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop): Prop :=
  match doc with
    | Empty => next place trace
    | BreakParent => next place trace
    | Blank => BlankLays place trace next
    | Chunk text _ => WriteLays indent text place trace next
    | Line => SepLays indent place trace next
    | SoftLine => SoftLays indent place trace next
    | HardLine => place.midLine = True ∧ (next (Broken indent) trace ∨ next (AtStart indent) trace)
    | CommentEnd => place.midLine = True ∧ next (AtStart place.indent) trace
    | LineStart => StartLays indent place trace next
    | LineStartHere => next (AtStart indent) trace
    | Nest more inner => Lays inner (indent + more) place trace next
    | Group inner _ => Lays inner indent place trace next
    | Flatten inner => Lays inner indent place trace next
    | OneLineBelow inner => place.midLine = True ∧ Lays inner (indent + 2) (AtStart (indent + 2)) trace next
    | Concat docs => LaysAll docs indent place trace next
    | Fill items => FillLays items indent place trace next
    | Choice options => OptionsLay options indent place trace next
    | LineSuffix comment => isLayout comment = False ∧ SuffixLays comment place trace next

def LaysAll (docs: List Doc) (indent: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop): Prop :=
  match docs with
    | [] => next place trace
    | [doc, ..rest] => Lays doc indent place trace (after later => LaysAll rest indent after later next)

def FillLays (items: List Doc) (indent: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop):
    Prop :=
  match items with
    | [] => next place trace
    | [first, ..others] => Lays first indent place trace (after later => SepsLay others indent after later next)

def SepsLay (items: List Doc) (indent: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop):
    Prop :=
  match items with
    | [] => next place trace
    | [item, ..more] => SepLays indent place trace (middle between =>
      Lays item indent middle between (after later => SepsLay more indent after later next))

def OptionsLay (options: List Doc) (indent: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop):
    Prop :=
  match options with
    | [] => next place trace
    | [last] => Lays last indent place trace next
    | [option, ..others] => Lays option indent place trace next ∧ OptionsLay others indent place trace next

--| The work list, from `place` to the end, where `spec` is asked of the
--| place and the whole trace.
def StackLays (spec: Place → List Event → Prop) (stack: List Cmd) (place: Place) (trace: List Event): Prop :=
  match stack with
    | [] => spec place trace
    | [Print indent _ doc, ..rest] => Lays doc indent place trace (after later => StackLays spec rest after later)
    | [FillSep indent item, ..rest] => SepLays indent place trace (middle between =>
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
            | Broken at, never => never
            | Mid at, lays => implies _ _ lays
            | Held at, lays => implies _ _ lays
        | False, Both oneLine lays =>
          match place, lays with
            | AtStart at, lays => (oneLine, (implies _ _ lays))
            | Broken at, lays => (oneLine, (implies _ _ lays))
            | Mid at, lays => (oneLine, (implies _ _ lays))
            | Held at, lays => (oneLine, (implies _ _ lays))

theorem sepLaysWeaker ∀ (indent: Nat) (place: Place) (trace: List Event) (strong weak: Place → List Event → Prop)
    (implies: ∀ (after: Place) (later: List Event) => strong after later → weak after later)
    (lays: SepLays indent place trace strong):
    SepLays indent place trace weak :=
  match place, lays with
    | AtStart at, never => never
    | Broken at, never => never
    | Mid at, Both same broken => ((implies _ _ same), (implies _ _ broken))
    | Held at, broken => implies _ _ broken

theorem softLaysWeaker ∀ (indent: Nat) (place: Place) (trace: List Event) (strong weak: Place → List Event → Prop)
    (implies: ∀ (after: Place) (later: List Event) => strong after later → weak after later)
    (lays: SoftLays indent place trace strong):
    SoftLays indent place trace weak :=
  match place, lays with
    | AtStart at, never => never
    | Broken at, never => never
    | Mid at, Both same broken => ((implies _ _ same), (implies _ _ broken))
    | Held at, broken => implies _ _ broken

theorem startLaysWeaker ∀ (indent: Nat) (place: Place) (trace: List Event) (strong weak: Place → List Event → Prop)
    (implies: ∀ (after: Place) (later: List Event) => strong after later → weak after later)
    (lays: StartLays indent place trace strong):
    StartLays indent place trace weak :=
  match place, lays with
    | AtStart at, lays => implies _ _ lays
    | Broken at, lays => implies _ _ lays
    | Mid at, lays => implies _ _ lays
    | Held at, lays => implies _ _ lays

theorem suffixLaysWeaker ∀ (comment: Text) (place: Place) (trace: List Event) (strong weak: Place → List Event → Prop)
    (implies: ∀ (after: Place) (later: List Event) => strong after later → weak after later)
    (lays: SuffixLays comment place trace strong):
    SuffixLays comment place trace weak :=
  match place, lays with
    | AtStart at, never => never
    | Broken at, never => never
    | Mid at, lays => implies _ _ lays
    | Held at, never => never

theorem blankLaysWeaker ∀ (place: Place) (trace: List Event) (strong weak: Place → List Event → Prop)
    (implies: ∀ (after: Place) (later: List Event) => strong after later → weak after later)
    (lays: BlankLays place trace strong):
    BlankLays place trace weak :=
  match place, lays with
    | AtStart at, never => never
    | Broken at, lays => implies _ _ lays
    | Mid at, lays => implies _ _ lays
    | Held at, lays => implies _ _ lays

--| What holds with a continuation holds with any it implies.
theorem laysWeaker ∀ (doc: Doc) (indent: Nat) (place: Place) (trace: List Event)
    (strong weak: Place → List Event → Prop)
    (implies: ∀ (after: Place) (later: List Event) => strong after later → weak after later)
    (lays: Lays doc indent place trace strong):
    Lays doc indent place trace weak :=
  match doc, lays with
    | Empty, lays => implies _ _ lays
    | BreakParent, lays => implies _ _ lays
    | Blank, lays => blankLaysWeaker place trace strong weak implies lays
    | Chunk text width, lays => writeLaysWeaker indent text place trace strong weak implies lays
    | Line, lays => sepLaysWeaker indent place trace strong weak implies lays
    | SoftLine, lays => softLaysWeaker indent place trace strong weak implies lays
    | HardLine, Both mid (Inl broken) => (mid, (Inl (implies _ _ broken)))
    | HardLine, Both mid (Inr started) => (mid, (Inr (implies _ _ started)))
    | CommentEnd, Both mid lays => (mid, (implies _ _ lays))
    | LineStart, lays => startLaysWeaker indent place trace strong weak implies lays
    | LineStartHere, lays => implies _ _ lays
    | Nest more inner, lays => laysWeaker inner (indent + more) place trace strong weak implies lays
    | Group inner hard, lays => laysWeaker inner indent place trace strong weak implies lays
    | Flatten inner, lays => laysWeaker inner indent place trace strong weak implies lays
    | OneLineBelow inner, Both mid lays =>
      (mid, (laysWeaker inner (indent + 2) (AtStart (indent + 2)) trace strong weak implies lays))
    | Concat docs, lays => allLaysWeaker docs indent place trace strong weak implies lays
    | Fill items, lays => fillLaysWeaker items indent place trace strong weak implies lays
    | Choice options, lays => optionsLayWeaker options indent place trace strong weak implies lays
    | LineSuffix comment, Both word lays => (word, (suffixLaysWeaker comment place trace strong weak implies lays))

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
    | [option, second, ..others], Both first rest => (
      (laysWeaker option indent place trace strong weak implies first),
      (optionsLayWeaker [second, ..others] indent place trace strong weak implies rest)
    )

-- What a step pushes on the work list lays as the document it came from.

theorem printsLay ∀ (spec: Place → List Event → Prop) (indent: Nat) (mode: Mode) (docs: List Doc) (rest: List Cmd)
    (place: Place) (trace: List Event)
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

theorem linesLay ∀ (first: Doc) (others: List Doc) (indent: Nat) (place: Place)
    (trace: List Event) (next: Place → List Event → Prop)
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

theorem optionLays ∀ (chosen: Doc) (options: List Doc) (indent: Nat) (place: Place)
    (trace: List Event) (next: Place → List Event → Prop)
    (isOption: IsOption chosen options)
    (lays: OptionsLay options indent place trace next):
    Lays chosen indent place trace next :=
  match options, isOption, lays with
    | [], picked, lays => rewrite picked in lays
    | [last], picked, lays => rewrite picked in lays
    | [option, second, ..others], Inl picked, Both first _ => rewrite picked in first
    | [option, second, ..others], Inr later, Both _ rest =>
      optionLays chosen [second, ..others] indent place trace next later rest

theorem headOrLays ∀ (options: List Doc) (indent: Nat) (place: Place)
    (trace: List Event) (next: Place → List Event → Prop)
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

--| Spaces are no event.
theorem eventsGap ∀ (piece: Text) (earlier: List Text)
    (gap: piece.all (char => char == ' ') = True):
    eventsOf [piece, ..earlier] = eventsOf earlier :=
  rewrite gapLayout piece gap, gapNoBreak piece gap in rfl

--| The line break that ends a line of words is no event.
theorem eventsBreak ∀ (earlier: List Text)
    (words: lineBlank earlier = False):
    eventsOf ["\n", ..earlier] = eventsOf earlier :=
  rewrite words in rfl

--| A line break on a line with nothing but spaces is a blank line.
theorem eventsBlank ∀ (earlier: List Text)
    (blank: lineBlank earlier = True):
    eventsOf ["\n", ..earlier] = eventsOf earlier ++ [Event.blankLine] :=
  rewrite blank in rfl

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
    | True, gap => rewrite trimDrop last earlier gap in Eq.trans rest (Eq.sym (eventsGap last earlier gap))
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
--| the trace, after the words written. `newlines` is the printer's count
--| of the line breaks its output ends with, which `Blank` reads: none
--| after words, one at `Broken`.
def AgreesParts (out: List Text) (owed: Option Nat) (atLineStart: Bool) (suffixes: List Text) (lineIndent: Nat)
    (started: Bool) (newlines: Nat) (place: Place) (trace: List Event):
    Prop :=
  match place with
    | AtStart at =>
      atLineStart = True
        ∧ suffixes = []
        ∧ lineBlank out = True
        ∧ lineWidth out = 0
        ∧ owed.getOrElse 0 = at
        ∧ lineIndent = at
        ∧ trace = eventsOf out
    | Broken at =>
      atLineStart = True
        ∧ suffixes = []
        ∧ lineBlank out = True
        ∧ lineWidth out = 0
        ∧ owed.getOrElse 0 = at
        ∧ lineIndent = at
        ∧ trace = eventsOf out
        ∧ started = True
        ∧ newlines = 1
    | Mid at =>
      atLineStart = False
        ∧ suffixes = []
        ∧ lineBlank out = False
        ∧ owed = None
        ∧ lineIndent = at
        ∧ trace = eventsOf out
        ∧ newlines = 0
    | Held at =>
      atLineStart = False
        ∧ (∃ (comment: Text) => suffixes = [comment]
          ∧ isLayout comment = False
          ∧ trace = eventsOf out ++ [{ word = comment, start = None }])
        ∧ lineBlank out = False
        ∧ owed = None
        ∧ lineIndent = at

def Agrees (printer: Printer) (place: Place) (trace: List Event): Prop :=
  AgreesParts printer.out printer.owed printer.atLineStart printer.suffixes printer.lineIndent printer.started
      printer.newlinesAtEnd place trace

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
    | { width = total, out, column, owed, atLineStart, suffixes, lineIndent, newlinesAtEnd, started }, (start, none,
        blank, empty, owes, indent, same) =>
      match owed, owes with
        | None, owes => (
          rfl,
          none,
          (blankWord text out word),
          rfl,
          indent,
          (rewrite <- owes, eventsWord text out word, blank, empty, same in rfl),
          rfl
        )
        | Some Zero, owes => (
          rfl,
          none,
          (blankWord text out word),
          rfl,
          indent,
          (rewrite <- owes, eventsWord text out word, blank, empty, same in rfl),
          rfl
        )
        | Some (Succ less), owes =>
          let stillBlank: lineBlank [" ".repeat (Succ less), ..out] = True :=
            Eq.trans (blankGap (" ".repeat (Succ less)) out (indentSpaces (Succ less))) blank
          let sum := widthPiece (" ".repeat (Succ less)) out (gapNoBreak _ (indentSpaces (Succ less)))
          let length := indentLength (Succ less)
          let wide: lineWidth [" ".repeat (Succ less), ..out] = Succ less := omega
          (
            rfl,
            none,
            (blankWord text [" ".repeat (Succ less), ..out] word),
            rfl,
            indent,
            (rewrite <- owes,
                eventsWord text [" ".repeat (Succ less), ..out] word,
                eventsGap (" ".repeat (Succ less)) out (indentSpaces (Succ less)),
                stillBlank,
                wide,
                same in
              rfl),
            rfl
          )

--| A word put after words on its line doesn't start the line.
theorem putMid ∀ (printer: Printer) (text: Text) (width at: Nat) (trace: List Event)
    (agrees: Agrees printer (Mid at) trace)
    (word: isLayout text = False):
    Agrees (printer.put text width) (Mid at) (trace ++ [{ word = text, start = None }]) :=
  match printer, agrees with
    | { width = total, out, column, owed, atLineStart, suffixes, lineIndent, newlinesAtEnd, started }, (start, none,
        blank, owes, indent, same, _) =>
      match owed, owes with
        | Some value, never => Void.exfalso (someNotNone value never)
        | None, _ => (
          rfl,
          none,
          (blankWord text out word),
          rfl,
          indent,
          (rewrite eventsWord text out word, blank, same in rfl),
          rfl
        )

--| Spaces put after words change nothing but the width.
theorem putSpaces ∀ (printer: Printer) (text: Text) (width at: Nat) (trace: List Event)
    (agrees: Agrees printer (Mid at) trace)
    (gap: text.all (char => char == ' ') = True):
    Agrees (printer.put text width) (Mid at) trace :=
  match printer, agrees with
    | { width = total, out, column, owed, atLineStart, suffixes, lineIndent, newlinesAtEnd, started }, (start, none,
        blank, owes, indent, same, _) =>
      match owed, owes with
        | Some value, never => Void.exfalso (someNotNone value never)
        | None, _ => (
          rfl,
          none,
          (Eq.trans (blankGap text out gap) blank),
          rfl,
          indent,
          (Eq.trans same (Eq.sym (eventsGap text out gap))),
          rfl
        )

--| After the line break that ends a line of words the printer is at the
--| start of a line indented as asked, with one line break behind it, and
--| a comment that waited is written where the trace has it.
theorem newlineBroken ∀ (printer: Printer) (indent: Nat) (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace)
    (mid: place.midLine = True):
    Agrees (printer.newline indent) (Broken indent) trace :=
  match printer, place, agrees, mid with
    | { width = total, out, column, owed, atLineStart, suffixes, lineIndent, newlinesAtEnd, started }, Mid
          at, Both start (Both none (Both blank (Both owes (Both same (Both events zero))))), _ =>
      match suffixes, none with
        | [first, ..more], never => Void.exfalso (consNotNil first more never)
        | [], _ =>
          let words: lineBlank (trimSpaces out) = False := Eq.trans (trimBlank out) blank
          (
            rfl,
            rfl,
            rfl,
            rfl,
            rfl,
            rfl,
            (Eq.trans events (Eq.sym (Eq.trans (eventsBreak (trimSpaces out) words) (trimEvents out)))),
            rfl,
            (Eq.cong ((count: Nat) => count + 1) zero)
          )
    | { width = total, out, column, owed, atLineStart, suffixes, lineIndent, newlinesAtEnd, started }, Held
          at, Both start (Both (Witness comment (Both one (Both word events))) (Both blank (Both owes same))), _ =>
      let written: eventsOf [comment, " ", ..trimSpaces out] = eventsOf out ++ [{ word = comment, start = None }] :=
        rewrite eventsWord comment [" ", ..trimSpaces out] word, trimBlank out, blank, trimEvents out in rfl
      let ended: eventsOf ["\n", comment, " ", ..trimSpaces out] = eventsOf [comment, " ", ..trimSpaces out] :=
        eventsBreak [comment, " ", ..trimSpaces out] (blankWord comment [" ", ..trimSpaces out] word)
      rewrite one, start in
        (rfl, rfl, rfl, rfl, rfl, rfl, (Eq.trans events (Eq.sym (Eq.trans ended written))), rfl, rfl)

--| A place that allows a `Blank` is a line start.
theorem brokenStart ∀ (printer: Printer) (at: Nat) (trace: List Event)
    (agrees: Agrees printer (Broken at) trace):
    Agrees printer (AtStart at) trace :=
  match agrees with
    | (start, none, blank, empty, owes, indent, events, _) => (start, none, blank, empty, owes, indent, events)

theorem newlineAgrees ∀ (printer: Printer) (indent: Nat) (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace)
    (mid: place.midLine = True):
    Agrees (printer.newline indent) (AtStart indent) trace :=
  brokenStart (printer.newline indent) indent trace (newlineBroken printer indent place trace agrees mid)

theorem agreesIndent ∀ (printer: Printer) (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace):
    printer.lineIndent = place.indent :=
  match place, agrees with
    | AtStart at, Both _ (Both _ (Both _ (Both _ (Both _ (Both indent _))))) => indent
    | Broken at, Both _ (Both _ (Both _ (Both _ (Both _ (Both indent _))))) => indent
    | Mid at, Both _ (Both _ (Both _ (Both _ (Both indent _)))) => indent
    | Held at, Both _ (Both _ (Both _ (Both _ indent))) => indent

--| No comment waits at a line start or after plain words; one does at
--| `Held`.
theorem agreesClear ∀ (printer: Printer) (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace):
    printer.suffixes.isEmpty
      = (match place with
        | AtStart _ => True
        | Broken _ => True
        | Mid _ => True
        | Held _ => False) :=
  match place, agrees with
    | AtStart at, Both _ (Both none _) => rewrite none in rfl
    | Broken at, Both _ (Both none _) => rewrite none in rfl
    | Mid at, Both _ (Both none _) => rewrite none in rfl
    | Held at, Both _ (Both (Witness comment (Both one _)) _) => rewrite one in rfl

theorem agreesStart ∀ (printer: Printer) (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace):
    printer.atLineStart
      = (match place with
        | AtStart _ => True
        | Broken _ => True
        | Mid _ => False
        | Held _ => False) :=
  match place, agrees with
    | AtStart at, Both start _ => start
    | Broken at, Both start _ => start
    | Mid at, Both start _ => start
    | Held at, Both start _ => start

theorem wordNotLayout ∀ (text: Text)
    (word: text.all (char => char == ' ') = False)
    (oneLine: (text == "\n") = False):
    isLayout text = False :=
  match gap: text.all (char => char == ' '), word with
    | False, _ => oneLine
    | True, never => Void.exfalso (Bool.falseNotTrue (Eq.sym never))

theorem newlineStays ∀ (next: Place → List Event → Prop) (printer: Printer) (indent: Nat)
    (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace)
    (mid: place.midLine = True) (after: next (AtStart indent) trace):
    Stays next (printer.newline indent) :=
  ((AtStart indent), trace, (newlineAgrees printer indent place trace agrees mid), after)

--| A comment break: a line break to deeper than the line it breaks.
theorem breakStays ∀ (next: Place → List Event → Prop) (printer: Printer) (indent: Nat)
    (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace)
    (mid: place.midLine = True) (after: next (AtStart (Nat.max indent (place.indent + 2))) trace):
    Stays next (printer.newline (printer.continuation indent)) :=
  let deeper: next (AtStart (Nat.max indent (printer.lineIndent + 2))) trace :=
    rewrite agreesIndent printer place trace agrees in after
  newlineStays next printer (printer.continuation indent) place trace agrees mid deeper

theorem writeStart ∀ (next: Place → List Event → Prop) (printer: Printer) (indent: Nat) (text: Text)
    (width at: Nat) (trace: List Event)
    (agrees: Agrees printer (AtStart at) trace)
    (clear: printer.suffixes.isEmpty = True)
    (lays: WriteLays indent text (AtStart at) trace next):
    Stays next (printer.write indent text width) :=
  match empty: text.isEmpty, lays with
    | True, lays => ((AtStart at), trace, agrees, lays)
    | False, lays =>
      match spaces: text.all (char => char == ' '), lays with
        | True, never => Void.exfalso (Bool.falseNotTrue never)
        | False, Both oneLine lays =>
          match waiting: printer.suffixes.isEmpty, clear with
            | True, _ =>
              ((Mid at), _, (putStart printer text width at trace agrees (wordNotLayout text spaces oneLine)), lays)

theorem writeMid ∀ (next: Place → List Event → Prop) (printer: Printer) (indent: Nat) (text: Text)
    (width at: Nat) (trace: List Event)
    (agrees: Agrees printer (Mid at) trace)
    (clear: printer.suffixes.isEmpty = True)
    (lays: WriteLays indent text (Mid at) trace next):
    Stays next (printer.write indent text width) :=
  match empty: text.isEmpty, lays with
    | True, lays => ((Mid at), trace, agrees, lays)
    | False, lays =>
      match spaces: text.all (char => char == ' '), lays with
        | True, lays =>
          match waiting: printer.suffixes.isEmpty, clear with
            | True, _ => ((Mid at), trace, (putSpaces printer text width at trace agrees spaces), lays)
        | False, Both oneLine lays =>
          match waiting: printer.suffixes.isEmpty, clear with
            | True, _ =>
              ((Mid at), _, (putMid printer text width at trace agrees (wordNotLayout text spaces oneLine)), lays)

theorem writeHeld ∀ (next: Place → List Event → Prop) (printer: Printer) (indent: Nat) (text: Text)
    (width at: Nat) (trace: List Event)
    (agrees: Agrees printer (Held at) trace)
    (waits: printer.suffixes.isEmpty = False)
    (lays: WriteLays indent text (Held at) trace next):
    Stays next (printer.write indent text width) :=
  match empty: text.isEmpty, lays with
    | True, lays => ((Held at), trace, agrees, lays)
    | False, lays =>
      match spaces: text.all (char => char == ' '), lays with
        | True, lays =>
          match waiting: printer.suffixes.isEmpty, waits with
            | False, _ => ((Held at), trace, agrees, lays)
        | False, Both oneLine lays =>
          let deeper: next
            (Mid (Nat.max indent (printer.lineIndent + 2)))
            (trace ++ [{ word = text, start = Some (Nat.max indent (printer.lineIndent + 2)) }]) :=
            rewrite agreesIndent printer (Held at) trace agrees in lays
          match waiting: printer.suffixes.isEmpty, waits with
            | False, _ => (
              (Mid (printer.continuation indent)),
              _,
              (putStart
                (printer.newline (printer.continuation indent))
                text
                width
                (printer.continuation indent)
                trace
                (newlineAgrees printer (printer.continuation indent) (Held at) trace agrees rfl)
                (wordNotLayout text spaces oneLine)),
              deeper
            )

theorem writeBroken ∀ (next: Place → List Event → Prop) (printer: Printer) (indent: Nat) (text: Text)
    (width at: Nat) (trace: List Event)
    (agrees: Agrees printer (Broken at) trace)
    (clear: printer.suffixes.isEmpty = True)
    (lays: WriteLays indent text (Broken at) trace next):
    Stays next (printer.write indent text width) :=
  match empty: text.isEmpty, lays with
    | True, lays => ((Broken at), trace, agrees, lays)
    | False, lays =>
      match spaces: text.all (char => char == ' '), lays with
        | True, never => Void.exfalso (Bool.falseNotTrue never)
        | False, Both oneLine lays =>
          match waiting: printer.suffixes.isEmpty, clear with
            | True, _ => (
              (Mid at),
              _,
              (putStart printer text width at trace
                (brokenStart printer at trace agrees)
                (wordNotLayout text spaces oneLine)),
              lays
            )

--| A chunk written where the document said.
theorem writeStays ∀ (next: Place → List Event → Prop) (printer: Printer) (indent: Nat) (text: Text) (width: Nat)
    (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace)
    (lays: WriteLays indent text place trace next):
    Stays next (printer.write indent text width) :=
  match place, agrees, lays with
    | AtStart at, agrees, lays =>
      writeStart next printer indent text width at trace agrees (agreesClear printer (AtStart at) trace agrees) lays
    | Broken at, agrees, lays =>
      writeBroken next printer indent text width at trace agrees (agreesClear printer (Broken at) trace agrees) lays
    | Mid at, agrees, lays =>
      writeMid next printer indent text width at trace agrees (agreesClear printer (Mid at) trace agrees) lays
    | Held at, agrees, lays =>
      writeHeld next printer indent text width at trace agrees (agreesClear printer (Held at) trace agrees) lays

theorem sepBroken ∀ (next: Place → List Event → Prop) (indent: Nat) (place: Place) (trace: List Event)
    (lays: SepLays indent place trace next):
    next (AtStart indent) trace :=
  match place, lays with
    | AtStart at, never => Void.exfalso (Bool.falseNotTrue never)
    | Broken at, never => Void.exfalso (Bool.falseNotTrue never)
    | Mid at, Both _ broken => broken
    | Held at, broken => broken

theorem sepMid ∀ (next: Place → List Event → Prop) (indent: Nat) (place: Place) (trace: List Event)
    (lays: SepLays indent place trace next):
    place.midLine = True :=
  match place, lays with
    | AtStart at, never => never
    | Broken at, never => never
    | Mid at, _ => rfl
    | Held at, _ => rfl

theorem softMid ∀ (next: Place → List Event → Prop) (indent: Nat) (place: Place) (trace: List Event)
    (lays: SoftLays indent place trace next):
    place.midLine = True :=
  match place, lays with
    | AtStart at, never => never
    | Broken at, never => never
    | Mid at, _ => rfl
    | Held at, _ => rfl

--| With nothing at the start of its line the printer is after words.
theorem startMid ∀ (printer: Printer) (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace)
    (start: printer.atLineStart = False):
    place.midLine = True :=
  match place, agrees with
    | AtStart at, Both other _ => Eq.trans (Eq.sym start) other
    | Broken at, Both other _ => Eq.trans (Eq.sym start) other
    | Mid at, _ => rfl
    | Held at, _ => rfl

--| A separator written as a space, with no comment waiting.
theorem sepSpace ∀ (next: Place → List Event → Prop) (printer: Printer) (indent: Nat) (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace)
    (clear: printer.suffixes.isEmpty = True)
    (lays: SepLays indent place trace next):
    Stays next (printer.write indent " " 1) :=
  match place, agrees, lays with
    | AtStart at, _, never => Void.exfalso (Bool.falseNotTrue never)
    | Broken at, _, never => Void.exfalso (Bool.falseNotTrue never)
    | Mid at, agrees, Both same _ =>
      match waiting: printer.suffixes.isEmpty, clear with
        | True, _ => ((Mid at), trace, (putSpaces printer " " 1 at trace agrees rfl), same)
    | Held at, agrees, _ =>
      Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym (agreesClear printer (Held at) trace agrees)) clear))

theorem softBroken ∀ (next: Place → List Event → Prop) (indent: Nat) (place: Place) (trace: List Event)
    (lays: SoftLays indent place trace next):
    next (AtStart indent) trace :=
  match place, lays with
    | AtStart at, never => Void.exfalso (Bool.falseNotTrue never)
    | Broken at, never => Void.exfalso (Bool.falseNotTrue never)
    | Mid at, Both _ broken => broken
    | Held at, broken => broken

theorem softSame ∀ (next: Place → List Event → Prop) (printer: Printer) (indent: Nat) (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace)
    (clear: printer.suffixes.isEmpty = True)
    (lays: SoftLays indent place trace next):
    next place trace :=
  match place, agrees, lays with
    | AtStart at, _, never => Void.exfalso (Bool.falseNotTrue never)
    | Broken at, _, never => Void.exfalso (Bool.falseNotTrue never)
    | Mid at, _, Both same _ => same
    | Held at, agrees, _ =>
      Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym (agreesClear printer (Held at) trace agrees)) clear))

theorem lineStartSame ∀ (printer: Printer) (indent: Nat)
    (start: printer.atLineStart = True):
    printer.lineStart indent = printer :=
  match at: printer.atLineStart, start with | True, _ => rfl

theorem lineStartBreaks ∀ (printer: Printer) (indent: Nat)
    (start: printer.atLineStart = False):
    printer.lineStart indent = printer.newline (printer.continuation indent) :=
  match at: printer.atLineStart, start with | False, _ => rfl

theorem lineStartStays ∀ (next: Place → List Event → Prop) (printer: Printer) (indent: Nat)
    (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace)
    (lays: StartLays indent place trace next):
    Stays next (printer.lineStart indent) :=
  match place, agrees, lays with
    | AtStart at, agrees, lays =>
      rewrite lineStartSame printer indent (agreesStart printer (AtStart at) trace agrees) in
        ((AtStart at), trace, agrees, lays)
    | Broken at, agrees, lays =>
      rewrite lineStartSame printer indent (agreesStart printer (Broken at) trace agrees) in
        ((AtStart at), trace, (brokenStart printer at trace agrees), lays)
    | Mid at, agrees, lays =>
      rewrite lineStartBreaks printer indent (agreesStart printer (Mid at) trace agrees) in
        breakStays next printer indent (Mid at) trace agrees rfl lays
    | Held at, agrees, lays =>
      rewrite lineStartBreaks printer indent (agreesStart printer (Held at) trace agrees) in
        breakStays next printer indent (Held at) trace agrees rfl lays

--| Indentation set at the start of a line.
theorem hereAgrees ∀ (printer: Printer) (indent: Nat) (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace)
    (start: printer.atLineStart = True):
    Agrees { printer | owed = Some indent, lineIndent = indent } (AtStart indent) trace :=
  match place, agrees with
    | AtStart at, Both _ (Both none (Both blank (Both empty (Both _ (Both _ events))))) =>
      (start, none, blank, empty, rfl, rfl, events)
    | Broken at, Both _ (Both none (Both blank (Both empty (Both _ (Both _ (Both events _)))))) =>
      (start, none, blank, empty, rfl, rfl, events)
    | Mid at, Both other _ => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym other) start))
    | Held at, Both other _ => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym other) start))

theorem blankSame ∀ (printer: Printer) (start: printer.atLineStart = False): printer.blank = printer :=
  match at: printer.atLineStart, start with | False, _ => rfl

--| One line break behind it and something printed, the printer adds the
--| line break that leaves a blank line.
theorem blankAdds ∀ (printer: Printer)
    (start: printer.atLineStart = True)
    (started: printer.started = True)
    (one: printer.newlinesAtEnd = 1):
    printer.blank = { printer | out = ["\n", ..printer.out], newlinesAtEnd = printer.newlinesAtEnd + 1 } :=
  match at: printer.atLineStart, begun: printer.started, start, started with | True, True, _, _ => rewrite one in rfl

--| A `Blank` leaves a blank line right after a line of words, and
--| nothing after words.
theorem blankStays ∀ (next: Place → List Event → Prop) (printer: Printer) (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace)
    (lays: BlankLays place trace next):
    Stays next printer.blank :=
  match place, agrees, lays with
    | AtStart at, _, never => Void.exfalso (Bool.falseNotTrue never)
    | Broken at, Both start
        (Both none (Both blank (Both empty (Both owes (Both indent (Both events (Both started one))))))), lays =>
      rewrite blankAdds printer start started one in
        (
          (AtStart at),
          (trace ++ [Event.blankLine]),
          ((
            start,
            none,
            rfl,
            rfl,
            owes,
            indent,
            (Eq.trans
              (Eq.cong ((before: List Event) => before ++ [Event.blankLine]) events)
              (Eq.sym (eventsBlank printer.out blank)))
          )),
          lays
        )
    | Mid at, agrees, lays =>
      rewrite blankSame printer (agreesStart printer (Mid at) trace agrees) in ((Mid at), trace, agrees, lays)
    | Held at, agrees, lays =>
      rewrite blankSame printer (agreesStart printer (Held at) trace agrees) in ((Held at), trace, agrees, lays)

--| A trailing comment starts waiting, already in the trace.
theorem suffixStays ∀ (next: Place → List Event → Prop) (printer: Printer) (comment: Text)
    (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace)
    (word: isLayout comment = False)
    (lays: SuffixLays comment place trace next):
    Stays next { printer | suffixes = printer.suffixes ++ [comment] } :=
  match place, agrees, lays with
    | AtStart at, _, never => Void.exfalso (Bool.falseNotTrue never)
    | Broken at, _, never => Void.exfalso (Bool.falseNotTrue never)
    | Held at, _, never => Void.exfalso (Bool.falseNotTrue never)
    | Mid at, Both start (Both none (Both blank (Both owes (Both indent (Both events _))))), lays =>
      let one: printer.suffixes ++ [comment] = [comment] := rewrite none in rfl
      (
        (Held at),
        _,
        ((
          start,
          ((
            comment,
            one,
            word,
            (Eq.cong ((before: List Event) => before ++ [{ word = comment, start = None }]) events)
          )),
          blank,
          owes,
          indent
        )),
        lays
      )

theorem eitherStays ∀ (spec: Place → List Event → Prop) (flat clear: Bool) (yes no: Printer) (rest: List Cmd)
    (whenYes: clear = True → Stays (place trace => StackLays spec rest place trace) yes)
    (whenNo: Stays (place trace => StackLays spec rest place trace) no):
    Stays
      (place trace => StackLays spec (if flat && clear then (yes, rest) else (no, rest)).snd place trace)
      (if flat && clear then (yes, rest) else (no, rest)).fst :=
  match flat, clear, whenYes with
    | True, True, whenYes => whenYes rfl
    | True, False, _ => whenNo
    | False, True, _ => whenNo
    | False, False, _ => whenNo

--| A step of a reading keeps the printer where the work list said, and
--| the work list it leaves lays from there.
theorem stepLays ∀ (spec: Place → List Event → Prop) (printer: Printer) (cmd: Cmd) (rest: List Cmd)
    (result: (Printer, List Cmd)) (place: Place) (trace: List Event)
    (steps: StepsTo printer cmd rest result)
    (agrees: Agrees printer place trace)
    (lays: StackLays spec [cmd, ..rest] place trace):
    Stays (after later => StackLays spec result.snd after later) result.fst :=
  match cmd, steps, lays with
    | FillSep indent item, Inl (Both clear flat), lays =>
      rewrite flat in
        sepSpace
          (middle between => Lays item indent middle between (after later => StackLays spec rest after later))
          printer
          indent
          place
          trace
          agrees
          clear
          lays
    | FillSep indent item, Inr broken, lays =>
      rewrite broken in
        newlineStays
          (middle between => Lays item indent middle between (after later => StackLays spec rest after later))
          printer
          indent
          place
          trace
          agrees
          (sepMid
            (middle between => Lays item indent middle between (after later => StackLays spec rest after later))
            indent
            place
            trace
            lays)
          (sepBroken
            (middle between => Lays item indent middle between (after later => StackLays spec rest after later))
            indent
            place
            trace
            lays)
    | Print indent mode doc, steps, lays =>
      match doc, steps, lays with
        | Empty, steps, lays => rewrite steps in (place, trace, agrees, lays)
        | BreakParent, steps, lays => rewrite steps in (place, trace, agrees, lays)
        | Chunk text width, steps, lays =>
          rewrite steps in
            writeStays
              (after later => StackLays spec rest after later)
              printer
              indent
              text
              width
              place
              trace
              agrees
              lays
        | Line, steps, lays =>
          rewrite steps in
            eitherStays spec mode.isFlat printer.suffixes.isEmpty
              (printer.write indent " " 1)
              (printer.newline indent)
              rest
              (clear =>
                sepSpace (after later => StackLays spec rest after later) printer indent place trace agrees clear lays)
              (newlineStays
                (after later => StackLays spec rest after later)
                printer
                indent
                place
                trace
                agrees
                (sepMid (after later => StackLays spec rest after later) indent place trace lays)
                (sepBroken (after later => StackLays spec rest after later) indent place trace lays))
        | SoftLine, steps, lays =>
          rewrite steps in
            eitherStays spec mode.isFlat printer.suffixes.isEmpty printer
              (printer.newline indent)
              rest
              (clear =>
                (
                  place,
                  trace,
                  agrees,
                  (softSame
                    (after later => StackLays spec rest after later)
                    printer
                    indent
                    place
                    trace
                    agrees
                    clear
                    lays)
                ))
              (newlineStays
                (after later => StackLays spec rest after later)
                printer
                indent
                place
                trace
                agrees
                (softMid (after later => StackLays spec rest after later) indent place trace lays)
                (softBroken (after later => StackLays spec rest after later) indent place trace lays))
        | HardLine, steps, Both mid (Inl broken) =>
          rewrite steps in ((Broken indent), trace, (newlineBroken printer indent place trace agrees mid), broken)
        | HardLine, steps, Both mid (Inr started) =>
          rewrite steps in
            newlineStays (after later => StackLays spec rest after later) printer indent place trace agrees mid started
        | CommentEnd, steps, Both mid lays =>
          let same: StackLays spec rest (AtStart printer.lineIndent) trace :=
            rewrite agreesIndent printer place trace agrees in lays
          rewrite steps in
            newlineStays
              (after later => StackLays spec rest after later)
              printer
              printer.lineIndent
              place
              trace
              agrees
              mid
              same
        | LineStart, steps, lays =>
          rewrite steps in
            lineStartStays (after later => StackLays spec rest after later) printer indent place trace agrees lays
        | LineStartHere, steps, lays =>
          match start: printer.atLineStart with
            | True =>
              rewrite steps in ((AtStart indent), trace, (hereAgrees printer indent place trace agrees start), lays)
            | False =>
              rewrite steps in
                newlineStays
                  (after later => StackLays spec rest after later)
                  printer
                  indent
                  place
                  trace
                  agrees
                  (startMid printer place trace agrees start)
                  lays
        | Blank, steps, lays =>
          rewrite steps in blankStays (after later => StackLays spec rest after later) printer place trace agrees lays
        | Nest more inner, steps, lays => rewrite steps in (place, trace, agrees, lays)
        | OneLineBelow inner, steps, Both mid lays => rewrite steps in (place, trace, agrees, mid, (Inr lays))
        | Flatten inner, steps, lays => rewrite steps in (place, trace, agrees, lays)
        | LineSuffix comment, steps, Both word lays =>
          rewrite steps in
            suffixStays (after later => StackLays spec rest after later) printer comment place trace agrees word lays
        | Group inner hard, Inl (Both _ flat), lays => rewrite flat in (place, trace, agrees, lays)
        | Group inner hard, Inr (Both _ broken), lays => rewrite broken in (place, trace, agrees, lays)
        | Concat docs, steps, lays =>
          rewrite steps in (place, trace, agrees, (printsLay spec indent mode docs rest place trace lays))
        | Fill [], steps, lays => rewrite steps in (place, trace, agrees, lays)
        | Fill [first, ..others], Inl (Both _ flat), lays =>
          rewrite flat in
            (
              place,
              trace,
              agrees,
              (printsLay spec indent Flat
                (Doc.joinLines [first, ..others])
                rest
                place
                trace
                (linesLay first others indent place trace (after later => StackLays spec rest after later) lays))
            )
        | Fill [first, ..others], Inr (Both _ (Witness firstMode broken)), lays =>
          rewrite broken in
            (
              place,
              trace,
              agrees,
              (laysWeaker first indent place trace
                (after later => SepsLay others indent after later (final last => StackLays spec rest final last))
                (after later => StackLays spec (others.map (FillSep indent) ++ rest) after later)
                (after later seps => fillSepsLay spec indent others rest after later seps)
                lays)
            )
        | Choice options, Inl (Both _ flat), lays =>
          rewrite flat in
            (
              place,
              trace,
              agrees,
              (headOrLays options indent place trace (after later => StackLays spec rest after later) lays)
            )
        | Choice options, Inr (Both _ (Witness chosen (Both isOption broken))), lays =>
          rewrite broken in
            (
              place,
              trace,
              agrees,
              (optionLays chosen options indent place trace
                (after later => StackLays spec rest after later)
                isOption
                lays)
            )

--| A reading that has the steps to finish its work list ends where the
--| work list's last document leaves it, at a place and trace `spec`
--| holds of.
theorem readingLays ∀ (spec: Place → List Event → Prop) (printer: Printer) (fuel: Nat) (stack: List Cmd)
    (final: Printer) (place: Place) (trace: List Event)
    (reads: Reads printer fuel stack final)
    (agrees: Agrees printer place trace)
    (lays: StackLays spec stack place trace)
    (enough: stackCost stack ≤ fuel):
    Stays spec final :=
  match fuel, stack, reads, lays with
    | Zero, [], reads, lays => (place, trace, (rewrite reads in agrees), lays)
    | Succ more, [], reads, lays => (place, trace, (rewrite reads in agrees), lays)
    | Zero, [cmd, ..rest], _, _ =>
      let positive := costPositive cmd
      Void.exfalso (omega)
    | Succ more, [cmd, ..rest], Witness next (Witness later (Both steps laterReads)), lays =>
      let lighter := readingLighter printer cmd rest (next, later) steps
      match stepLays spec printer cmd rest (next, later) place trace steps agrees lays with
        | Witness after (Witness written (Both nextAgrees nextLays)) =>
          readingLays spec next more later final after written laterReads nextAgrees nextLays (omega)

--| Writing the comment that still waits at the end adds no word the
--| trace doesn't have.
theorem flushAgrees ∀ (printer: Printer) (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace):
    trace = eventsOf printer.flushSuffixes.out :=
  match printer, place, agrees with
    | { width = total, out, column, owed, atLineStart, suffixes, lineIndent, newlinesAtEnd, started }, AtStart
          at, Both _ (Both none (Both _ (Both _ (Both _ (Both _ events))))) => rewrite none in events
    | { width = total, out, column, owed, atLineStart, suffixes, lineIndent, newlinesAtEnd, started }, Broken at, Both _
        (Both none (Both _ (Both _ (Both _ (Both _ (Both events _)))))) => rewrite none in events
    | { width = total, out, column, owed, atLineStart, suffixes, lineIndent, newlinesAtEnd, started }, Mid at, Both _
        (Both none (Both _ (Both _ (Both _ (Both events _))))) => rewrite none in events
    | { width = total, out, column, owed, atLineStart, suffixes, lineIndent, newlinesAtEnd, started }, Held
          at, Both start (Both (Witness comment (Both one (Both word events))) (Both blank _)) =>
      let written: eventsOf [comment, " ", ..out] = eventsOf out ++ [{ word = comment, start = None }] :=
        rewrite eventsWord comment [" ", ..out] word, blank in rfl
      rewrite one, start in Eq.trans events (Eq.sym written)

--| The pieces `print` joins, in the order printed.
def printedPieces (doc: Doc) (width: Nat): List Text :=
  ((Printer.start width).run (3 * doc.size + 3) (3 * doc.size + 3) [Print 0 Break doc] |> .flushSuffixes).out.reverse

theorem printIsPieces ∀ (doc: Doc) (width: Nat): print doc width = (printedPieces doc width).joinWith "" := rfl

--| A document that lays from the start of an unindented line, printed at
--| any width, puts each word where the document said: `spec` holds of the
--| words of the printed pieces in order, each with the column it starts
--| its line at, if it does.
theorem printLays ∀ (spec: Place → List Event → Prop) (doc: Doc) (width: Nat)
    (lays: Lays doc 0 (AtStart 0) [] spec):
    ∃ (place: Place) => spec place (eventsOf (printedPieces doc width).reverse) :=
  let fuel := 3 * doc.size + 3
  let ran := (Printer.start width).run fuel fuel [Print 0 Break doc]
  let bound := stepsUnderSize doc
  let start: Agrees (Printer.start width) (AtStart 0) [] := (rfl, rfl, rfl, rfl, rfl, rfl, rfl)
  match readingLays spec
    (Printer.start width)
    fuel
    [Print 0 Break doc]
    ran
    (AtStart 0)
    []
    (runIsReading (Printer.start width) fuel fuel [Print 0 Break doc])
    start
    lays
    (omega) with
    | (place, trace, agrees, holds) =>
      (place, (rewrite List.reverseReverse ran.flushSuffixes.out, <- flushAgrees ran place trace agrees in holds))

--| `Lays` computes, and can be met: `f`, then `x` on a line of its own
--| two columns in, at every width.
theorem printLaysExample ∀ (width: Nat):
    ∃ (place: Place) => eventsOf
      (printedPieces (Concat [Chunk "f" 1, Nest 2 (Concat [HardLine, Chunk "x" 1])]) width).reverse
      = [{ word = "f", start = Some 0 }, { word = "x", start = Some 2 }] :=
  printLays
    (place trace => trace = [{ word = "f", start = Some 0 }, { word = "x", start = Some 2 }])
    (Concat [Chunk "f" 1, Nest 2 (Concat [HardLine, Chunk "x" 1])])
    width
    ((rfl, rfl, (Inr ((rfl, rfl)))))

--| `putMid`'s and `putSpaces`' hypothesis can be met: after `f` at the
--| start, the printer is in the middle of an unindented line.
theorem midExample: Agrees ((Printer.start 80).put "f" 1) (Mid 0) [{ word = "f", start = Some 0 }] :=
  putStart (Printer.start 80) "f" 1 0 [] ((rfl, rfl, rfl, rfl, rfl, rfl, rfl)) rfl
