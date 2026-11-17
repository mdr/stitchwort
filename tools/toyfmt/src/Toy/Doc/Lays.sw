--| Where a document lays each word, in the order the tree has them.
--|
--| `Lays` is what a document's rules prove: from the place the printer is
--| at and the trace so far, every way the document may print puts its
--| words where the predicate lists them (`printLays`). It is in
--| continuation style, as `Joins` is, and it doesn't follow modes: a
--| `Line` may be a space or a break wherever it stands.
--|
--| The trace is in the document's order. The printed order differs in one
--| way: a closer (`Closing`) that joins the line of a comment that waits
--| is printed before the comment (`Puts`, Places.sw, has the printed
--| order). `Tucks` says exactly that of the two orders: stretch by
--| stretch they are the same events, but that a trailing comment comes
--| after the closers the document has after it on its line. Every `Lays`
--| is a `Puts` of a printed trace the laid one `Tucks` to (`laysPuts`),
--| so the printer's theorem (`printPuts`) gives `printLays`.

namespace Toy.Doc.Proofs
import Toy.Doc (..)
import Std (Bool, DecEq, Eq, List, Nat, Option, Text, Void)

--| `--` and the rest of its line: a trailing comment's text.
def IsComment (text: Text): Prop :=
  ∃ (others: List Char) => text.toList = ['-', '-', ..others] ∧ others.all (char => char != '\n') = True

--| The texts `Closing` is for: a closing bracket or a comma.
def closesText (text: Text): Bool := text == ")" || text == "]" || text == ","

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

--| A closer in a construct indented `indent`: a chunk where no comment
--| waits; where one waits, a word on the comment's line, which the tree
--| has after the comment (the printer writes it before).
def CloseLays (indent: Nat) (text: Text) (place: Place) (trace: List Event) (next: Place → List Event → Prop): Prop :=
  match place with
    | Held at => closesText text = True ∧ next (Held at) (trace ++ [{ word = text, start = None }])
    | _ => WriteLays indent text place trace next

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

--| From `place` with `trace` laid, every way `doc` may print in a
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
    | Closing text => CloseLays indent text place trace next
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
    | LineSuffix comment => IsComment comment ∧ isLayout comment = False ∧ SuffixLays comment place trace next

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

theorem closeLaysWeaker ∀ (indent: Nat) (text: Text) (place: Place) (trace: List Event)
    (strong weak: Place → List Event → Prop)
    (implies: ∀ (after: Place) (later: List Event) => strong after later → weak after later)
    (lays: CloseLays indent text place trace strong):
    CloseLays indent text place trace weak :=
  match place, lays with
    | Held at, (closes, lays) => (closes, (implies _ _ lays))
    | AtStart at, lays => writeLaysWeaker indent text (AtStart at) trace strong weak implies lays
    | Broken at, lays => writeLaysWeaker indent text (Broken at) trace strong weak implies lays
    | Mid at, lays => writeLaysWeaker indent text (Mid at) trace strong weak implies lays

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
    | Closing text, lays => closeLaysWeaker indent text place trace strong weak implies lays
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
    | LineSuffix comment, (isComment, word, lays) =>
      (isComment, word, (suffixLaysWeaker comment place trace strong weak implies lays))

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

-- The laid order against the printed order.

--| A stretch of a trace: one event, or a trailing comment that waited
--| and the closers written on its line while it did.
type Stretch =
  | Kept (event: Event)
  | Tucked (comment: Event) (closers: List Event)

--| The stretch as the document has it: the comment, then the closers.
def Stretch.laid: Stretch → List Event
  | Kept event => [event]
  | Tucked comment closers => [comment, ..closers]

--| The stretch as it is printed: the closers, then the comment.
def Stretch.printed: Stretch → List Event
  | Kept event => [event]
  | Tucked comment closers => closers ++ [comment]

--| A closer written on a waiting comment's line: after other words.
def Closer (event: Event): Prop := event.start = None ∧ closesText event.word = True

--| A tucked stretch is a trailing comment and closers on its line.
def Stretch.Fits: Stretch → Prop
  | Kept event => True
  | Tucked comment closers => comment.start = None ∧ IsComment comment.word ∧ List.All Closer closers

def laidOf: List Stretch → List Event
  | [] => []
  | [first, ..rest] => first.laid ++ laidOf rest

def printedOf: List Stretch → List Event
  | [] => []
  | [first, ..rest] => first.printed ++ printedOf rest

--| An event that starts a line, or a blank line: what follows a
--| trailing comment's line.
def Stretch.Starts: Stretch → Prop
  | Kept event => (∃ (at: Nat) => event.start = Some at) ∨ event.word = "\n"
  | Tucked _ _ => False

--| After a trailing comment's stretch the next line starts: no word
--| follows a comment on its line but the closers tucked before it.
def LineEnded: List Stretch → Prop
  | [] => True
  | [only] => True
  | [Tucked comment closers, next, ..rest] => next.Starts ∧ LineEnded [next, ..rest]
  | [Kept event, next, ..rest] => LineEnded [next, ..rest]

def Stretch.IsKept: Stretch → Prop
  | Kept event => True
  | Tucked comment closers => False

--| The last stretch is one event (or there is none): no comment has
--| just been written.
def EndsKept: List Stretch → Prop
  | [] => True
  | [last] => last.IsKept
  | [first, next, ..rest] => EndsKept [next, ..rest]

--| `printed` is `laid` with each trailing comment after the closers that
--| were written on its line.
def Tucks (laid printed: List Event): Prop :=
  ∃ (stretches: List Stretch) => List.All Stretch.Fits stretches
    ∧ LineEnded stretches
    ∧ laid = laidOf stretches
    ∧ printed = printedOf stretches

--| As `Tucks`, after a word on its line: no comment was written last.
def Settles (laid printed: List Event): Prop :=
  ∃ (stretches: List Stretch) => List.All Stretch.Fits stretches
    ∧ LineEnded stretches
    ∧ EndsKept stretches
    ∧ laid = laidOf stretches
    ∧ printed = printedOf stretches

--| As `Tucks`, where a comment still waits: the last stretch is its.
def Waits (laid printed: List Event): Prop :=
  ∃ (stretches: List Stretch) => ∃ (comment: Event) => ∃ (closers: List Event) => List.All Stretch.Fits stretches
    ∧ LineEnded stretches
    ∧ EndsKept stretches
    ∧ Stretch.Fits (Tucked comment closers)
    ∧ laid = laidOf stretches ++ [comment, ..closers]
    ∧ printed = printedOf stretches ++ (closers ++ [comment])

--| The two traces at a place the printer is at.
def Tracks (place: Place) (laid printed: List Event): Prop := match place with
  | Held _ => Waits laid printed
  | Mid _ => Settles laid printed
  | _ => Tucks laid printed

theorem fitsSnoc ∀ (stretches: List Stretch) (last: Stretch)
    (all: List.All Stretch.Fits stretches) (fits: last.Fits):
    List.All Stretch.Fits (stretches ++ [last]) :=
  match stretches, all with
    | [], _ => (fits, ())
    | [first, ..rest], (firstFits, others) => (firstFits, (fitsSnoc rest last others fits))

theorem closersSnoc ∀ (closers: List Event) (last: Event)
    (all: List.All Closer closers)
    (closer: Closer last):
    List.All Closer (closers ++ [last]) :=
  match closers, all with
    | [], _ => (closer, ())
    | [first, ..rest], (firstCloser, others) => (firstCloser, (closersSnoc rest last others closer))

--| One more stretch keeps the stretches spaced, after an event or if it
--| starts a line.
theorem lineEndedSnoc ∀ (stretches: List Stretch) (last: Stretch)
    (spaced: LineEnded stretches)
    (apart: EndsKept stretches ∨ last.Starts):
    LineEnded (stretches ++ [last]) :=
  match stretches, spaced, apart with
    | [Tucked comment closers], _, Inl never => (Bool.falseNotTrue never).impossible
    | [Tucked comment closers], _, Inr starts => (starts, byComputing)
    | [Kept event, next, ..rest], spaced, apart => lineEndedSnoc [next, ..rest] last spaced apart
    | [Tucked comment closers, next, ..rest], (starts, spaced), apart =>
      (starts, (lineEndedSnoc [next, ..rest] last spaced apart))
    | _, _, _ => cases

theorem endsKeptSnoc ∀ (stretches: List Stretch) (event: Event): EndsKept (stretches ++ [Kept event]) :=
  match stretches with
    | [first, next, ..rest] => endsKeptSnoc [next, ..rest] event
    | _ => cases

theorem laidSnoc ∀ (stretches: List Stretch) (last: Stretch):
    laidOf (stretches ++ [last]) = laidOf stretches ++ last.laid :=
  match stretches with
    | [] => List.appendNil last.laid
    | [first, ..rest] =>
      calc first.laid ++ laidOf (rest ++ [last])
        _ = first.laid ++ (laidOf rest ++ last.laid) :=
          Eq.cong ((later: List Event) => first.laid ++ later) (laidSnoc rest last)
        _ = (first.laid ++ laidOf rest) ++ last.laid := (List.appendAssoc first.laid (laidOf rest) last.laid).flipped

theorem printedSnoc ∀ (stretches: List Stretch) (last: Stretch):
    printedOf (stretches ++ [last]) = printedOf stretches ++ last.printed :=
  match stretches with
    | [] => List.appendNil last.printed
    | [first, ..rest] =>
      calc first.printed ++ printedOf (rest ++ [last])
        _ = first.printed ++ (printedOf rest ++ last.printed) :=
          Eq.cong ((later: List Event) => first.printed ++ later) (printedSnoc rest last)
        _ = (first.printed ++ printedOf rest) ++ last.printed :=
          (List.appendAssoc first.printed (printedOf rest) last.printed).flipped

theorem settlesTucks ∀ (laid printed: List Event) (settles: Settles laid printed): Tucks laid printed :=
  match settles with
    | (stretches, fits, spaced, ends, sameLaid, samePrinted) => (stretches, fits, spaced, sameLaid, samePrinted)

--| An event after a word on its line, after both traces.
theorem settlesSnoc ∀ (laid printed: List Event) (event: Event)
    (settles: Settles laid printed):
    Settles (laid ++ [event]) (printed ++ [event]) :=
  match settles with
    | (stretches, fits, spaced, ends, sameLaid, samePrinted) => (
      (stretches ++ [Kept event]),
      (fitsSnoc stretches (Kept event) fits byComputing),
      (lineEndedSnoc stretches (Kept event) spaced (Inl ends)),
      (endsKeptSnoc stretches event),
      (rewrite sameLaid then (laidSnoc stretches (Kept event)).flipped),
      (rewrite samePrinted then (printedSnoc stretches (Kept event)).flipped)
    )

--| An event that starts a line, or a blank line, after both traces.
theorem tucksSnoc ∀ (laid printed: List Event) (event: Event)
    (tucks: Tucks laid printed)
    (starts: Stretch.Starts (Kept event)):
    Settles (laid ++ [event]) (printed ++ [event]) :=
  match tucks with
    | (stretches, fits, spaced, sameLaid, samePrinted) => (
      (stretches ++ [Kept event]),
      (fitsSnoc stretches (Kept event) fits byComputing),
      (lineEndedSnoc stretches (Kept event) spaced (Inr starts)),
      (endsKeptSnoc stretches event),
      (rewrite sameLaid then (laidSnoc stretches (Kept event)).flipped),
      (rewrite samePrinted then (printedSnoc stretches (Kept event)).flipped)
    )

--| A comment that waited has been written: its stretch is done.
theorem waitsTucks ∀ (laid printed: List Event) (waits: Waits laid printed): Tucks laid printed := match waits with
  | (stretches, comment, closers, fits, spaced, ends, last, sameLaid, samePrinted) => (
    (stretches ++ [Tucked comment closers]),
    (fitsSnoc stretches (Tucked comment closers) fits last),
    (lineEndedSnoc stretches (Tucked comment closers) spaced (Inl ends)),
    (rewrite sameLaid then (laidSnoc stretches (Tucked comment closers)).flipped),
    (rewrite samePrinted then (printedSnoc stretches (Tucked comment closers)).flipped)
  )

theorem tracksTucks ∀ (place: Place) (laid printed: List Event)
    (tracks: Tracks place laid printed):
    Tucks laid printed :=
  match place, tracks with
    | AtStart at, tucks => tucks
    | Broken at, tucks => tucks
    | Mid at, settles => settlesTucks laid printed settles
    | Held at, waits => waitsTucks laid printed waits

--| A trailing comment starts to wait: it is in both traces, last.
theorem settlesWaits ∀ (laid printed: List Event) (comment: Text)
    (settles: Settles laid printed)
    (isComment: IsComment comment):
    Waits (laid ++ [{ word = comment, start = None }]) (printed ++ [{ word = comment, start = None }]) :=
  match settles with
    | (stretches, fits, spaced, ends, sameLaid, samePrinted) => (
      stretches,
      ({ word = comment, start = None }),
      [],
      fits,
      spaced,
      ends,
      ((byComputing, isComment, ())),
      (rewrite sameLaid),
      (rewrite samePrinted)
    )

--| A closer written where a comment waits: after it in the laid trace,
--| before it in the printed one.
theorem waitsClose ∀ (laid printed: List Event) (text: Text)
    (waits: Waits laid printed)
    (closes: closesText text = True):
    Waits (laid ++ [{ word = text, start = None }]) (tucked { word = text, start = None } printed) :=
  match waits with
    | (stretches, comment, closers, fits, spaced, ends, (unstarted, isComment, closing), sameLaid, samePrinted) =>
      let closer: Event := { word = text, start = None }
      (
        stretches,
        comment,
        (closers ++ [closer]),
        fits,
        spaced,
        ends,
        ((unstarted, isComment, (closersSnoc closers closer closing ((byComputing, closes))))),
        (rewrite sameLaid then List.appendAssoc (laidOf stretches) [comment, ..closers] [closer]),
        (rewrite samePrinted then
          calc tucked closer (printedOf stretches ++ (closers ++ [comment]))
            _ = tucked closer ((printedOf stretches ++ closers) ++ [comment]) :=
              Eq.cong (tucked closer) (List.appendAssoc (printedOf stretches) closers [comment]).flipped
            _ = (printedOf stretches ++ closers) ++ [closer, comment] :=
              tuckedSnoc closer comment (printedOf stretches ++ closers)
            _ = printedOf stretches ++ (closers ++ [closer, comment]) :=
              List.appendAssoc (printedOf stretches) closers [closer, comment]
            _ = printedOf stretches ++ ((closers ++ [closer]) ++ [comment]) :=
              Eq.cong
                ((later: List Event) => printedOf stretches ++ later)
                (List.appendAssoc closers [closer] [comment]).flipped)
      )

theorem closesWord ∀ (text: Text) (closes: closesText text = True): isLayout text = False :=
  match round: text == ")" with
    | True =>
      let same: text = ")" := DecEq.sound round
      rewrite same
    | False =>
      match square: text == "]" with
        | True =>
          let same: text = "]" := DecEq.sound square
          rewrite same
        | False =>
          match comma: text == "," with
            | True =>
              let same: text = "," := DecEq.sound comma
              rewrite same

--| An instance of `closesWord`, so it isn't vacuous. The audit's random
--| search misses one: it rarely makes a text that is exactly `)`, `]` or `,`.
theorem closesWordExample: isLayout ")" = False := closesWord ")" byComputing

-- Every `Lays` is a `Puts`.

theorem writeLaysPuts ∀ (indent: Nat) (text: Text) (place: Place) (laid printed: List Event)
    (next put: Place → List Event → Prop)
    (onward: ∀ (after: Place) (later written: List Event) => Tracks after later written
      → next after later
      → put after written)
    (tracks: Tracks place laid printed)
    (lays: WriteLays indent text place laid next):
    WritePuts indent text place printed put :=
  match empty: text.isEmpty, lays with
    | True, lays => onward _ _ _ tracks lays
    | False, lays =>
      match spaces: text.all (char => char == ' '), lays with
        | True, lays =>
          match place, tracks, lays with
            | AtStart at, _, never => never
            | Broken at, _, never => never
            | Mid at, tracks, lays => onward _ _ _ tracks lays
            | Held at, tracks, lays => onward _ _ _ tracks lays
        | False, Both oneLine lays =>
          match place, tracks, lays with
            | AtStart at, tracks, lays =>
              (oneLine, (onward _ _ _ (tucksSnoc laid printed _ tracks (Inl ((at, byComputing)))) lays))
            | Broken at, tracks, lays =>
              (oneLine, (onward _ _ _ (tucksSnoc laid printed _ tracks (Inl ((at, byComputing)))) lays))
            | Mid at, tracks, lays => (oneLine, (onward _ _ _ (settlesSnoc laid printed _ tracks) lays))
            | Held at, tracks, lays => (
              oneLine,
              (onward _ _ _
                (tucksSnoc laid printed _
                  (waitsTucks laid printed tracks)
                  (Inl (((Nat.max indent (at + 2)), byComputing))))
                lays)
            )

theorem closeLaysPuts ∀ (indent: Nat) (text: Text) (place: Place) (laid printed: List Event)
    (next put: Place → List Event → Prop)
    (onward: ∀ (after: Place) (later written: List Event) => Tracks after later written
      → next after later
      → put after written)
    (tracks: Tracks place laid printed)
    (lays: CloseLays indent text place laid next):
    ClosePuts indent text place printed put :=
  match place, tracks, lays with
    | Held at, tracks, (closes, lays) =>
      ((closesWord text closes), (onward _ _ _ (waitsClose laid printed text tracks closes) lays))
    | AtStart at, tracks, lays => writeLaysPuts indent text (AtStart at) laid printed next put onward tracks lays
    | Broken at, tracks, lays => writeLaysPuts indent text (Broken at) laid printed next put onward tracks lays
    | Mid at, tracks, lays => writeLaysPuts indent text (Mid at) laid printed next put onward tracks lays

theorem sepLaysPuts ∀ (indent: Nat) (place: Place) (laid printed: List Event) (next put: Place → List Event → Prop)
    (onward: ∀ (after: Place) (later written: List Event) => Tracks after later written
      → next after later
      → put after written)
    (tracks: Tracks place laid printed)
    (lays: SepLays indent place laid next):
    SepPuts indent place printed put :=
  match place, tracks, lays with
    | AtStart at, _, never => never
    | Broken at, _, never => never
    | Mid at, tracks, Both same broken =>
      ((onward _ _ _ tracks same), (onward _ _ _ (settlesTucks laid printed tracks) broken))
    | Held at, tracks, broken => onward _ _ _ (waitsTucks laid printed tracks) broken

theorem softLaysPuts ∀ (indent: Nat) (place: Place) (laid printed: List Event) (next put: Place → List Event → Prop)
    (onward: ∀ (after: Place) (later written: List Event) => Tracks after later written
      → next after later
      → put after written)
    (tracks: Tracks place laid printed)
    (lays: SoftLays indent place laid next):
    SoftPuts indent place printed put :=
  match place, tracks, lays with
    | AtStart at, _, never => never
    | Broken at, _, never => never
    | Mid at, tracks, Both same broken =>
      ((onward _ _ _ tracks same), (onward _ _ _ (settlesTucks laid printed tracks) broken))
    | Held at, tracks, broken => onward _ _ _ (waitsTucks laid printed tracks) broken

theorem startLaysPuts ∀ (indent: Nat) (place: Place) (laid printed: List Event) (next put: Place → List Event → Prop)
    (onward: ∀ (after: Place) (later written: List Event) => Tracks after later written
      → next after later
      → put after written)
    (tracks: Tracks place laid printed)
    (lays: StartLays indent place laid next):
    StartPuts indent place printed put :=
  match place, tracks, lays with
    | AtStart at, tracks, lays => onward _ _ _ tracks lays
    | Broken at, tracks, lays => onward _ _ _ tracks lays
    | Mid at, tracks, lays => onward _ _ _ (settlesTucks laid printed tracks) lays
    | Held at, tracks, lays => onward _ _ _ (waitsTucks laid printed tracks) lays

theorem suffixLaysPuts ∀ (comment: Text) (place: Place) (laid printed: List Event) (next put: Place → List Event → Prop)
    (onward: ∀ (after: Place) (later written: List Event) => Tracks after later written
      → next after later
      → put after written)
    (tracks: Tracks place laid printed)
    (isComment: IsComment comment)
    (lays: SuffixLays comment place laid next):
    SuffixPuts comment place printed put :=
  match place, tracks, lays with
    | AtStart at, _, never => never
    | Broken at, _, never => never
    | Mid at, tracks, lays => onward _ _ _ (settlesWaits laid printed comment tracks isComment) lays
    | Held at, _, never => never

theorem blankLaysPuts ∀ (place: Place) (laid printed: List Event) (next put: Place → List Event → Prop)
    (onward: ∀ (after: Place) (later written: List Event) => Tracks after later written
      → next after later
      → put after written)
    (tracks: Tracks place laid printed)
    (lays: BlankLays place laid next):
    BlankPuts place printed put :=
  match place, tracks, lays with
    | AtStart at, _, never => never
    | Broken at, tracks, lays =>
      onward _ _ _ (settlesTucks _ _ (tucksSnoc laid printed Event.blankLine tracks (Inr byComputing))) lays
    | Mid at, tracks, lays => onward _ _ _ tracks lays
    | Held at, tracks, lays => onward _ _ _ tracks lays

--| What a document lays, the printer puts: from traces that track each
--| other, every way the document may print leaves traces that do. By
--| induction on the document; only a closer where a comment waits puts
--| its word elsewhere than it lays it (`waitsClose`).
theorem laysPuts ∀ (doc: Doc) (indent: Nat) (place: Place) (laid printed: List Event)
    (next put: Place → List Event → Prop)
    (onward: ∀ (after: Place) (later written: List Event) => Tracks after later written
      → next after later
      → put after written)
    (tracks: Tracks place laid printed)
    (lays: Lays doc indent place laid next):
    Puts doc indent place printed put :=
  match doc, lays with
    | Empty, lays => onward _ _ _ tracks lays
    | BreakParent, lays => onward _ _ _ tracks lays
    | Blank, lays => blankLaysPuts place laid printed next put onward tracks lays
    | Chunk text width, lays => writeLaysPuts indent text place laid printed next put onward tracks lays
    | Closing text, lays => closeLaysPuts indent text place laid printed next put onward tracks lays
    | Line, lays => sepLaysPuts indent place laid printed next put onward tracks lays
    | SoftLine, lays => softLaysPuts indent place laid printed next put onward tracks lays
    | HardLine, Both mid (Inl broken) => (mid, (Inl (onward _ _ _ (tracksTucks place laid printed tracks) broken)))
    | HardLine, Both mid (Inr started) => (mid, (Inr (onward _ _ _ (tracksTucks place laid printed tracks) started)))
    | CommentEnd, Both mid lays => (mid, (onward _ _ _ (tracksTucks place laid printed tracks) lays))
    | LineStart, lays => startLaysPuts indent place laid printed next put onward tracks lays
    | LineStartHere, lays => onward _ _ _ (tracksTucks place laid printed tracks) lays
    | Nest more inner, lays => laysPuts inner (indent + more) place laid printed next put onward tracks lays
    | Group inner hard, lays => laysPuts inner indent place laid printed next put onward tracks lays
    | Flatten inner, lays => laysPuts inner indent place laid printed next put onward tracks lays
    | OneLineBelow inner, Both mid lays => (
      mid,
      (laysPuts inner
        (indent + 2)
        (AtStart (indent + 2))
        laid
        printed
        next
        put
        onward
        (tracksTucks place laid printed tracks)
        lays)
    )
    | Concat docs, lays => allLaysPuts docs indent place laid printed next put onward tracks lays
    | Fill items, lays => fillLaysPuts items indent place laid printed next put onward tracks lays
    | Choice options, lays => optionsLayPuts options indent place laid printed next put onward tracks lays
    | LineSuffix comment, (isComment, word, lays) =>
      (word, (suffixLaysPuts comment place laid printed next put onward tracks isComment lays))

theorem allLaysPuts ∀ (docs: List Doc) (indent: Nat) (place: Place) (laid printed: List Event)
    (next put: Place → List Event → Prop)
    (onward: ∀ (after: Place) (later written: List Event) => Tracks after later written
      → next after later
      → put after written)
    (tracks: Tracks place laid printed)
    (lays: LaysAll docs indent place laid next):
    PutsAll docs indent place printed put :=
  match docs, lays with
    | [], lays => onward _ _ _ tracks lays
    | [doc, ..rest], lays =>
      laysPuts doc indent place laid printed
        (after later => LaysAll rest indent after later next)
        (after written => PutsAll rest indent after written put)
        (after later written tracked others =>
          allLaysPuts rest indent after later written next put onward tracked others)
        tracks
        lays

theorem fillLaysPuts ∀ (items: List Doc) (indent: Nat) (place: Place) (laid printed: List Event)
    (next put: Place → List Event → Prop)
    (onward: ∀ (after: Place) (later written: List Event) => Tracks after later written
      → next after later
      → put after written)
    (tracks: Tracks place laid printed)
    (lays: FillLays items indent place laid next):
    FillPuts items indent place printed put :=
  match items, lays with
    | [], lays => onward _ _ _ tracks lays
    | [first, ..others], lays =>
      laysPuts first indent place laid printed
        (after later => SepsLay others indent after later next)
        (after written => SepsPut others indent after written put)
        (after later written tracked seps => sepsLayPuts others indent after later written next put onward tracked seps)
        tracks
        lays

theorem sepsLayPuts ∀ (items: List Doc) (indent: Nat) (place: Place) (laid printed: List Event)
    (next put: Place → List Event → Prop)
    (onward: ∀ (after: Place) (later written: List Event) => Tracks after later written
      → next after later
      → put after written)
    (tracks: Tracks place laid printed)
    (lays: SepsLay items indent place laid next):
    SepsPut items indent place printed put :=
  match items, lays with
    | [], lays => onward _ _ _ tracks lays
    | [item, ..more], lays =>
      sepLaysPuts indent place laid printed
        (middle between => Lays item indent middle between (after later => SepsLay more indent after later next))
        (middle between => Puts item indent middle between (after written => SepsPut more indent after written put))
        (middle between written tracked inner =>
          laysPuts item indent middle between written
            (after later => SepsLay more indent after later next)
            (after wrote => SepsPut more indent after wrote put)
            (after later wrote followed seps => sepsLayPuts more indent after later wrote next put onward followed seps)
            tracked
            inner)
        tracks
        lays

theorem optionsLayPuts ∀ (options: List Doc) (indent: Nat) (place: Place) (laid printed: List Event)
    (next put: Place → List Event → Prop)
    (onward: ∀ (after: Place) (later written: List Event) => Tracks after later written
      → next after later
      → put after written)
    (tracks: Tracks place laid printed)
    (lays: OptionsLay options indent place laid next):
    OptionsPut options indent place printed put :=
  match options, lays with
    | [], lays => onward _ _ _ tracks lays
    | [last], lays => laysPuts last indent place laid printed next put onward tracks lays
    | [option, second, ..others], Both first rest => (
      (laysPuts option indent place laid printed next put onward tracks first),
      (optionsLayPuts [second, ..others] indent place laid printed next put onward tracks rest)
    )

--| A document that lays from the start of an unindented line, printed at
--| any width, lays each word where the document said: `spec` holds of a
--| trace in the document's order, and the words of the printed pieces,
--| each with the column it starts its line at, if it does, are that
--| trace with each trailing comment after the closers on its line.
theorem printLays ∀ (spec: Place → List Event → Prop) (doc: Doc) (width: Nat)
    (lays: Lays doc 0 (AtStart 0) [] spec):
    ∃ (place: Place) => ∃ (laid: List Event) => spec place laid
      ∧ Tucks laid (eventsOf (printedPieces doc width).reverse) :=
  let put: Place → List Event → Prop := place printed => ∃ (laid: List Event) => spec place laid ∧ Tucks laid printed
  let puts: Puts doc 0 (AtStart 0) [] put :=
    laysPuts doc 0
      (AtStart 0)
      []
      []
      spec
      put
      (after later written tracked holds => (later, holds, (tracksTucks after later written tracked)))
      (([], (), byComputing, byComputing, byComputing))
      lays
  match printPuts put doc width puts with | (place, laid, holds, tucks) => (place, laid, holds, tucks)
