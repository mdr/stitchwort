--| Where the printer puts each word. Through every reading, each word
--| written is at the place the document's own predicate (`Puts`) listed
--| for it: after other words on its line, or first on a line indented as
--| the document says (`printPuts`). The trace of a print, each word with
--| the column it starts its line at, if it does, is `eventsOf` of the
--| printed pieces, which is what the lexer will see of them: a token
--| starts its line when only spaces come before it there, at the column
--| the line is wide.
--|
--| `Puts` is in continuation style, as `Joins` is: from the place the
--| printer is at and the trace so far, a document hands every place and
--| trace it may leave to what comes after. It doesn't follow modes: a
--| `Line` may be a space or a break wherever it stands.
--|
--| The trace is in the order printed, which is the document's except
--| where a closer (`Closing`) joins the line of a comment that waits: the
--| comment is in the trace from when it starts to wait, and the closer
--| goes in before it (`tucked`), as it does in the text. The rules prove
--| `Lays` (Lays.sw), the same predicate with the trace in the document's
--| order, and `laysPuts` there takes it to this one.

namespace Fmt.Doc.Proofs
import Fmt.Doc (..)
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
--| lexer (the toy formatter's `placePiece`).
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
def WritePuts (indent: Nat) (text: Text) (place: Place) (trace: List Event) (next: Place → List Event → Prop): Prop :=
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

--| `event` put before the last of `trace`. Where a comment waits, it is
--| the trace's last event already, and a closer written then is printed
--| before it.
def tucked (event: Event): List Event → List Event
  | [] => [event]
  | [last] => [event, last]
  | [first, ..rest] => [first, ..tucked event rest]

--| A closer in a construct indented `indent`: a chunk where no comment
--| waits; where one waits, a word on the comment's line, before it.
def ClosePuts (indent: Nat) (text: Text) (place: Place) (trace: List Event) (next: Place → List Event → Prop): Prop :=
  match place with
    | Held at => isLayout text = False ∧ next (Held at) (tucked { word = text, start = None } trace)
    | _ => WritePuts indent text place trace next

--| Whether words are on the line: a line break here ends their line, and
--| leaves no blank line.
def Place.midLine: Place → Bool
  | AtStart _ => False
  | Broken _ => False
  | Mid _ => True
  | Held _ => True

--| A `Line` or a fill's separator: a space or a line break, after words.
def SepPuts (indent: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop): Prop := match place with
  | AtStart _ => False
  | Broken _ => False
  | Mid at => next (Mid at) trace ∧ next (AtStart indent) trace
  | Held _ => next (AtStart indent) trace

--| A `SoftLine`: nothing or a line break, after words; a line break if a
--| comment waits.
def SoftPuts (indent: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop): Prop :=
  match place with
    | AtStart _ => False
    | Broken _ => False
    | Mid at => next (Mid at) trace ∧ next (AtStart indent) trace
    | Held _ => next (AtStart indent) trace

--| A `LineStart`: a comment break, deeper than the line, unless a line
--| starts here.
def StartPuts (indent: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop): Prop :=
  match place with
    | AtStart at => next (AtStart at) trace
    | Broken at => next (AtStart at) trace
    | Mid at => next (AtStart (Nat.max indent (at + 2))) trace
    | Held at => next (AtStart (Nat.max indent (at + 2))) trace

--| A trailing comment: after words on its line, with no other waiting.
def SuffixPuts (comment: Text) (place: Place) (trace: List Event) (next: Place → List Event → Prop): Prop :=
  match place with
    | AtStart _ => False
    | Broken _ => False
    | Mid at => next (Held at) (trace ++ [{ word = comment, start = None }])
    | Held _ => False

--| A `Blank`: a blank line right after the line break that ended a line
--| of words; nothing after words; at no other line start, where the
--| printer may or may not leave one.
def BlankPuts (place: Place) (trace: List Event) (next: Place → List Event → Prop): Prop := match place with
  | AtStart _ => False
  | Broken at => next (AtStart at) (trace ++ [Event.blankLine])
  | Mid at => next (Mid at) trace
  | Held at => next (Held at) trace

--| An `Align`'s contents, given the indentation of their line breaks:
--| `atStart` at a line start, otherwise the column the `Align` starts at,
--| which a place doesn't say, so they must do for every column.
def AlignHolds (atStart: Nat) (place: Place) (inner: Nat → Prop): Prop := match place with
  | AtStart _ => inner atStart
  | Broken _ => inner atStart
  | Mid _ => ∀ (column: Nat) => inner column
  | Held _ => ∀ (column: Nat) => inner column

--| A `Displaced` element's contents in a construct indented `indent`,
--| given the indentation of their line breaks and where they start: at a
--| line start, the line's indentation if deeper; after words, the
--| construct's; after a waiting comment, a comment break's, on the line
--| it starts.
def DisplacedHolds (indent: Nat) (place: Place) (inner: Nat → Place → Prop): Prop := match place with
  | AtStart at => inner (Nat.max indent at) (AtStart at)
  | Broken at => inner (Nat.max indent at) (Broken at)
  | Mid at => inner indent (Mid at)
  | Held at => inner (Nat.max indent (at + 2)) (AtStart (Nat.max indent (at + 2)))

--| From `place` with `trace` printed, every way `doc` may print in a
--| construct indented `indent` puts its words where `next` is told, and
--| every place it may leave satisfies `next`. A line break that isn't a
--| `Line` or `SoftLine` comes only after words (at a line start it would
--| leave a blank line); after a `HardLine` the document says whether a
--| `Blank` follows (`Broken`) or not (`AtStart`).
def Puts (doc: Doc) (indent: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop): Prop :=
  match doc with
    | Empty => next place trace
    | BreakParent => next place trace
    | Blank => BlankPuts place trace next
    | Chunk text _ => WritePuts indent text place trace next
    | Closing text => ClosePuts indent text place trace next
    | Line => SepPuts indent place trace next
    | SoftLine => SoftPuts indent place trace next
    | HardLine => place.midLine = True ∧ (next (Broken indent) trace ∨ next (AtStart indent) trace)
    | CommentEnd => place.midLine = True ∧ next (AtStart place.indent) trace
    | LineStart => StartPuts indent place trace next
    | LineStartHere => next (AtStart indent) trace
    | Nest more inner => Puts inner (indent + more) place trace next
    | Align inner => AlignHolds indent place (column => Puts inner column place trace next)
    | AlignInset inner => AlignHolds (indent + 2) place (column => Puts inner column place trace next)
    | Displaced inner => DisplacedHolds indent place (column start => Puts inner column start trace next)
    | Group inner _ => Puts inner indent place trace next
    | NarrowGroup _ inner _ => Puts inner indent place trace next
    | IdGroup _ inner _ => Puts inner indent place trace next
    | IfBroken _ broken flat => Puts broken indent place trace next ∧ Puts flat indent place trace next
    | Flatten inner => Puts inner indent place trace next
    | OneLineBelow inner => place.midLine = True ∧ Puts inner (indent + 2) (AtStart (indent + 2)) trace next
    | Concat docs => PutsAll docs indent place trace next
    | Fill items => FillPuts items indent place trace next
    | Choice options => OptionsPut options indent place trace next
    | LineSuffix comment => isLayout comment = False ∧ SuffixPuts comment place trace next

--| Each of the docs in turn puts its words, from the place and trace the one
--| before left.
def PutsAll (docs: List Doc) (indent: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop): Prop :=
  match docs with
    | [] => next place trace
    | [doc, ..rest] => Puts doc indent place trace (after later => PutsAll rest indent after later next)

--| The items of a fill put their words, each after a separator that is a space
--| or a line break.
def FillPuts (items: List Doc) (indent: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop):
    Prop :=
  match items with
    | [] => next place trace
    | [first, ..others] => Puts first indent place trace (after later => SepsPut others indent after later next)

--| The separators before the items of a fill, and the items, put their words in
--| turn.
def SepsPut (items: List Doc) (indent: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop):
    Prop :=
  match items with
    | [] => next place trace
    | [item, ..more] => SepPuts indent place trace (middle between =>
      Puts item indent middle between (after later => SepsPut more indent after later next))

--| Every option a choice may take puts its words.
def OptionsPut (options: List Doc) (indent: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop):
    Prop :=
  match options with
    | [] => next place trace
    | [last] => Puts last indent place trace next
    | [option, ..others] => Puts option indent place trace next ∧ OptionsPut others indent place trace next

--| The work list, from `place` to the end, where `spec` is asked of the
--| place and the whole trace.
def StackPuts (spec: Place → List Event → Prop) (stack: List Cmd) (place: Place) (trace: List Event): Prop :=
  match stack with
    | [] => spec place trace
    | [Print indent _ doc, ..rest] => Puts doc indent place trace (after later => StackPuts spec rest after later)
    | [FillSep indent item, ..rest] => SepPuts indent place trace (middle between =>
      Puts item indent middle between (after later => StackPuts spec rest after later))

-- A weaker continuation still holds.

--| `WritePuts` holds with a weaker requirement on what follows, if it holds
--| with a stronger one.
theorem writePutsWeaker ∀ (indent: Nat) (text: Text) (place: Place) (trace: List Event)
    (strong weak: Place → List Event → Prop)
    (implies: ∀ (after: Place) (later: List Event) => strong after later → weak after later)
    (lays: WritePuts indent text place trace strong):
    WritePuts indent text place trace weak :=
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

--| `ClosePuts` holds with a weaker requirement on what follows, if it holds
--| with a stronger one.
theorem closePutsWeaker ∀ (indent: Nat) (text: Text) (place: Place) (trace: List Event)
    (strong weak: Place → List Event → Prop)
    (implies: ∀ (after: Place) (later: List Event) => strong after later → weak after later)
    (lays: ClosePuts indent text place trace strong):
    ClosePuts indent text place trace weak :=
  match place, lays with
    | Held at, (word, lays) => (word, (implies _ _ lays))
    | AtStart at, lays => writePutsWeaker indent text (AtStart at) trace strong weak implies lays
    | Broken at, lays => writePutsWeaker indent text (Broken at) trace strong weak implies lays
    | Mid at, lays => writePutsWeaker indent text (Mid at) trace strong weak implies lays

--| `SepPuts` holds with a weaker requirement on what follows, if it holds with
--| a stronger one.
theorem sepPutsWeaker ∀ (indent: Nat) (place: Place) (trace: List Event) (strong weak: Place → List Event → Prop)
    (implies: ∀ (after: Place) (later: List Event) => strong after later → weak after later)
    (lays: SepPuts indent place trace strong):
    SepPuts indent place trace weak :=
  match place, lays with
    | AtStart at, never => never
    | Broken at, never => never
    | Mid at, Both same broken => ((implies _ _ same), (implies _ _ broken))
    | Held at, broken => implies _ _ broken

--| `SoftPuts` holds with a weaker requirement on what follows, if it holds with
--| a stronger one.
theorem softPutsWeaker ∀ (indent: Nat) (place: Place) (trace: List Event) (strong weak: Place → List Event → Prop)
    (implies: ∀ (after: Place) (later: List Event) => strong after later → weak after later)
    (lays: SoftPuts indent place trace strong):
    SoftPuts indent place trace weak :=
  match place, lays with
    | AtStart at, never => never
    | Broken at, never => never
    | Mid at, Both same broken => ((implies _ _ same), (implies _ _ broken))
    | Held at, broken => implies _ _ broken

--| `StartPuts` holds with a weaker requirement on what follows, if it holds
--| with a stronger one.
theorem startPutsWeaker ∀ (indent: Nat) (place: Place) (trace: List Event) (strong weak: Place → List Event → Prop)
    (implies: ∀ (after: Place) (later: List Event) => strong after later → weak after later)
    (lays: StartPuts indent place trace strong):
    StartPuts indent place trace weak :=
  match place, lays with
    | AtStart at, lays => implies _ _ lays
    | Broken at, lays => implies _ _ lays
    | Mid at, lays => implies _ _ lays
    | Held at, lays => implies _ _ lays

--| `SuffixPuts` holds with a weaker requirement on what follows, if it holds
--| with a stronger one.
theorem suffixPutsWeaker ∀ (comment: Text) (place: Place) (trace: List Event) (strong weak: Place → List Event → Prop)
    (implies: ∀ (after: Place) (later: List Event) => strong after later → weak after later)
    (lays: SuffixPuts comment place trace strong):
    SuffixPuts comment place trace weak :=
  match place, lays with
    | AtStart at, never => never
    | Broken at, never => never
    | Mid at, lays => implies _ _ lays
    | Held at, never => never

--| `BlankPuts` holds with a weaker requirement on what follows, if it holds
--| with a stronger one.
theorem blankPutsWeaker ∀ (place: Place) (trace: List Event) (strong weak: Place → List Event → Prop)
    (implies: ∀ (after: Place) (later: List Event) => strong after later → weak after later)
    (lays: BlankPuts place trace strong):
    BlankPuts place trace weak :=
  match place, lays with
    | AtStart at, never => never
    | Broken at, lays => implies _ _ lays
    | Mid at, lays => implies _ _ lays
    | Held at, lays => implies _ _ lays

--| What holds with a continuation holds with any it implies.
theorem putsWeaker ∀ (doc: Doc) (indent: Nat) (place: Place) (trace: List Event)
    (strong weak: Place → List Event → Prop)
    (implies: ∀ (after: Place) (later: List Event) => strong after later → weak after later)
    (lays: Puts doc indent place trace strong):
    Puts doc indent place trace weak :=
  match doc, lays with
    | Empty, lays => implies _ _ lays
    | BreakParent, lays => implies _ _ lays
    | Blank, lays => blankPutsWeaker place trace strong weak implies lays
    | Chunk text width, lays => writePutsWeaker indent text place trace strong weak implies lays
    | Closing text, lays => closePutsWeaker indent text place trace strong weak implies lays
    | Line, lays => sepPutsWeaker indent place trace strong weak implies lays
    | SoftLine, lays => softPutsWeaker indent place trace strong weak implies lays
    | HardLine, Both mid (Inl broken) => (mid, (Inl (implies _ _ broken)))
    | HardLine, Both mid (Inr started) => (mid, (Inr (implies _ _ started)))
    | CommentEnd, Both mid lays => (mid, (implies _ _ lays))
    | LineStart, lays => startPutsWeaker indent place trace strong weak implies lays
    | LineStartHere, lays => implies _ _ lays
    | Nest more inner, lays => putsWeaker inner (indent + more) place trace strong weak implies lays
    | Align inner, lays =>
      match place, lays with
        | AtStart at, lays => putsWeaker inner indent (AtStart at) trace strong weak implies lays
        | Broken at, lays => putsWeaker inner indent (Broken at) trace strong weak implies lays
        | Mid at, lays => column => putsWeaker inner column (Mid at) trace strong weak implies (lays column)
        | Held at, lays => column => putsWeaker inner column (Held at) trace strong weak implies (lays column)
    | AlignInset inner, lays =>
      match place, lays with
        | AtStart at, lays => putsWeaker inner (indent + 2) (AtStart at) trace strong weak implies lays
        | Broken at, lays => putsWeaker inner (indent + 2) (Broken at) trace strong weak implies lays
        | Mid at, lays => column => putsWeaker inner column (Mid at) trace strong weak implies (lays column)
        | Held at, lays => column => putsWeaker inner column (Held at) trace strong weak implies (lays column)
    | Displaced inner, lays =>
      match place, lays with
        | AtStart at, lays => putsWeaker inner (Nat.max indent at) (AtStart at) trace strong weak implies lays
        | Broken at, lays => putsWeaker inner (Nat.max indent at) (Broken at) trace strong weak implies lays
        | Mid at, lays => putsWeaker inner indent (Mid at) trace strong weak implies lays
        | Held at, lays =>
          putsWeaker inner (Nat.max indent (at + 2)) (AtStart (Nat.max indent (at + 2))) trace strong weak implies lays
    | Group inner hard, lays => putsWeaker inner indent place trace strong weak implies lays
    | NarrowGroup max inner hard, lays => putsWeaker inner indent place trace strong weak implies lays
    | IdGroup id inner hard, lays => putsWeaker inner indent place trace strong weak implies lays
    | IfBroken id broken flat, Both brokenPuts flatPuts => (
      (putsWeaker broken indent place trace strong weak implies brokenPuts),
      (putsWeaker flat indent place trace strong weak implies flatPuts)
    )
    | Flatten inner, lays => putsWeaker inner indent place trace strong weak implies lays
    | OneLineBelow inner, Both mid lays =>
      (mid, (putsWeaker inner (indent + 2) (AtStart (indent + 2)) trace strong weak implies lays))
    | Concat docs, lays => allPutsWeaker docs indent place trace strong weak implies lays
    | Fill items, lays => fillPutsWeaker items indent place trace strong weak implies lays
    | Choice options, lays => optionsPutWeaker options indent place trace strong weak implies lays
    | LineSuffix comment, Both word lays => (word, (suffixPutsWeaker comment place trace strong weak implies lays))

--| `PutsAll` holds with a weaker requirement on what follows, if it holds with
--| a stronger one.
theorem allPutsWeaker ∀ (docs: List Doc) (indent: Nat) (place: Place) (trace: List Event)
    (strong weak: Place → List Event → Prop)
    (implies: ∀ (after: Place) (later: List Event) => strong after later → weak after later)
    (lays: PutsAll docs indent place trace strong):
    PutsAll docs indent place trace weak :=
  match docs, lays with
    | [], lays => implies _ _ lays
    | [doc, ..rest], lays =>
      putsWeaker doc indent place trace
        (after later => PutsAll rest indent after later strong)
        (after later => PutsAll rest indent after later weak)
        (after later others => allPutsWeaker rest indent after later strong weak implies others)
        lays

--| `FillPuts` holds with a weaker requirement on what follows, if it holds with
--| a stronger one.
theorem fillPutsWeaker ∀ (items: List Doc) (indent: Nat) (place: Place) (trace: List Event)
    (strong weak: Place → List Event → Prop)
    (implies: ∀ (after: Place) (later: List Event) => strong after later → weak after later)
    (lays: FillPuts items indent place trace strong):
    FillPuts items indent place trace weak :=
  match items, lays with
    | [], lays => implies _ _ lays
    | [first, ..others], lays =>
      putsWeaker first indent place trace
        (after later => SepsPut others indent after later strong)
        (after later => SepsPut others indent after later weak)
        (after later seps => sepsPutWeaker others indent after later strong weak implies seps)
        lays

--| `SepsPut` holds with a weaker requirement on what follows, if it holds with
--| a stronger one.
theorem sepsPutWeaker ∀ (items: List Doc) (indent: Nat) (place: Place) (trace: List Event)
    (strong weak: Place → List Event → Prop)
    (implies: ∀ (after: Place) (later: List Event) => strong after later → weak after later)
    (lays: SepsPut items indent place trace strong):
    SepsPut items indent place trace weak :=
  match items, lays with
    | [], lays => implies _ _ lays
    | [item, ..more], lays =>
      sepPutsWeaker indent place trace
        (middle between => Puts item indent middle between (after later => SepsPut more indent after later strong))
        (middle between => Puts item indent middle between (after later => SepsPut more indent after later weak))
        (middle between inner =>
          putsWeaker item indent middle between
            (after later => SepsPut more indent after later strong)
            (after later => SepsPut more indent after later weak)
            (after later seps => sepsPutWeaker more indent after later strong weak implies seps)
            inner)
        lays

--| `OptionsPut` holds with a weaker requirement on what follows, if it holds
--| with a stronger one.
theorem optionsPutWeaker ∀ (options: List Doc) (indent: Nat) (place: Place) (trace: List Event)
    (strong weak: Place → List Event → Prop)
    (implies: ∀ (after: Place) (later: List Event) => strong after later → weak after later)
    (lays: OptionsPut options indent place trace strong):
    OptionsPut options indent place trace weak :=
  match options, lays with
    | [], lays => implies _ _ lays
    | [last], lays => putsWeaker last indent place trace strong weak implies lays
    | [option, second, ..others], Both first rest => (
      (putsWeaker option indent place trace strong weak implies first),
      (optionsPutWeaker [second, ..others] indent place trace strong weak implies rest)
    )

-- What a step pushes on the work list lays as the document it came from.

--| Docs printed in order, then the work list, put their words if the docs do
--| and then the work list.
theorem printsPut ∀ (spec: Place → List Event → Prop) (indent: Nat) (mode: Mode) (docs: List Doc) (rest: List Cmd)
    (place: Place) (trace: List Event)
    (lays: PutsAll docs indent place trace (after later => StackPuts spec rest after later)):
    StackPuts spec (docs.map (Print indent mode) ++ rest) place trace :=
  match docs, lays with
    | [], lays => lays
    | [doc, ..others], lays =>
      putsWeaker doc indent place trace
        (after later => PutsAll others indent after later (final last => StackPuts spec rest final last))
        (after later => StackPuts spec (others.map (Print indent mode) ++ rest) after later)
        (after later more => printsPut spec indent mode others rest after later more)
        lays

--| Items with a `Line` between each two put their words if the first does and
--| then the rest, each after a separator.
theorem linesPut ∀ (first: Doc) (others: List Doc) (indent: Nat) (place: Place)
    (trace: List Event) (next: Place → List Event → Prop)
    (lays: Puts first indent place trace (after later => SepsPut others indent after later next)):
    PutsAll (Doc.joinLines [first, ..others]) indent place trace next :=
  match others, lays with
    | [], lays => lays
    | [second, ..rest], lays =>
      putsWeaker first indent place trace
        (after later => SepsPut [second, ..rest] indent after later next)
        (after later => PutsAll [Line, ..Doc.joinLines [second, ..rest]] indent after later next)
        (after later seps =>
          sepPutsWeaker indent after later
            (middle between => Puts second indent middle between (final last => SepsPut rest indent final last next))
            (middle between => PutsAll (Doc.joinLines [second, ..rest]) indent middle between next)
            (middle between inner => linesPut second rest indent middle between next inner)
            seps)
        lays

--| The separators before a fill's items, then the work list, put their words if
--| the items do and then the work list.
theorem fillSepsPut ∀ (spec: Place → List Event → Prop) (indent: Nat) (items: List Doc) (rest: List Cmd)
    (place: Place) (trace: List Event)
    (lays: SepsPut items indent place trace (after later => StackPuts spec rest after later)):
    StackPuts spec (items.map (FillSep indent) ++ rest) place trace :=
  match items, lays with
    | [], lays => lays
    | [item, ..more], lays =>
      sepPutsWeaker indent place trace
        (middle between =>
          Puts item indent middle between (after later =>
            SepsPut more indent after later (final last => StackPuts spec rest final last)))
        (middle between =>
          Puts item indent middle between (after later =>
            StackPuts spec (more.map (FillSep indent) ++ rest) after later))
        (middle between inner =>
          putsWeaker item indent middle between
            (after later => SepsPut more indent after later (final last => StackPuts spec rest final last))
            (after later => StackPuts spec (more.map (FillSep indent) ++ rest) after later)
            (after later seps => fillSepsPut spec indent more rest after later seps)
            inner)
        lays

--| A doc that is one of the options of a choice puts its words as the options
--| do.
theorem optionPuts ∀ (chosen: Doc) (options: List Doc) (indent: Nat) (place: Place)
    (trace: List Event) (next: Place → List Event → Prop)
    (isOption: IsOption chosen options)
    (lays: OptionsPut options indent place trace next):
    Puts chosen indent place trace next :=
  match options, isOption, lays with
    | [], picked, lays => rewrite picked then lays
    | [last], picked, lays => rewrite picked then lays
    | [option, second, ..others], Inl picked, Both first _ => rewrite picked then first
    | [option, second, ..others], Inr later, Both _ rest =>
      optionPuts chosen [second, ..others] indent place trace next later rest

--| The first option of a choice puts its words as the options do.
theorem headOrPuts ∀ (options: List Doc) (indent: Nat) (place: Place)
    (trace: List Event) (next: Place → List Event → Prop)
    (lays: OptionsPut options indent place trace next):
    Puts (options.headOr Empty) indent place trace next :=
  match options, lays with
    | [], lays => lays
    | [last], lays => lays
    | [option, second, ..others], Both first _ => first

-- The output's side: events, blank lines and widths, a piece at a time.

--| Spaces aren't a line break.
theorem gapNoBreak ∀ (piece: Text) (gap: piece.all (char => char == ' ') = True): (piece == "\n") = False :=
  match isBreak: piece == "\n" with
    | False => byComputing
    | True =>
      let same: piece = "\n" := DecEq.sound isBreak
      let never: "\n".all (char => char == ' ') = True := rewrite <- same then gap
      match never with
        | ()

--| Spaces are layout.
theorem gapLayout ∀ (piece: Text) (gap: piece.all (char => char == ' ') = True): isLayout piece = True :=
  Eq.cong ((spaces: Bool) => spaces || piece == "\n") gap

--| A word on top of the output is an event at its line's start, if only layout
--| is before it, else not at a line start.
theorem eventsWord ∀ (piece: Text) (earlier: List Text)
    (word: isLayout piece = False):
    eventsOf [piece, ..earlier]
      = eventsOf earlier ++ [{ word = piece, start = if lineBlank earlier then Some (lineWidth earlier) else None }] :=
  match layout: isLayout piece, word with
    | False, _ => byComputing
    | True, never =>
      match never with
        | ()

--| Spaces are no event.
theorem eventsGap ∀ (piece: Text) (earlier: List Text)
    (gap: piece.all (char => char == ' ') = True):
    eventsOf [piece, ..earlier] = eventsOf earlier :=
  rewrite gapLayout piece gap, gapNoBreak piece gap

--| The line break that ends a line of words is no event.
theorem eventsBreak ∀ (earlier: List Text)
    (words: lineBlank earlier = False):
    eventsOf ["\n", ..earlier] = eventsOf earlier :=
  rewrite words

--| A line break on a line with nothing but spaces is a blank line.
theorem eventsBlank ∀ (earlier: List Text)
    (blank: lineBlank earlier = True):
    eventsOf ["\n", ..earlier] = eventsOf earlier ++ [Event.blankLine] :=
  rewrite blank

--| A line with a word on it isn't blank.
theorem blankWord ∀ (piece: Text) (earlier: List Text)
    (word: isLayout piece = False):
    lineBlank [piece, ..earlier] = False :=
  match gap: piece.all (char => char == ' '), word with
    | True, never => (Bool.falseNotTrue never.flipped).impossible
    | False, word => word

--| Spaces don't change whether a line is blank.
theorem blankGap ∀ (piece: Text) (earlier: List Text)
    (gap: piece.all (char => char == ' ') = True):
    lineBlank [piece, ..earlier] = lineBlank earlier :=
  match spaces: piece.all (char => char == ' '), gap with
    | True, _ => byComputing
    | False, never =>
      match never with
        | ()

--| A piece that isn't a line break adds its length to the line's width.
theorem widthPiece ∀ (piece: Text) (earlier: List Text)
    (oneLine: (piece == "\n") = False):
    lineWidth [piece, ..earlier] = piece.length + lineWidth earlier :=
  match isBreak: piece == "\n", oneLine with
    | False, _ => byComputing
    | True, never =>
      match never with
        | ()

--| A last piece that isn't only spaces is kept when spaces at the end are
--| dropped.
theorem trimKeep ∀ (last: Text) (earlier: List Text)
    (word: last.all (char => char == ' ') = False):
    trimSpaces [last, ..earlier] = [last, ..earlier] :=
  match spaces: last.all (char => char == ' '), word with
    | False, _ => byComputing
    | True, never =>
      match never with
        | ()

--| A last piece of spaces is dropped with any spaces before it.
theorem trimDrop ∀ (last: Text) (earlier: List Text)
    (gap: last.all (char => char == ' ') = True):
    trimSpaces [last, ..earlier] = trimSpaces earlier :=
  match spaces: last.all (char => char == ' '), gap with
    | True, _ => byComputing
    | False, never =>
      match never with
        | ()

--| Dropping the spaces at the end of the output leaves its events the same,
--| given the same for the earlier output.
theorem trimEventsBy ∀ (last: Text) (earlier: List Text) (spaces: Bool)
    (is: last.all (char => char == ' ') = spaces)
    (rest: eventsOf (trimSpaces earlier) = eventsOf earlier):
    eventsOf (trimSpaces [last, ..earlier]) = eventsOf [last, ..earlier] :=
  match spaces, is with
    | True, gap => rewrite trimDrop last earlier gap then Eq.trans rest (eventsGap last earlier gap).flipped
    | False, word => rewrite trimKeep last earlier word

--| The spaces a line break drops are no words.
theorem trimEvents ∀ (out: List Text): eventsOf (trimSpaces out) = eventsOf out := match out with
  | [] => byComputing
  | [last, ..earlier] => trimEventsBy last earlier _ byComputing (trimEvents earlier)

--| Dropping the spaces at the end of the output leaves a line's blankness the
--| same, given the same for the earlier output.
theorem trimBlankBy ∀ (last: Text) (earlier: List Text) (spaces: Bool)
    (is: last.all (char => char == ' ') = spaces)
    (rest: lineBlank (trimSpaces earlier) = lineBlank earlier):
    lineBlank (trimSpaces [last, ..earlier]) = lineBlank [last, ..earlier] :=
  match spaces, is with
    | True, gap => rewrite trimDrop last earlier gap then Eq.trans rest (blankGap last earlier gap).flipped
    | False, word => rewrite trimKeep last earlier word

--| Dropping the spaces at the end of the output leaves a line's blankness the
--| same.
theorem trimBlank ∀ (out: List Text): lineBlank (trimSpaces out) = lineBlank out := match out with
  | [] => byComputing
  | [last, ..earlier] => trimBlankBy last earlier _ byComputing (trimBlank earlier)

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

--| The printer is at `place` with `trace` printed: its output, indentation owed
--| and waiting comments are what the place says.
def Agrees (printer: Printer) (place: Place) (trace: List Event): Prop :=
  AgreesParts printer.out printer.owed printer.atLineStart printer.suffixes printer.lineIndent printer.started
      printer.newlinesAtEnd place trace

--| The printer is at a place and trace that `next` holds of.
def Stays (next: Place → List Event → Prop) (printer: Printer): Prop :=
  ∃ (place: Place) => ∃ (trace: List Event) => Agrees printer place trace ∧ next place trace

--| `Some` isn't `None`.
theorem someNotNone ∀ (value: Nat) (wrong: Some value = None): Void := cases

--| A list with a first item isn't empty.
theorem consNotNil ∀ (first: Text) (more: List Text) (wrong: [first, ..more] = []): Void := cases

--| A word put at a line start starts the line, at the indentation owed.
theorem putStart ∀ (printer: Printer) (text: Text) (width at: Nat) (trace: List Event)
    (agrees: Agrees printer (AtStart at) trace)
    (word: isLayout text = False):
    Agrees (printer.put text width) (Mid at) (trace ++ [{ word = text, start = Some at }]) :=
  match printer, agrees with
    | { width = total, out, column, owed, atLineStart, suffixes, lineIndent, newlinesAtEnd, started, modes }, (start,
        none, blank, empty, owes, indent, same) =>
      match owed, owes with
        | None, owes => (
          byComputing,
          none,
          (blankWord text out word),
          byComputing,
          indent,
          (rewrite <- owes, eventsWord text out word, blank, empty, same),
          byComputing
        )
        | Some Zero, owes => (
          byComputing,
          none,
          (blankWord text out word),
          byComputing,
          indent,
          (rewrite <- owes, eventsWord text out word, blank, empty, same),
          byComputing
        )
        | Some (Succ less), owes =>
          let stillBlank: lineBlank [" ".repeat (Succ less), ..out] = True :=
            Eq.trans (blankGap (" ".repeat (Succ less)) out (indentSpaces (Succ less))) blank
          let sum := widthPiece (" ".repeat (Succ less)) out (gapNoBreak _ (indentSpaces (Succ less)))
          let length := indentLength (Succ less)
          let wide: lineWidth [" ".repeat (Succ less), ..out] = Succ less := arithmetic
          (
            byComputing,
            none,
            (blankWord text [" ".repeat (Succ less), ..out] word),
            byComputing,
            indent,
            (rewrite <- owes,
                eventsWord text [" ".repeat (Succ less), ..out] word,
                eventsGap (" ".repeat (Succ less)) out (indentSpaces (Succ less)),
                stillBlank,
                wide,
                same),
            byComputing
          )

--| A word put after words on its line doesn't start the line.
theorem putMid ∀ (printer: Printer) (text: Text) (width at: Nat) (trace: List Event)
    (agrees: Agrees printer (Mid at) trace)
    (word: isLayout text = False):
    Agrees (printer.put text width) (Mid at) (trace ++ [{ word = text, start = None }]) :=
  match printer, agrees with
    | { width = total, out, column, owed, atLineStart, suffixes, lineIndent, newlinesAtEnd, started, modes }, (start,
        none, blank, owes, indent, same, _) =>
      match owed, owes with
        | Some value, never => (someNotNone value never).impossible
        | None, _ => (
          byComputing,
          none,
          (blankWord text out word),
          byComputing,
          indent,
          (rewrite eventsWord text out word, blank, same),
          byComputing
        )

--| Spaces put after words change nothing but the width.
theorem putSpaces ∀ (printer: Printer) (text: Text) (width at: Nat) (trace: List Event)
    (agrees: Agrees printer (Mid at) trace)
    (gap: text.all (char => char == ' ') = True):
    Agrees (printer.put text width) (Mid at) trace :=
  match printer, agrees with
    | { width = total, out, column, owed, atLineStart, suffixes, lineIndent, newlinesAtEnd, started, modes }, (start,
        none, blank, owes, indent, same, _) =>
      match owed, owes with
        | Some value, never => (someNotNone value never).impossible
        | None, _ => (
          byComputing,
          none,
          (Eq.trans (blankGap text out gap) blank),
          byComputing,
          indent,
          (Eq.trans same (eventsGap text out gap).flipped),
          byComputing
        )

--| After the line break that ends a line of words the printer is at the
--| start of a line indented as asked, with one line break behind it, and
--| a comment that waited is written where the trace has it.
theorem newlineBroken ∀ (printer: Printer) (indent: Nat) (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace)
    (mid: place.midLine = True):
    Agrees (printer.newline indent) (Broken indent) trace :=
  match printer, place, agrees, mid with
    | { width = total, out, column, owed, atLineStart, suffixes, lineIndent, newlinesAtEnd, started, modes }, Mid
          at, Both start (Both none (Both blank (Both owes (Both same (Both events zero))))), _ =>
      match suffixes, none with
        | [first, ..more], never => (consNotNil first more never).impossible
        | [], _ =>
          let words: lineBlank (trimSpaces out) = False := Eq.trans (trimBlank out) blank
          (
            byComputing,
            byComputing,
            byComputing,
            byComputing,
            byComputing,
            byComputing,
            (Eq.trans events (Eq.flipped (Eq.trans (eventsBreak (trimSpaces out) words) (trimEvents out)))),
            byComputing,
            (Eq.cong ((count: Nat) => count + 1) zero)
          )
    | { width = total, out, column, owed, atLineStart, suffixes, lineIndent, newlinesAtEnd, started, modes }, Held
          at, Both start (Both (Witness comment (Both one (Both word events))) (Both blank (Both owes same))), _ =>
      let written: eventsOf [comment, " ", ..trimSpaces out] = eventsOf out ++ [{ word = comment, start = None }] :=
        rewrite eventsWord comment [" ", ..trimSpaces out] word, trimBlank out, blank, trimEvents out
      let ended: eventsOf ["\n", comment, " ", ..trimSpaces out] = eventsOf [comment, " ", ..trimSpaces out] :=
        eventsBreak [comment, " ", ..trimSpaces out] (blankWord comment [" ", ..trimSpaces out] word)
      rewrite one, start then
        (
          byComputing,
          byComputing,
          byComputing,
          byComputing,
          byComputing,
          byComputing,
          (Eq.trans events (Eq.trans ended written).flipped),
          byComputing,
          byComputing
        )

--| A place that allows a `Blank` is a line start.
theorem brokenStart ∀ (printer: Printer) (at: Nat) (trace: List Event)
    (agrees: Agrees printer (Broken at) trace):
    Agrees printer (AtStart at) trace :=
  match agrees with
    | (start, none, blank, empty, owes, indent, events, _) => (start, none, blank, empty, owes, indent, events)

--| A line break from the middle of a line leaves the printer at the start of a
--| line with the same trace.
theorem newlineAgrees ∀ (printer: Printer) (indent: Nat) (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace)
    (mid: place.midLine = True):
    Agrees (printer.newline indent) (AtStart indent) trace :=
  brokenStart (printer.newline indent) indent trace (newlineBroken printer indent place trace agrees mid)

--| A printer agreeing with a place has the place's indentation as its line's.
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
    | AtStart at, Both _ (Both none _) => rewrite none
    | Broken at, Both _ (Both none _) => rewrite none
    | Mid at, Both _ (Both none _) => rewrite none
    | Held at, Both _ (Both (Witness comment (Both one _)) _) => rewrite one

--| A printer agreeing with a place is at a line start exactly at the places
--| that start a line.
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

--| Text that isn't only spaces or a line break is a word.
theorem wordNotLayout ∀ (text: Text)
    (word: text.all (char => char == ' ') = False)
    (oneLine: (text == "\n") = False):
    isLayout text = False :=
  match gap: text.all (char => char == ' '), word with
    | False, _ => oneLine
    | True, never =>
      match never with
        | ()

--| A line break from the middle of a line leaves the printer at a place that
--| satisfies what follows.
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
    rewrite agreesIndent printer place trace agrees then after
  newlineStays next printer (printer.continuation indent) place trace agrees mid deeper

--| Writing at a line start, with no comment waiting, leaves the printer at a
--| place that satisfies what follows.
theorem writeStart ∀ (next: Place → List Event → Prop) (printer: Printer) (indent: Nat) (text: Text)
    (width at: Nat) (trace: List Event)
    (agrees: Agrees printer (AtStart at) trace)
    (clear: printer.suffixes.isEmpty = True)
    (lays: WritePuts indent text (AtStart at) trace next):
    Stays next (printer.write indent text width) :=
  match empty: text.isEmpty, lays with
    | True, lays => ((AtStart at), trace, agrees, lays)
    | False, lays =>
      match spaces: text.all (char => char == ' '), lays with
        | True, never => (Bool.falseNotTrue never).impossible
        | False, Both oneLine lays =>
          match waiting: printer.suffixes.isEmpty, clear with
            | True, _ =>
              ((Mid at), _, (putStart printer text width at trace agrees (wordNotLayout text spaces oneLine)), lays)

--| Writing in the middle of a line, with no comment waiting, leaves the printer
--| at a place that satisfies what follows.
theorem writeMid ∀ (next: Place → List Event → Prop) (printer: Printer) (indent: Nat) (text: Text)
    (width at: Nat) (trace: List Event)
    (agrees: Agrees printer (Mid at) trace)
    (clear: printer.suffixes.isEmpty = True)
    (lays: WritePuts indent text (Mid at) trace next):
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

--| Writing while a comment waits leaves the printer at a place that satisfies
--| what follows.
theorem writeHeld ∀ (next: Place → List Event → Prop) (printer: Printer) (indent: Nat) (text: Text)
    (width at: Nat) (trace: List Event)
    (agrees: Agrees printer (Held at) trace)
    (waits: printer.suffixes.isEmpty = False)
    (lays: WritePuts indent text (Held at) trace next):
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
            rewrite agreesIndent printer (Held at) trace agrees then lays
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
                (newlineAgrees printer (printer.continuation indent) (Held at) trace agrees byComputing)
                (wordNotLayout text spaces oneLine)),
              deeper
            )

--| Writing after a blank line, with no comment waiting, leaves the printer at a
--| place that satisfies what follows.
theorem writeBroken ∀ (next: Place → List Event → Prop) (printer: Printer) (indent: Nat) (text: Text)
    (width at: Nat) (trace: List Event)
    (agrees: Agrees printer (Broken at) trace)
    (clear: printer.suffixes.isEmpty = True)
    (lays: WritePuts indent text (Broken at) trace next):
    Stays next (printer.write indent text width) :=
  match empty: text.isEmpty, lays with
    | True, lays => ((Broken at), trace, agrees, lays)
    | False, lays =>
      match spaces: text.all (char => char == ' '), lays with
        | True, never => (Bool.falseNotTrue never).impossible
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
    (lays: WritePuts indent text place trace next):
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

--| A comment tucked into events that end with `last` goes before `last`.
theorem tuckedSnoc ∀ (event last: Event) (before: List Event):
    tucked event (before ++ [last]) = before ++ [event, last] :=
  match before with
    | [first, second, ..rest] => rewrite repeatedly [tuckedSnoc event last [second, ..rest]]
    | _ => cases

--| A word put on a line where a comment waits goes before the comment,
--| which still waits.
theorem putHeld ∀ (printer: Printer) (text: Text) (width at: Nat) (trace: List Event)
    (agrees: Agrees printer (Held at) trace)
    (word: isLayout text = False):
    Agrees (printer.put text width) (Held at) (tucked { word = text, start = None } trace) :=
  match printer, agrees with
    | { width = total, out, column, owed, atLineStart, suffixes, lineIndent, newlinesAtEnd, started, modes }, Both start
        (Both (Witness comment (Both one (Both isWord same))) (Both blank (Both owes indent))) =>
      match owed, owes with
        | Some value, never => (someNotNone value never).impossible
        | None, _ => (
          byComputing,
          ((
            comment,
            one,
            isWord,
            (rewrite repeatedly [same, tuckedSnoc, eventsWord text out word, blank, List.appendAssoc])
          )),
          (blankWord text out word),
          byComputing,
          indent
        )

--| A closer written where the document said.
theorem closeStays ∀ (next: Place → List Event → Prop) (printer: Printer) (indent: Nat) (text: Text)
    (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace)
    (lays: ClosePuts indent text place trace next):
    Stays next (printer.close text) :=
  match place, agrees, lays with
    | AtStart at, agrees, lays =>
      rewrite closeClear printer indent text (agreesClear printer (AtStart at) trace agrees) then
        writeStays next printer indent text text.length (AtStart at) trace agrees lays
    | Broken at, agrees, lays =>
      rewrite closeClear printer indent text (agreesClear printer (Broken at) trace agrees) then
        writeStays next printer indent text text.length (Broken at) trace agrees lays
    | Mid at, agrees, lays =>
      rewrite closeClear printer indent text (agreesClear printer (Mid at) trace agrees) then
        writeStays next printer indent text text.length (Mid at) trace agrees lays
    | Held at, agrees, (word, lays) =>
      rewrite closePut printer text (wordFilled text word) then
        (
          (Held at),
          (tucked { word = text, start = None } trace),
          (putHeld printer text text.length at trace agrees word),
          lays
        )

--| A separator's puts, where it breaks, hold `next` at the start of a line.
theorem sepBroken ∀ (next: Place → List Event → Prop) (indent: Nat) (place: Place) (trace: List Event)
    (lays: SepPuts indent place trace next):
    next (AtStart indent) trace :=
  match place, lays with
    | AtStart at, never => (Bool.falseNotTrue never).impossible
    | Broken at, never => (Bool.falseNotTrue never).impossible
    | Mid at, Both _ broken => broken
    | Held at, broken => broken

--| A separator's puts are only met in the middle of a line.
theorem sepMid ∀ (next: Place → List Event → Prop) (indent: Nat) (place: Place) (trace: List Event)
    (lays: SepPuts indent place trace next):
    place.midLine = True :=
  match place, lays with
    | AtStart at, never => never
    | Broken at, never => never
    | _, _ => cases

--| A soft line's puts are only met in the middle of a line.
theorem softMid ∀ (next: Place → List Event → Prop) (indent: Nat) (place: Place) (trace: List Event)
    (lays: SoftPuts indent place trace next):
    place.midLine = True :=
  match place, lays with
    | AtStart at, never => never
    | Broken at, never => never
    | _, _ => cases

--| With nothing at the start of its line the printer is after words.
theorem startMid ∀ (printer: Printer) (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace)
    (start: printer.atLineStart = False):
    place.midLine = True :=
  match place, agrees with
    | AtStart at, Both other _ => Eq.trans start.flipped other
    | Broken at, Both other _ => Eq.trans start.flipped other
    | _, _ => cases

--| A separator written as a space, with no comment waiting.
theorem sepSpace ∀ (next: Place → List Event → Prop) (printer: Printer) (indent: Nat) (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace)
    (clear: printer.suffixes.isEmpty = True)
    (lays: SepPuts indent place trace next):
    Stays next (printer.write indent " " 1) :=
  match place, agrees, lays with
    | AtStart at, _, never => (Bool.falseNotTrue never).impossible
    | Broken at, _, never => (Bool.falseNotTrue never).impossible
    | Mid at, agrees, Both same _ =>
      match waiting: printer.suffixes.isEmpty, clear with
        | True, _ => ((Mid at), trace, (putSpaces printer " " 1 at trace agrees byComputing), same)
    | Held at, agrees, _ =>
      Void.impossible (Bool.falseNotTrue (Eq.trans (Eq.flipped (agreesClear printer (Held at) trace agrees)) clear))

--| A soft line's puts, where it breaks, hold `next` at the start of a line.
theorem softBroken ∀ (next: Place → List Event → Prop) (indent: Nat) (place: Place) (trace: List Event)
    (lays: SoftPuts indent place trace next):
    next (AtStart indent) trace :=
  match place, lays with
    | AtStart at, never => (Bool.falseNotTrue never).impossible
    | Broken at, never => (Bool.falseNotTrue never).impossible
    | Mid at, Both _ broken => broken
    | Held at, broken => broken

--| A soft line's puts, where it stays flat with no comment waiting, hold `next`
--| at the place as it was.
theorem softSame ∀ (next: Place → List Event → Prop) (printer: Printer) (indent: Nat) (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace)
    (clear: printer.suffixes.isEmpty = True)
    (lays: SoftPuts indent place trace next):
    next place trace :=
  match place, agrees, lays with
    | AtStart at, _, never => (Bool.falseNotTrue never).impossible
    | Broken at, _, never => (Bool.falseNotTrue never).impossible
    | Mid at, _, Both same _ => same
    | Held at, agrees, _ =>
      Void.impossible (Bool.falseNotTrue (Eq.trans (Eq.flipped (agreesClear printer (Held at) trace agrees)) clear))

--| A line start at a line's start changes nothing.
theorem lineStartSame ∀ (printer: Printer) (indent: Nat)
    (start: printer.atLineStart = True):
    printer.lineStart indent = printer :=
  match at: printer.atLineStart, start with | True, _ => byComputing

--| A line start after text breaks the line at the continuation indentation.
theorem lineStartBreaks ∀ (printer: Printer) (indent: Nat)
    (start: printer.atLineStart = False):
    printer.lineStart indent = printer.newline (printer.continuation indent) :=
  match at: printer.atLineStart, start with | False, _ => byComputing

--| A line start leaves the printer at a place that satisfies what follows.
theorem lineStartStays ∀ (next: Place → List Event → Prop) (printer: Printer) (indent: Nat)
    (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace)
    (lays: StartPuts indent place trace next):
    Stays next (printer.lineStart indent) :=
  match place, agrees, lays with
    | AtStart at, agrees, lays =>
      rewrite lineStartSame printer indent (agreesStart printer (AtStart at) trace agrees) then
        ((AtStart at), trace, agrees, lays)
    | Broken at, agrees, lays =>
      rewrite lineStartSame printer indent (agreesStart printer (Broken at) trace agrees) then
        ((AtStart at), trace, (brokenStart printer at trace agrees), lays)
    | Mid at, agrees, lays =>
      rewrite lineStartBreaks printer indent (agreesStart printer (Mid at) trace agrees) then
        breakStays next printer indent (Mid at) trace agrees byComputing lays
    | Held at, agrees, lays =>
      rewrite lineStartBreaks printer indent (agreesStart printer (Held at) trace agrees) then
        breakStays next printer indent (Held at) trace agrees byComputing lays

--| Indentation set at the start of a line.
theorem hereAgrees ∀ (printer: Printer) (indent: Nat) (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace)
    (start: printer.atLineStart = True):
    Agrees { printer | owed = Some indent, lineIndent = indent } (AtStart indent) trace :=
  match place, agrees with
    | AtStart at, Both _ (Both none (Both blank (Both empty (Both _ (Both _ events))))) =>
      (start, none, blank, empty, byComputing, byComputing, events)
    | Broken at, Both _ (Both none (Both blank (Both empty (Both _ (Both _ (Both events _)))))) =>
      (start, none, blank, empty, byComputing, byComputing, events)
    | Mid at, Both other _ => Void.impossible (Bool.falseNotTrue (Eq.trans other.flipped start))
    | Held at, Both other _ => Void.impossible (Bool.falseNotTrue (Eq.trans other.flipped start))

--| A blank line after text, not at a line start, changes nothing.
theorem blankSame ∀ (printer: Printer) (start: printer.atLineStart = False): printer.blank = printer :=
  match at: printer.atLineStart, start with | False, _ => byComputing

--| One line break behind it and something printed, the printer adds the
--| line break that leaves a blank line.
theorem blankAdds ∀ (printer: Printer)
    (start: printer.atLineStart = True)
    (started: printer.started = True)
    (one: printer.newlinesAtEnd = 1):
    printer.blank = { printer | out = ["\n", ..printer.out], newlinesAtEnd = printer.newlinesAtEnd + 1 } :=
  match at: printer.atLineStart, begun: printer.started, start, started with | True, True, _, _ => rewrite one

--| A `Blank` leaves a blank line right after a line of words, and
--| nothing after words.
theorem blankStays ∀ (next: Place → List Event → Prop) (printer: Printer) (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace)
    (lays: BlankPuts place trace next):
    Stays next printer.blank :=
  match place, agrees, lays with
    | AtStart at, _, never => (Bool.falseNotTrue never).impossible
    | Broken at, Both start
        (Both none (Both blank (Both empty (Both owes (Both indent (Both events (Both started one))))))), lays =>
      rewrite blankAdds printer start started one then
        (
          (AtStart at),
          (trace ++ [Event.blankLine]),
          ((
            start,
            none,
            byComputing,
            byComputing,
            owes,
            indent,
            (Eq.trans
              (Eq.cong ((before: List Event) => before ++ [Event.blankLine]) events)
              (eventsBlank printer.out blank).flipped)
          )),
          lays
        )
    | Mid at, agrees, lays =>
      rewrite blankSame printer (agreesStart printer (Mid at) trace agrees) then ((Mid at), trace, agrees, lays)
    | Held at, agrees, lays =>
      rewrite blankSame printer (agreesStart printer (Held at) trace agrees) then ((Held at), trace, agrees, lays)

--| A trailing comment starts waiting, already in the trace.
theorem suffixStays ∀ (next: Place → List Event → Prop) (printer: Printer) (comment: Text)
    (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace)
    (word: isLayout comment = False)
    (lays: SuffixPuts comment place trace next):
    Stays next { printer | suffixes = printer.suffixes ++ [comment] } :=
  match place, agrees, lays with
    | AtStart at, _, never => (Bool.falseNotTrue never).impossible
    | Broken at, _, never => (Bool.falseNotTrue never).impossible
    | Held at, _, never => (Bool.falseNotTrue never).impossible
    | Mid at, Both start (Both none (Both blank (Both owes (Both indent (Both events _))))), lays =>
      let one: printer.suffixes ++ [comment] = [comment] := rewrite none
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

--| A step that goes one way or the other leaves the printer at a place that
--| satisfies what follows if each way does.
theorem eitherStays ∀ (spec: Place → List Event → Prop) (flat clear: Bool) (yes no: Printer) (rest: List Cmd)
    (whenYes: clear = True → Stays (place trace => StackPuts spec rest place trace) yes)
    (whenNo: Stays (place trace => StackPuts spec rest place trace) no):
    Stays
      (place trace => StackPuts spec (if flat && clear then (yes, rest) else (no, rest)).snd place trace)
      (if flat && clear then (yes, rest) else (no, rest)).fst :=
  match flat, clear, whenYes with
    | True, True, whenYes => whenYes byComputing
    | True, False, _ => whenNo
    | False, True, _ => whenNo
    | False, False, _ => whenNo

--| A step of a reading keeps the printer where the work list said, and
--| the work list it leaves lays from there.
theorem stepPuts ∀ (spec: Place → List Event → Prop) (printer: Printer) (cmd: Cmd) (rest: List Cmd)
    (result: (Printer, List Cmd)) (place: Place) (trace: List Event)
    (steps: StepsTo printer cmd rest result)
    (agrees: Agrees printer place trace)
    (lays: StackPuts spec [cmd, ..rest] place trace):
    Stays (after later => StackPuts spec result.snd after later) result.fst :=
  match cmd, steps, lays with
    | FillSep indent item, Inl (Both clear flat), lays =>
      rewrite flat then
        sepSpace
          (middle between => Puts item indent middle between (after later => StackPuts spec rest after later))
          printer
          indent
          place
          trace
          agrees
          clear
          lays
    | FillSep indent item, Inr broken, lays =>
      rewrite broken then
        newlineStays
          (middle between => Puts item indent middle between (after later => StackPuts spec rest after later))
          printer
          indent
          place
          trace
          agrees
          (sepMid
            (middle between => Puts item indent middle between (after later => StackPuts spec rest after later))
            indent
            place
            trace
            lays)
          (sepBroken
            (middle between => Puts item indent middle between (after later => StackPuts spec rest after later))
            indent
            place
            trace
            lays)
    | Print indent mode doc, steps, lays =>
      match doc, steps, lays with
        | Empty, steps, lays => rewrite steps then (place, trace, agrees, lays)
        | BreakParent, steps, lays => rewrite steps then (place, trace, agrees, lays)
        | Chunk text width, steps, lays =>
          rewrite steps then
            writeStays
              (after later => StackPuts spec rest after later)
              printer
              indent
              text
              width
              place
              trace
              agrees
              lays
        | Closing text, steps, lays =>
          rewrite steps then
            closeStays (after later => StackPuts spec rest after later) printer indent text place trace agrees lays
        | Line, steps, lays =>
          rewrite steps then
            eitherStays spec mode.isFlat printer.suffixes.isEmpty
              (printer.write indent " " 1)
              (printer.newline indent)
              rest
              (clear =>
                sepSpace (after later => StackPuts spec rest after later) printer indent place trace agrees clear lays)
              (newlineStays
                (after later => StackPuts spec rest after later)
                printer
                indent
                place
                trace
                agrees
                (sepMid (after later => StackPuts spec rest after later) indent place trace lays)
                (sepBroken (after later => StackPuts spec rest after later) indent place trace lays))
        | SoftLine, steps, lays =>
          rewrite steps then
            eitherStays spec mode.isFlat printer.suffixes.isEmpty printer
              (printer.newline indent)
              rest
              (clear =>
                (
                  place,
                  trace,
                  agrees,
                  (softSame
                    (after later => StackPuts spec rest after later)
                    printer
                    indent
                    place
                    trace
                    agrees
                    clear
                    lays)
                ))
              (newlineStays
                (after later => StackPuts spec rest after later)
                printer
                indent
                place
                trace
                agrees
                (softMid (after later => StackPuts spec rest after later) indent place trace lays)
                (softBroken (after later => StackPuts spec rest after later) indent place trace lays))
        | HardLine, steps, Both mid (Inl broken) =>
          rewrite steps then ((Broken indent), trace, (newlineBroken printer indent place trace agrees mid), broken)
        | HardLine, steps, Both mid (Inr started) =>
          rewrite steps then
            newlineStays (after later => StackPuts spec rest after later) printer indent place trace agrees mid started
        | CommentEnd, steps, Both mid lays =>
          let same: StackPuts spec rest (AtStart printer.lineIndent) trace :=
            rewrite agreesIndent printer place trace agrees then lays
          rewrite steps then
            newlineStays
              (after later => StackPuts spec rest after later)
              printer
              printer.lineIndent
              place
              trace
              agrees
              mid
              same
        | LineStart, steps, lays =>
          rewrite steps then
            lineStartStays (after later => StackPuts spec rest after later) printer indent place trace agrees lays
        | LineStartHere, steps, lays =>
          match start: printer.atLineStart with
            | True =>
              rewrite steps then ((AtStart indent), trace, (hereAgrees printer indent place trace agrees start), lays)
            | False =>
              rewrite steps then
                newlineStays
                  (after later => StackPuts spec rest after later)
                  printer
                  indent
                  place
                  trace
                  agrees
                  (startMid printer place trace agrees start)
                  lays
        | Blank, steps, lays =>
          rewrite steps then blankStays (after later => StackPuts spec rest after later) printer place trace agrees lays
        | Nest more inner, steps, lays => rewrite steps then (place, trace, agrees, lays)
        | Align inner, steps, lays =>
          rewrite steps then
            (
              place,
              trace,
              agrees,
              (alignHere printer indent place trace (column => Puts inner column place trace _) agrees lays)
            )
        | AlignInset inner, steps, lays =>
          rewrite steps then
            (
              place,
              trace,
              agrees,
              (alignHere printer (indent + 2) place trace (column => Puts inner column place trace _) agrees lays)
            )
        | Displaced inner, steps, lays =>
          rewrite steps then
            displacedStays printer indent place trace
              (column start later => Puts inner column start later (after more => StackPuts spec rest after more))
              agrees
              lays
        | OneLineBelow inner, steps, Both mid lays => rewrite steps then (place, trace, agrees, mid, (Inr lays))
        | Flatten inner, steps, lays => rewrite steps then (place, trace, agrees, lays)
        | LineSuffix comment, steps, Both word lays =>
          rewrite steps then
            suffixStays (after later => StackPuts spec rest after later) printer comment place trace agrees word lays
        | Group inner hard, Inl (Both _ flat), lays => rewrite flat then (place, trace, agrees, lays)
        | NarrowGroup max inner hard, Inl (Both _ flat), lays => rewrite flat then (place, trace, agrees, lays)
        | Group inner hard, Inr (Both _ broken), lays => rewrite broken then (place, trace, agrees, lays)
        | NarrowGroup max inner hard, Inr (Both _ broken), lays => rewrite broken then (place, trace, agrees, lays)
        | IdGroup id inner hard, Inl (Both _ flat), lays => rewrite flat then (place, trace, agrees, lays)
        | IdGroup id inner hard, Inr (Both _ broken), lays => rewrite broken then (place, trace, agrees, lays)
        | IfBroken id broken flat, steps, lays =>
          rewrite steps then (place, trace, agrees, (pickPuts printer.modes id broken flat indent place trace _ lays))
        | Concat docs, steps, lays =>
          rewrite steps then (place, trace, agrees, (printsPut spec indent mode docs rest place trace lays))
        | Fill [], steps, lays => rewrite steps then (place, trace, agrees, lays)
        | Fill [first, ..others], Inl (Both _ flat), lays =>
          rewrite flat then
            (
              place,
              trace,
              agrees,
              (printsPut spec indent Flat
                (Doc.joinLines [first, ..others])
                rest
                place
                trace
                (linesPut first others indent place trace (after later => StackPuts spec rest after later) lays))
            )
        | Fill [first, ..others], Inr (Both _ (Witness firstMode broken)), lays =>
          rewrite broken then
            (
              place,
              trace,
              agrees,
              (putsWeaker first indent place trace
                (after later => SepsPut others indent after later (final last => StackPuts spec rest final last))
                (after later => StackPuts spec (others.map (FillSep indent) ++ rest) after later)
                (after later seps => fillSepsPut spec indent others rest after later seps)
                lays)
            )
        | Choice options, Inl (Both _ flat), lays =>
          rewrite flat then
            (
              place,
              trace,
              agrees,
              (headOrPuts options indent place trace (after later => StackPuts spec rest after later) lays)
            )
        | Choice options, Inr (Both _ (Witness chosen (Both isOption broken))), lays =>
          rewrite broken then
            (
              place,
              trace,
              agrees,
              (optionPuts chosen options indent place trace
                (after later => StackPuts spec rest after later)
                isOption
                lays)
            )

--| The branch an `IfBroken` takes puts its words as both do.
theorem pickPuts ∀ (modes: List (Nat, Mode)) (id: Nat) (broken flat: Doc) (indent: Nat) (place: Place)
    (trace: List Event) (next: Place → List Event → Prop)
    (puts: Puts (IfBroken id broken flat) indent place trace next):
    Puts (pickBranch modes id broken flat) indent place trace next :=
  match pickEither modes id broken flat, puts with
    | Inl isBroken, Both brokenPuts _ => rewrite isBroken then brokenPuts
    | Inr isFlat, Both _ flatPuts => rewrite isFlat then flatPuts

--| An `Align` at a line start indents its line breaks to `atStart`.
theorem alignAtStart ∀ (printer: Printer) (atStart: Nat)
    (start: printer.atLineStart = True):
    printer.alignAt atStart = atStart :=
  match at: printer.atLineStart, start with | True, _ => byComputing

--| An `Align`'s contents hold at the indentation the printer gives them.
theorem alignHere ∀ (printer: Printer) (atStart: Nat) (place: Place) (trace: List Event) (inner: Nat → Prop)
    (agrees: Agrees printer place trace)
    (holds: AlignHolds atStart place inner):
    inner (printer.alignAt atStart) :=
  match place, agrees, holds with
    | AtStart at, agrees, holds =>
      rewrite alignAtStart printer atStart (agreesStart printer (AtStart at) trace agrees) then holds
    | Broken at, agrees, holds =>
      rewrite alignAtStart printer atStart (agreesStart printer (Broken at) trace agrees) then holds
    | Mid at, _, holds => holds (printer.alignAt atStart)
    | Held at, _, holds => holds (printer.alignAt atStart)

--| With no comment waiting, a `Displaced` element changes nothing before
--| it.
theorem displaceClear ∀ (printer: Printer) (indent: Nat)
    (clear: printer.suffixes.isEmpty = True):
    printer.displace indent = printer :=
  match empty: printer.suffixes.isEmpty, clear with | True, _ => byComputing

--| A `Displaced` element after a waiting comment starts a line first.
theorem displaceWaiting ∀ (printer: Printer) (indent: Nat)
    (waiting: printer.suffixes.isEmpty = False):
    printer.displace indent = printer.lineStart indent :=
  match empty: printer.suffixes.isEmpty, waiting with | False, _ => byComputing

--| At a line start, a `Displaced` element's line breaks go to the line's
--| indentation, if deeper.
theorem displacedAtStart ∀ (printer: Printer) (indent at: Nat)
    (start: printer.atLineStart = True)
    (owes: printer.owed.getOrElse 0 = at):
    printer.displacedAt indent = Nat.max indent at :=
  match on: printer.atLineStart, start with | True, _ => rewrite owes

--| After words, with no comment waiting, a `Displaced` element's line
--| breaks go to the construct's indentation.
theorem displacedAtMid ∀ (printer: Printer) (indent: Nat)
    (start: printer.atLineStart = False)
    (clear: printer.suffixes.isEmpty = True):
    printer.displacedAt indent = indent :=
  match on: printer.atLineStart, start with
    | False, _ =>
      match empty: printer.suffixes.isEmpty, clear with
        | True, _ => byComputing

--| After a waiting comment, a `Displaced` element's line breaks go to the
--| comment break's indentation.
theorem displacedAtHeld ∀ (printer: Printer) (indent: Nat)
    (start: printer.atLineStart = False)
    (waiting: printer.suffixes.isEmpty = False):
    printer.displacedAt indent = printer.continuation indent :=
  match on: printer.atLineStart, start with
    | False, _ =>
      match empty: printer.suffixes.isEmpty, waiting with
        | False, _ => byComputing

--| A `Displaced` element leaves the printer where its contents start, as
--| `DisplacedHolds` says.
theorem displacedStays ∀ (printer: Printer) (indent: Nat) (place: Place)
    (trace: List Event) (put: Nat → Place → List Event → Prop)
    (agrees: Agrees printer place trace)
    (holds: DisplacedHolds indent place (column start => put column start trace)):
    Stays (put (printer.displacedAt indent)) (printer.displace indent) :=
  match place, agrees, holds with
    | AtStart at, agrees, holds =>
      let start := agreesStart printer (AtStart at) trace agrees
      let clear := agreesClear printer (AtStart at) trace agrees
      match agrees with
        | Both _ (Both _ (Both _ (Both _ (Both owes _)))) =>
          rewrite displaceClear printer indent clear, (displacedAtStart printer indent at start owes) then
            ((AtStart at), trace, agrees, holds)
    | Broken at, agrees, holds =>
      let start := agreesStart printer (Broken at) trace agrees
      let clear := agreesClear printer (Broken at) trace agrees
      match agrees with
        | Both _ (Both _ (Both _ (Both _ (Both owes _)))) =>
          rewrite displaceClear printer indent clear, (displacedAtStart printer indent at start owes) then
            ((Broken at), trace, agrees, holds)
    | Mid at, agrees, holds =>
      let start := agreesStart printer (Mid at) trace agrees
      let clear := agreesClear printer (Mid at) trace agrees
      rewrite displaceClear printer indent clear, displacedAtMid printer indent start clear then
        ((Mid at), trace, agrees, holds)
    | Held at, agrees, holds =>
      let start := agreesStart printer (Held at) trace agrees
      let waiting := agreesClear printer (Held at) trace agrees
      let deeper: put (printer.continuation indent) (AtStart (Nat.max indent (at + 2))) trace :=
        rewrite agreesIndent printer (Held at) trace agrees then holds
      rewrite displaceWaiting printer indent waiting,
          lineStartBreaks printer indent start,
          displacedAtHeld printer indent start waiting then
        breakStays (put (printer.continuation indent)) printer indent (Held at) trace agrees byComputing deeper

--| A reading that has the steps to finish its work list ends where the
--| work list's last document leaves it, at a place and trace `spec`
--| holds of.
theorem readingPuts ∀ (spec: Place → List Event → Prop) (printer: Printer) (fuel: Nat) (stack: List Cmd)
    (final: Printer) (place: Place) (trace: List Event)
    (reads: Reads printer fuel stack final)
    (agrees: Agrees printer place trace)
    (lays: StackPuts spec stack place trace)
    (enough: stackCost stack ≤ fuel):
    Stays spec final :=
  match fuel, stack, reads, lays with
    | Zero, [], reads, lays => (place, trace, (rewrite reads then agrees), lays)
    | Succ more, [], reads, lays => (place, trace, (rewrite reads then agrees), lays)
    | Zero, [cmd, ..rest], _, _ =>
      let positive := costPositive cmd
      Void.impossible (arithmetic)
    | Succ more, [cmd, ..rest], Witness next (Witness later (Both steps laterReads)), lays =>
      let lighter := readingLighter printer cmd rest (next, later) steps
      match stepPuts spec printer cmd rest (next, later) place trace steps agrees lays with
        | Witness after (Witness written (Both nextAgrees nextPuts)) =>
          readingPuts spec next more later final after written laterReads nextAgrees nextPuts (arithmetic)

--| Writing the comment that still waits at the end adds no word the
--| trace doesn't have.
theorem flushAgrees ∀ (printer: Printer) (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace):
    trace = eventsOf printer.flushSuffixes.out :=
  match printer, place, agrees with
    | { width = total, out, column, owed, atLineStart, suffixes, lineIndent, newlinesAtEnd, started, modes }, AtStart
          at, Both _ (Both none (Both _ (Both _ (Both _ (Both _ events))))) => rewrite none then events
    | { width = total, out, column, owed, atLineStart, suffixes, lineIndent, newlinesAtEnd, started, modes }, Broken
          at, Both _ (Both none (Both _ (Both _ (Both _ (Both _ (Both events _)))))) => rewrite none then events
    | { width = total, out, column, owed, atLineStart, suffixes, lineIndent, newlinesAtEnd, started, modes }, Mid
          at, Both _ (Both none (Both _ (Both _ (Both _ (Both events _))))) => rewrite none then events
    | { width = total, out, column, owed, atLineStart, suffixes, lineIndent, newlinesAtEnd, started, modes }, Held
          at, Both start (Both (Witness comment (Both one (Both word events))) (Both blank _)) =>
      let written: eventsOf [comment, " ", ..out] = eventsOf out ++ [{ word = comment, start = None }] :=
        rewrite eventsWord comment [" ", ..out] word, blank
      rewrite one, start then Eq.trans events written.flipped

--| The pieces `print` joins, in the order printed.
def printedPieces (doc: Doc) (width: Nat): List Text :=
  ((Printer.start width).run (3 * doc.size + 3) (3 * doc.size + 3) [Print 0 Break doc] |> .flushSuffixes).out.reverse

--| `print` is the printer's pieces joined.
theorem printIsPieces ∀ (doc: Doc) (width: Nat): print doc width = (printedPieces doc width).joinWith "" := byComputing

--| A document that lays from the start of an unindented line, printed at
--| any width, puts each word where the document said: `spec` holds of the
--| words of the printed pieces in order, each with the column it starts
--| its line at, if it does.
theorem printPuts ∀ (spec: Place → List Event → Prop) (doc: Doc) (width: Nat)
    (lays: Puts doc 0 (AtStart 0) [] spec):
    ∃ (place: Place) => spec place (eventsOf (printedPieces doc width).reverse) :=
  let fuel := 3 * doc.size + 3
  let ran := (Printer.start width).run fuel fuel [Print 0 Break doc]
  let bound := stepsUnderSize doc
  let start: Agrees (Printer.start width) (AtStart 0) [] :=
    (byComputing, byComputing, byComputing, byComputing, byComputing, byComputing, byComputing)
  match readingPuts spec
    (Printer.start width)
    fuel
    [Print 0 Break doc]
    ran
    (AtStart 0)
    []
    (runIsReading (Printer.start width) fuel fuel [Print 0 Break doc])
    start
    lays
    (arithmetic) with
    | (place, trace, agrees, holds) =>
      (place, (rewrite List.reverseReverse ran.flushSuffixes.out, <- flushAgrees ran place trace agrees then holds))

--| `Puts` computes, and can be met: `f`, then `x` on a line of its own
--| two columns in, at every width.
theorem printPutsExample ∀ (width: Nat):
    ∃ (place: Place) => eventsOf
      (printedPieces (Concat [Chunk "f" 1, Nest 2 (Concat [HardLine, Chunk "x" 1])]) width).reverse
      = [{ word = "f", start = Some 0 }, { word = "x", start = Some 2 }] :=
  printPuts
    (place trace => trace = [{ word = "f", start = Some 0 }, { word = "x", start = Some 2 }])
    (Concat [Chunk "f" 1, Nest 2 (Concat [HardLine, Chunk "x" 1])])
    width
    ((byComputing, byComputing, (Inr ((byComputing, byComputing)))))

--| A closer after a trailing comment is printed before it: `x) -- c` at
--| every width, the comment last in the trace.
theorem closerPutsExample ∀ (width: Nat):
    ∃ (place: Place) => eventsOf (printedPieces (Concat [Chunk "x" 1, LineSuffix "-- c", Closing ")"]) width).reverse
      = [{ word = "x", start = Some 0 }, { word = ")", start = None }, { word = "-- c", start = None }] :=
  printPuts
    (place trace =>
      trace = [{ word = "x", start = Some 0 }, { word = ")", start = None }, { word = "-- c", start = None }])
    (Concat [Chunk "x" 1, LineSuffix "-- c", Closing ")"])
    width
    ((byComputing, byComputing, byComputing, byComputing))

--| `putMid`'s and `putSpaces`' hypothesis can be met: after `f` at the
--| start, the printer is in the middle of an unindented line.
theorem midExample: Agrees ((Printer.start 80).put "f" 1) (Mid 0) [{ word = "f", start = Some 0 }] :=
  putStart
    (Printer.start 80)
    "f"
    1
    0
    []
    ((byComputing, byComputing, byComputing, byComputing, byComputing, byComputing, byComputing))
    byComputing

--| An instance of `putMid` with all its hypotheses met, so it isn't
--| vacuous: `g` after `f` doesn't start the line. The audit's random search
--| can't find one, since a random printer almost never agrees with a trace.
theorem putMidExample: Agrees (((Printer.start 80).put "f" 1).put "g" 1) (Mid 0) [
      { word = "f", start = Some 0 },
      { word = "g", start = None }
    ] :=
  putMid ((Printer.start 80).put "f" 1) "g" 1 0 [{ word = "f", start = Some 0 }] midExample byComputing

--| An instance of `putSpaces` with all its hypotheses met, as for
--| `putMidExample`: a space after `f` leaves the trace alone.
theorem putSpacesExample: Agrees (((Printer.start 80).put "f" 1).put " " 1) (Mid 0) [{ word = "f", start = Some 0 }] :=
  putSpaces ((Printer.start 80).put "f" 1) " " 1 0 [{ word = "f", start = Some 0 }] midExample byComputing
