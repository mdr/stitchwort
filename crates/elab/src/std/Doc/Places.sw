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

import Doc (..)
import Bool (not)
import Doc.Proofs (..)

--| Whether the last line of the output (its pieces the last first) has
--| nothing but spaces on it.
def Doc.Proofs.lineBlank: List Text → Bool
  | [] => True
  | [piece, ..earlier] => if piece.all (char => char == ' ') then lineBlank earlier else piece == "\n"

--| A word as printed: `start` is the column it starts its line at, or
--| `None` if other words come before it on the line. A blank line is an
--| event too (`Event.blankLine`).
type Doc.Proofs.Event = { word: Text, start: Option Nat }

--| A blank line: the line break that ends a line with nothing but spaces
--| on it. No word is `"\n"`, so no word's event is this one.
def Doc.Proofs.Event.blankLine: Event := { word = "\n", start = None }

--| The words of the output (its pieces the last first), in the order
--| printed, each with where it starts its line, and its blank lines: a
--| line break on a line with nothing but spaces is one, as it is to the
--| lexer (the toy formatter's `placePiece`).
def Doc.Proofs.eventsOf: List Text → List Event
  | [] => []
  | [piece, ..earlier] =>
    if isLayout piece then
      if piece == "\n" && lineBlank earlier then eventsOf earlier ++ [Event.blankLine] else eventsOf earlier
    else eventsOf earlier ++ [{ word = piece, start = if lineBlank earlier then Some (lineWidth earlier) else None }]

--| Where the printer is on its line. Each place has what the printer
--| carries from line to line (`Printer.carry`): the comment floor in
--| force (after a comment break before an own-line comment, the least
--| indentation of the lines up to the next code) and the open marks.
type Doc.Proofs.Place =
  --| Nothing but indentation on the line; the next word starts it at
  --| column `indent`. A `Blank` here may print nothing (at the start of
  --| the output, after a blank line), so none is allowed.
  | AtStart (indent: Nat) (carry: Carry)
  --| As `AtStart`, right after the line break that ended a line of
  --| words: the one place a `Blank` leaves a blank line.
  | Broken (indent: Nat) (carry: Carry)
  --| Words on the line, which is indented `indent`.
  | Mid (indent: Nat) (carry: Carry)
  --| As `Mid`, with a trailing comment waiting for the end of the line.
  | Held (indent: Nat) (carry: Carry)

--| A chunk in a construct indented `indent`: nothing if empty; spaces
--| after words (never at a line start, where they would move the next
--| word); a word where the place says, on a new line after a waiting
--| comment.
def Doc.Proofs.WritePuts (indent: Nat) (text: Text) (place: Place)
    (trace: List Event) (next: Place → List Event → Prop):
    Prop :=
  if text.isEmpty then next place trace
  else if text.all (char => char == ' ') then
    match place with
      | AtStart _ _ | Broken _ _ => False
      | Mid at carry => next (Mid at (floorAfter text carry)) trace
      | Held at carry => next (Held at carry) trace
  else
    (text == "\n") = False
      ∧ (match place with
        | AtStart at carry | Broken at carry =>
          next (Mid at (floorAfter text carry)) (trace ++ [{ word = text, start = Some at }])
        | Mid at carry => next (Mid at (floorAfter text carry)) (trace ++ [{ word = text, start = None }])
        | Held at carry =>
          let broken := floored carry (Nat.max indent (at + 2))
          next
            (Mid broken (floorAfter text (carry.breakTo (Nat.max indent (at + 2)))))
            (trace ++ [{ word = text, start = Some broken }]))

--| `event` put before the last of `trace`. Where a comment waits, it is
--| the trace's last event already, and a closer written then is printed
--| before it.
def Doc.Proofs.tucked (event: Event): List Event → List Event
  | [] => [event]
  | [last] => [event, last]
  | [first, ..rest] => [first, ..tucked event rest]

--| A closer in a construct indented `indent`: a chunk where no comment
--| waits; where one waits, a word on the comment's line, before it.
def Doc.Proofs.ClosePuts (indent: Nat) (text: Text) (place: Place)
    (trace: List Event) (next: Place → List Event → Prop):
    Prop :=
  match place with
    | Held at carry =>
      isLayout text = False ∧ next (Held at (floorAfter text carry)) (tucked { word = text, start = None } trace)
    | _ => WritePuts indent text place trace next

--| Whether words are on the line: a line break here ends their line, and
--| leaves no blank line.
def Doc.Proofs.Place.midLine: Place → Bool
  | AtStart _ _ | Broken _ _ => False
  | Mid _ _ | Held _ _ => True

--| A `Line` or a fill's separator: a space or a line break, after words.
--| After a waiting comment the space is held, so the place stays.
def Doc.Proofs.SepPuts (indent: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop): Prop :=
  match place with
    | AtStart _ _ | Broken _ _ => False
    | Mid at carry =>
      next (Mid at { carry | floor = None }) trace ∧ next (Broken (floored carry indent) (carry.breakTo indent)) trace
    | Held at carry => next (Held at carry) trace ∧ next (Broken (floored carry indent) (carry.breakTo indent)) trace

--| A `SoftLine`: nothing or a line break, after words.
def Doc.Proofs.SoftPuts (indent: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop): Prop :=
  match place with
    | AtStart _ _ | Broken _ _ => False
    | Mid at carry => next (Mid at carry) trace ∧ next (Broken (floored carry indent) (carry.breakTo indent)) trace
    | Held at carry => next (Held at carry) trace ∧ next (Broken (floored carry indent) (carry.breakTo indent)) trace

--| A `LineStart`: a comment break, deeper than the line, unless a line
--| starts here; the break's indentation is the floor until the next
--| code.
def Doc.Proofs.StartPuts (indent: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop): Prop :=
  match place with
    | AtStart at carry => next (AtStart at carry) trace
    | Broken at carry => next (Broken at carry) trace
    | Mid at carry | Held at carry =>
      let broken := Nat.max indent (at + 2)
      next (Broken (floored carry broken) (carry.startFloor broken)) trace

--| A `LineStartHere`: at a line start the line moves to `indent`;
--| after words, a line break there.
def Doc.Proofs.HerePuts (indent: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop): Prop :=
  match place with
    | AtStart _ carry => next (AtStart indent carry) trace
    | Broken _ carry => next (Broken indent carry) trace
    | Mid _ carry | Held _ carry => next (Broken (floored carry indent) (carry.breakTo indent)) trace

--| The place, carrying `carry` instead of its own.
def Doc.Proofs.Place.withCarry (place: Place) (carry: Carry): Place := match place with
  | AtStart at _ => AtStart at carry
  | Broken at _ => Broken at carry
  | Mid at _ => Mid at carry
  | Held at _ => Held at carry

--| Where a `CloserLine` with this key in a construct indented `indent`
--| leaves the printer: at the start of the closer's line, where the open
--| marks put it (`Carry.closerAt`), with its mark closed and no comment
--| floor. After words that is a line break; at a line start (a break
--| before it ended the line already) the line moves there, still right
--| after a line break if it was.
def Doc.Proofs.Place.closerLine (place: Place) (key indent: Nat): Place :=
  let column := place.carry.closerAt key indent
  let carry := (place.carry.close key).breakTo column
  match place with
    | AtStart _ _ => AtStart column carry
    | _ => Broken column carry

--| A `CloserLine` in a construct indented `indent`: the closer's line,
--| after a line break or at the line start one left (`Place.closerLine`).
def Doc.Proofs.CloserPuts (key indent: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop):
    Prop :=
  next (place.closerLine key indent) trace

--| A trailing comment: after words on its line, with no other waiting.
def Doc.Proofs.SuffixPuts (comment: Text) (place: Place) (trace: List Event) (next: Place → List Event → Prop): Prop :=
  match place with
    | AtStart _ _ | Broken _ _ => False
    | Mid at carry => next (Held at carry) (trace ++ [{ word = comment, start = None }])
    | Held _ _ => False

--| A `Blank`: a blank line right after the line break that ended a line
--| of words; nothing after words; at no other line start, where the
--| printer may or may not leave one.
def Doc.Proofs.BlankPuts (place: Place) (trace: List Event) (next: Place → List Event → Prop): Prop := match place with
  | AtStart _ _ => False
  | Broken at carry => next (AtStart at carry) (trace ++ [Event.blankLine])
  | Mid at carry => next (Mid at carry) trace
  | Held at carry => next (Held at carry) trace

--| An `Align`'s contents, given the indentation of their line breaks:
--| `atStart` at a line start, otherwise the column the `Align` starts at,
--| which a place doesn't say, so they must do for every column.
def Doc.Proofs.AlignHolds (atStart: Nat) (place: Place) (inner: Nat → Prop): Prop := match place with
  | AtStart _ _ | Broken _ _ => inner atStart
  | Mid _ _ | Held _ _ => ∀ (column: Nat) => inner column

--| A `Displaced` element's contents in a construct indented `indent`,
--| given the indentation of their line breaks and where they start: at a
--| line start, the line's indentation if deeper; after words, the
--| construct's; after a waiting comment, a comment break's, on the line
--| it starts (at the floor, if deeper).
def Doc.Proofs.DisplacedHolds (indent: Nat) (place: Place) (inner: Nat → Place → Prop): Prop := match place with
  | AtStart at carry => inner (Nat.max indent at) (AtStart at carry)
  | Broken at carry => inner (Nat.max indent at) (Broken at carry)
  | Mid at carry => inner indent (Mid at carry)
  | Held at carry =>
    let broken := Nat.max indent (at + 2)
    inner broken (Broken (floored carry broken) (carry.breakTo broken))

--| From `place` with `trace` printed, every way `doc` may print in a
--| construct indented `indent` puts its words where `next` is told, and
--| every place it may leave satisfies `next`. A line break that isn't a
--| `Line` or `SoftLine` comes only after words (at a line start it would
--| leave a blank line). Every line break after words leaves `Broken`, as
--| the printer is then (one line break behind it), so a `Blank` may
--| follow; after a `HardLine` the document may say instead that none
--| does (`AtStart`).
def Doc.Proofs.Puts (doc: Doc) (indent: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop):
    Prop :=
  match doc with
    | Doc.Nothing | BreakParent => next place trace
    | Blank => BlankPuts place trace next
    | Chunk text _ => WritePuts indent text place trace next
    | Closing text => ClosePuts indent text place trace next
    | Line => SepPuts indent place trace next
    | SoftLine => SoftPuts indent place trace next
    | HardLine =>
      let broken := floored place.carry indent
      place.midLine = True
        ∧ (next (Broken broken (place.carry.breakTo indent)) trace
          ∨ next (AtStart broken (place.carry.breakTo indent)) trace)
    | LineStart => StartPuts indent place trace next
    | LineStartHere => HerePuts indent place trace next
    | Mark key => next (place.withCarry (place.carry.mark key place.indent)) trace
    | CloserLine key => CloserPuts key indent place trace next
    | Nest more inner => Puts inner (indent + more) place trace next
    | Align inner => AlignHolds indent place (column => Puts inner column place trace next)
    | AlignInset inner => AlignHolds (indent + 2) place (column => Puts inner column place trace next)
    | Displaced inner => DisplacedHolds indent place (column start => Puts inner column start trace next)
    | Group inner _ | NarrowGroup _ inner _ | IdGroup _ inner _ => Puts inner indent place trace next
    | IfBroken _ broken flat => Puts broken indent place trace next ∧ Puts flat indent place trace next
    | Flatten inner => Puts inner indent place trace next
    | OneLineBelow inner =>
      place.midLine = True
        ∧ Puts inner
          (indent + 2)
          (Broken (floored place.carry (indent + 2)) (place.carry.breakTo (indent + 2)))
          trace
          next
    | Concat docs => PutsAll docs indent place trace next
    | Fill items => FillPuts items indent place trace next
    | Choice options => OptionsPut options indent place trace next
    | LineSuffix comment => isLayout comment = False ∧ SuffixPuts comment place trace next

--| Each of the docs in turn puts its words, from the place and trace the one
--| before left.
def Doc.Proofs.PutsAll (docs: List Doc) (indent: Nat) (place: Place)
    (trace: List Event) (next: Place → List Event → Prop):
    Prop :=
  match docs with
    | [] => next place trace
    | [doc, ..rest] => Puts doc indent place trace (after later => PutsAll rest indent after later next)

--| The items of a fill put their words, each after a separator that is a space
--| or a line break.
def Doc.Proofs.FillPuts (items: List Doc) (indent: Nat) (place: Place)
    (trace: List Event) (next: Place → List Event → Prop):
    Prop :=
  match items with
    | [] => next place trace
    | [first, ..others] => Puts first indent place trace (after later => SepsPut others indent after later next)

--| The separators before the items of a fill, and the items, put their words in
--| turn.
def Doc.Proofs.SepsPut (items: List Doc) (indent: Nat) (place: Place)
    (trace: List Event) (next: Place → List Event → Prop):
    Prop :=
  match items with
    | [] => next place trace
    | [item, ..more] => SepPuts indent place trace (middle between =>
      Puts item indent middle between (after later => SepsPut more indent after later next))

--| Every option a choice may take puts its words.
def Doc.Proofs.OptionsPut (options: List Doc) (indent: Nat) (place: Place)
    (trace: List Event) (next: Place → List Event → Prop):
    Prop :=
  match options with
    | [] => next place trace
    | [last] => Puts last indent place trace next
    | [option, ..others] => Puts option indent place trace next ∧ OptionsPut others indent place trace next

--| The work list, from `place` to the end, where `spec` is asked of the
--| place and the whole trace.
def Doc.Proofs.StackPuts (spec: Place → List Event → Prop) (stack: List Cmd) (place: Place) (trace: List Event): Prop :=
  match stack with
    | [] => spec place trace
    | [Print indent _ doc, ..rest] => Puts doc indent place trace (after later => StackPuts spec rest after later)
    | [FillSep indent item, ..rest] => SepPuts indent place trace (middle between =>
      Puts item indent middle between (after later => StackPuts spec rest after later))

-- A weaker continuation still holds.

--| `WritePuts` holds with a weaker requirement on what follows, if it holds
--| with a stronger one.
theorem Doc.Proofs.writePutsWeaker ∀ (indent: Nat) (text: Text) (place: Place) (trace: List Event)
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
            | AtStart _ _ | Broken _ _, never => never
            | Mid _ _ | Held _ _, lays => implies _ _ lays
        | False, Both oneLine lays =>
          match place, lays with
            | AtStart _ _ | Broken _ _ | Mid _ _ | Held _ _, lays => (oneLine, (implies _ _ lays))

--| `ClosePuts` holds with a weaker requirement on what follows, if it holds
--| with a stronger one.
theorem Doc.Proofs.closePutsWeaker ∀ (indent: Nat) (text: Text) (place: Place) (trace: List Event)
    (strong weak: Place → List Event → Prop)
    (implies: ∀ (after: Place) (later: List Event) => strong after later → weak after later)
    (lays: ClosePuts indent text place trace strong):
    ClosePuts indent text place trace weak :=
  match place, lays with
    | Held at carry, (word, lays) => (word, (implies _ _ lays))
    | AtStart at carry, lays => writePutsWeaker indent text (AtStart at carry) trace strong weak implies lays
    | Broken at carry, lays => writePutsWeaker indent text (Broken at carry) trace strong weak implies lays
    | Mid at carry, lays => writePutsWeaker indent text (Mid at carry) trace strong weak implies lays

--| `SepPuts` holds with a weaker requirement on what follows, if it holds with
--| a stronger one.
theorem Doc.Proofs.sepPutsWeaker ∀ (indent: Nat) (place: Place) (trace: List Event)
    (strong weak: Place → List Event → Prop)
    (implies: ∀ (after: Place) (later: List Event) => strong after later → weak after later)
    (lays: SepPuts indent place trace strong):
    SepPuts indent place trace weak :=
  match place, lays with
    | AtStart _ _ | Broken _ _, never => never
    | Mid _ _ | Held _ _, Both same broken => ((implies _ _ same), (implies _ _ broken))

--| `SoftPuts` holds with a weaker requirement on what follows, if it holds with
--| a stronger one.
theorem Doc.Proofs.softPutsWeaker ∀ (indent: Nat) (place: Place) (trace: List Event)
    (strong weak: Place → List Event → Prop)
    (implies: ∀ (after: Place) (later: List Event) => strong after later → weak after later)
    (lays: SoftPuts indent place trace strong):
    SoftPuts indent place trace weak :=
  match place, lays with
    | AtStart _ _ | Broken _ _, never => never
    | Mid _ _ | Held _ _, Both same broken => ((implies _ _ same), (implies _ _ broken))

--| `StartPuts` holds with a weaker requirement on what follows, if it holds
--| with a stronger one.
theorem Doc.Proofs.startPutsWeaker ∀ (indent: Nat) (place: Place) (trace: List Event)
    (strong weak: Place → List Event → Prop)
    (implies: ∀ (after: Place) (later: List Event) => strong after later → weak after later)
    (lays: StartPuts indent place trace strong):
    StartPuts indent place trace weak :=
  match place, lays with | AtStart _ _ | Broken _ _ | Mid _ _ | Held _ _, lays => implies _ _ lays

--| `SuffixPuts` holds with a weaker requirement on what follows, if it holds
--| with a stronger one.
theorem Doc.Proofs.suffixPutsWeaker ∀ (comment: Text) (place: Place) (trace: List Event)
    (strong weak: Place → List Event → Prop)
    (implies: ∀ (after: Place) (later: List Event) => strong after later → weak after later)
    (lays: SuffixPuts comment place trace strong):
    SuffixPuts comment place trace weak :=
  match place, lays with
    | AtStart _ _ | Broken _ _, never => never
    | Mid at carry, lays => implies _ _ lays
    | Held at carry, never => never

--| `HerePuts` holds with a weaker requirement on what follows, if it holds
--| with a stronger one.
theorem Doc.Proofs.herePutsWeaker ∀ (indent: Nat) (place: Place) (trace: List Event)
    (strong weak: Place → List Event → Prop)
    (implies: ∀ (after: Place) (later: List Event) => strong after later → weak after later)
    (lays: HerePuts indent place trace strong):
    HerePuts indent place trace weak :=
  match place, lays with | AtStart _ _ | Broken _ _ | Mid _ _ | Held _ _, lays => implies _ _ lays

--| `BlankPuts` holds with a weaker requirement on what follows, if it holds
--| with a stronger one.
theorem Doc.Proofs.blankPutsWeaker ∀ (place: Place) (trace: List Event) (strong weak: Place → List Event → Prop)
    (implies: ∀ (after: Place) (later: List Event) => strong after later → weak after later)
    (lays: BlankPuts place trace strong):
    BlankPuts place trace weak :=
  match place, lays with
    | AtStart at carry, never => never
    | Broken _ _ | Mid _ _ | Held _ _, lays => implies _ _ lays

--| What holds with a continuation holds with any it implies.
theorem Doc.Proofs.putsWeaker ∀ (doc: Doc) (indent: Nat) (place: Place) (trace: List Event)
    (strong weak: Place → List Event → Prop)
    (implies: ∀ (after: Place) (later: List Event) => strong after later → weak after later)
    (lays: Puts doc indent place trace strong):
    Puts doc indent place trace weak :=
  match doc, lays with
    | Doc.Nothing | BreakParent, lays => implies _ _ lays
    | Blank, lays => blankPutsWeaker place trace strong weak implies lays
    | Chunk text width, lays => writePutsWeaker indent text place trace strong weak implies lays
    | Closing text, lays => closePutsWeaker indent text place trace strong weak implies lays
    | Line, lays => sepPutsWeaker indent place trace strong weak implies lays
    | SoftLine, lays => softPutsWeaker indent place trace strong weak implies lays
    | HardLine, Both mid (Inl broken) => (mid, (Inl (implies _ _ broken)))
    | HardLine, Both mid (Inr started) => (mid, (Inr (implies _ _ started)))
    | LineStart, lays => startPutsWeaker indent place trace strong weak implies lays
    | LineStartHere, lays => herePutsWeaker indent place trace strong weak implies lays
    | Mark _ | CloserLine _, lays => implies _ _ lays
    | Nest more inner, lays => putsWeaker inner (indent + more) place trace strong weak implies lays
    | Align inner, lays =>
      match place, lays with
        | AtStart at carry, lays => putsWeaker inner indent (AtStart at carry) trace strong weak implies lays
        | Broken at carry, lays => putsWeaker inner indent (Broken at carry) trace strong weak implies lays
        | Mid at carry, lays => column => putsWeaker inner column (Mid at carry) trace strong weak implies (lays column)
        | Held at carry, lays => column =>
          putsWeaker inner column (Held at carry) trace strong weak implies (lays column)
    | AlignInset inner, lays =>
      match place, lays with
        | AtStart at carry, lays => putsWeaker inner (indent + 2) (AtStart at carry) trace strong weak implies lays
        | Broken at carry, lays => putsWeaker inner (indent + 2) (Broken at carry) trace strong weak implies lays
        | Mid at carry, lays => column => putsWeaker inner column (Mid at carry) trace strong weak implies (lays column)
        | Held at carry, lays => column =>
          putsWeaker inner column (Held at carry) trace strong weak implies (lays column)
    | Displaced inner, lays =>
      match place, lays with
        | AtStart at carry, lays =>
          putsWeaker inner (Nat.max indent at) (AtStart at carry) trace strong weak implies lays
        | Broken at carry, lays => putsWeaker inner (Nat.max indent at) (Broken at carry) trace strong weak implies lays
        | Mid at carry, lays => putsWeaker inner indent (Mid at carry) trace strong weak implies lays
        | Held at carry, lays =>
          putsWeaker inner
            (Nat.max indent (at + 2))
            (Broken (floored carry (Nat.max indent (at + 2))) (carry.breakTo (Nat.max indent (at + 2))))
            trace
            strong
            weak
            implies
            lays
    | Group inner _ | NarrowGroup _ inner _ | IdGroup _ inner _, lays =>
      putsWeaker inner indent place trace strong weak implies lays
    | IfBroken id broken flat, Both brokenPuts flatPuts => (
      (putsWeaker broken indent place trace strong weak implies brokenPuts),
      (putsWeaker flat indent place trace strong weak implies flatPuts)
    )
    | Flatten inner, lays => putsWeaker inner indent place trace strong weak implies lays
    | OneLineBelow inner, Both mid lays => (
      mid,
      (putsWeaker inner
        (indent + 2)
        (Broken (floored place.carry (indent + 2)) (place.carry.breakTo (indent + 2)))
        trace
        strong
        weak
        implies
        lays)
    )
    | Concat docs, lays => allPutsWeaker docs indent place trace strong weak implies lays
    | Fill items, lays => fillPutsWeaker items indent place trace strong weak implies lays
    | Choice options, lays => optionsPutWeaker options indent place trace strong weak implies lays
    | LineSuffix comment, Both word lays => (word, (suffixPutsWeaker comment place trace strong weak implies lays))

--| `PutsAll` holds with a weaker requirement on what follows, if it holds with
--| a stronger one.
theorem Doc.Proofs.allPutsWeaker ∀ (docs: List Doc) (indent: Nat) (place: Place) (trace: List Event)
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
theorem Doc.Proofs.fillPutsWeaker ∀ (items: List Doc) (indent: Nat) (place: Place) (trace: List Event)
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
theorem Doc.Proofs.sepsPutWeaker ∀ (items: List Doc) (indent: Nat) (place: Place) (trace: List Event)
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
theorem Doc.Proofs.optionsPutWeaker ∀ (options: List Doc) (indent: Nat) (place: Place) (trace: List Event)
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
theorem Doc.Proofs.printsPut ∀ (spec: Place → List Event → Prop) (indent: Nat) (mode: Mode) (docs: List Doc)
    (rest: List Cmd) (place: Place) (trace: List Event)
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
theorem Doc.Proofs.linesPut ∀ (first: Doc) (others: List Doc) (indent: Nat) (place: Place)
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
theorem Doc.Proofs.fillSepsPut ∀ (spec: Place → List Event → Prop) (indent: Nat) (items: List Doc) (rest: List Cmd)
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
theorem Doc.Proofs.optionPuts ∀ (chosen: Doc) (options: List Doc) (indent: Nat) (place: Place)
    (trace: List Event) (next: Place → List Event → Prop)
    (isOption: IsOption chosen options)
    (lays: OptionsPut options indent place trace next):
    Puts chosen indent place trace next :=
  match options, isOption, lays with
    | [] | [_], picked, lays => rewrite picked then lays
    | [option, second, ..others], Inl picked, Both first _ => rewrite picked then first
    | [option, second, ..others], Inr later, Both _ rest =>
      optionPuts chosen [second, ..others] indent place trace next later rest

--| The first option of a choice puts its words as the options do.
theorem Doc.Proofs.headOrPuts ∀ (options: List Doc) (indent: Nat) (place: Place)
    (trace: List Event) (next: Place → List Event → Prop)
    (lays: OptionsPut options indent place trace next):
    Puts (options.headOr Doc.Nothing) indent place trace next :=
  match options, lays with
    | [] | [_], lays => lays
    | [option, second, ..others], Both first _ => first

-- The output's side: events, blank lines and widths, a piece at a time.

--| Spaces aren't a line break.
theorem Doc.Proofs.gapNoBreak ∀ (piece: Text) (gap: piece.all (char => char == ' ') = True): (piece == "\n") = False :=
  match isBreak: piece == "\n" with
    | False => byComputing
    | True =>
      let same: piece = "\n" := DecEq.sound isBreak
      let never: "\n".all (char => char == ' ') = True := rewrite <- same then gap
      match never with
        | ()

--| Spaces are layout.
theorem Doc.Proofs.gapLayout ∀ (piece: Text) (gap: piece.all (char => char == ' ') = True): isLayout piece = True :=
  Eq.cong ((spaces: Bool) => spaces || piece == "\n") gap

--| A word on top of the output is an event at its line's start, if only layout
--| is before it, else not at a line start.
theorem Doc.Proofs.eventsWord ∀ (piece: Text) (earlier: List Text)
    (word: isLayout piece = False):
    eventsOf [piece, ..earlier]
      = eventsOf earlier ++ [{ word = piece, start = if lineBlank earlier then Some (lineWidth earlier) else None }] :=
  match layout: isLayout piece, word with
    | False, _ => byComputing
    | True, never =>
      match never with
        | ()

--| Spaces are no event.
theorem Doc.Proofs.eventsGap ∀ (piece: Text) (earlier: List Text)
    (gap: piece.all (char => char == ' ') = True):
    eventsOf [piece, ..earlier] = eventsOf earlier :=
  rewrite gapLayout piece gap, gapNoBreak piece gap

--| The line break that ends a line of words is no event.
theorem Doc.Proofs.eventsBreak ∀ (earlier: List Text)
    (words: lineBlank earlier = False):
    eventsOf ["\n", ..earlier] = eventsOf earlier :=
  rewrite words

--| A line break on a line with nothing but spaces is a blank line.
theorem Doc.Proofs.eventsBlank ∀ (earlier: List Text)
    (blank: lineBlank earlier = True):
    eventsOf ["\n", ..earlier] = eventsOf earlier ++ [Event.blankLine] :=
  rewrite blank

--| A line with a word on it isn't blank.
theorem Doc.Proofs.blankWord ∀ (piece: Text) (earlier: List Text)
    (word: isLayout piece = False):
    lineBlank [piece, ..earlier] = False :=
  match gap: piece.all (char => char == ' '), word with
    | True, never => (Bool.falseNotTrue never.flipped).impossible
    | False, word => word

--| Spaces don't change whether a line is blank.
theorem Doc.Proofs.blankGap ∀ (piece: Text) (earlier: List Text)
    (gap: piece.all (char => char == ' ') = True):
    lineBlank [piece, ..earlier] = lineBlank earlier :=
  match spaces: piece.all (char => char == ' '), gap with
    | True, _ => byComputing
    | False, never =>
      match never with
        | ()

--| A piece that isn't a line break adds its length to the line's width.
theorem Doc.Proofs.widthPiece ∀ (piece: Text) (earlier: List Text)
    (oneLine: (piece == "\n") = False):
    lineWidth [piece, ..earlier] = piece.length + lineWidth earlier :=
  match isBreak: piece == "\n", oneLine with
    | False, _ => byComputing
    | True, never =>
      match never with
        | ()

--| A last piece that isn't only spaces is kept when spaces at the end are
--| dropped.
theorem Doc.Proofs.trimKeep ∀ (last: Text) (earlier: List Text)
    (word: last.all (char => char == ' ') = False):
    trimSpaces [last, ..earlier] = [last, ..earlier] :=
  match spaces: last.all (char => char == ' '), word with
    | False, _ => byComputing
    | True, never =>
      match never with
        | ()

--| A last piece of spaces is dropped with any spaces before it.
theorem Doc.Proofs.trimDrop ∀ (last: Text) (earlier: List Text)
    (gap: last.all (char => char == ' ') = True):
    trimSpaces [last, ..earlier] = trimSpaces earlier :=
  match spaces: last.all (char => char == ' '), gap with
    | True, _ => byComputing
    | False, never =>
      match never with
        | ()

--| Dropping the spaces at the end of the output leaves its events the same,
--| given the same for the earlier output.
theorem Doc.Proofs.trimEventsBy ∀ (last: Text) (earlier: List Text) (spaces: Bool)
    (is: last.all (char => char == ' ') = spaces)
    (rest: eventsOf (trimSpaces earlier) = eventsOf earlier):
    eventsOf (trimSpaces [last, ..earlier]) = eventsOf [last, ..earlier] :=
  match spaces, is with
    | True, gap => rewrite trimDrop last earlier gap then Eq.trans rest (eventsGap last earlier gap).flipped
    | False, word => rewrite trimKeep last earlier word

--| The spaces a line break drops are no words.
theorem Doc.Proofs.trimEvents ∀ (out: List Text): eventsOf (trimSpaces out) = eventsOf out := match out with
  | [] => byComputing
  | [last, ..earlier] => trimEventsBy last earlier _ byComputing (trimEvents earlier)

--| Dropping the spaces at the end of the output leaves a line's blankness the
--| same, given the same for the earlier output.
theorem Doc.Proofs.trimBlankBy ∀ (last: Text) (earlier: List Text) (spaces: Bool)
    (is: last.all (char => char == ' ') = spaces)
    (rest: lineBlank (trimSpaces earlier) = lineBlank earlier):
    lineBlank (trimSpaces [last, ..earlier]) = lineBlank [last, ..earlier] :=
  match spaces, is with
    | True, gap => rewrite trimDrop last earlier gap then Eq.trans rest (blankGap last earlier gap).flipped
    | False, word => rewrite trimKeep last earlier word

--| Dropping the spaces at the end of the output leaves a line's blankness the
--| same.
theorem Doc.Proofs.trimBlank ∀ (out: List Text): lineBlank (trimSpaces out) = lineBlank out := match out with
  | [] => byComputing
  | [last, ..earlier] => trimBlankBy last earlier _ byComputing (trimBlank earlier)

-- The printer's side: where it is agrees with its output.

--| The printer is at `place` with `trace` printed: a line start has
--| nothing but the indentation owed; a comment that waits is already in
--| the trace, after the words written. `newlines` is the printer's count
--| of the line breaks its output ends with, which `Blank` reads: none
--| after words, one at `Broken`. The carry (comment floor and
--| open marks) is the place's.
def Doc.Proofs.AgreesParts (out: List Text) (owed: Option Nat) (atLineStart: Bool) (suffixes: List Text)
    (lineIndent: Nat) (started: Bool) (newlines: Nat) (printerCarry: Carry) (place: Place) (trace: List Event):
    Prop :=
  match place with
    | AtStart at carry =>
      atLineStart = True
        ∧ suffixes = []
        ∧ lineBlank out = True
        ∧ lineWidth out = 0
        ∧ owed.getOrElse 0 = at
        ∧ lineIndent = at
        ∧ trace = eventsOf out
        ∧ printerCarry = carry
    | Broken at carry =>
      atLineStart = True
        ∧ suffixes = []
        ∧ lineBlank out = True
        ∧ lineWidth out = 0
        ∧ owed.getOrElse 0 = at
        ∧ lineIndent = at
        ∧ trace = eventsOf out
        ∧ started = True
        ∧ newlines = 1
        ∧ printerCarry = carry
    | Mid at carry =>
      atLineStart = False
        ∧ suffixes = []
        ∧ lineBlank out = False
        ∧ owed = None
        ∧ lineIndent = at
        ∧ trace = eventsOf out
        ∧ newlines = 0
        ∧ printerCarry = carry
    | Held at carry =>
      atLineStart = False
        ∧ (∃ (comment: Text) => suffixes = [comment]
          ∧ isLayout comment = False
          ∧ trace = eventsOf out ++ [{ word = comment, start = None }])
        ∧ lineBlank out = False
        ∧ owed = None
        ∧ lineIndent = at
        ∧ printerCarry = carry

--| The printer is at `place` with `trace` printed: its output, indentation owed,
--| waiting comments, comment floor and open marks are what the place
--| says.
def Doc.Proofs.Agrees (printer: Printer) (place: Place) (trace: List Event): Prop :=
  AgreesParts printer.out printer.owed printer.atLineStart printer.suffixes printer.lineIndent printer.started
      printer.newlinesAtEnd printer.carry place trace

--| The printer is at a place and trace that `next` holds of.
def Doc.Proofs.Stays (next: Place → List Event → Prop) (printer: Printer): Prop :=
  ∃ (place: Place) => ∃ (trace: List Event) => Agrees printer place trace ∧ next place trace

--| `Some` isn't `None`.
theorem Doc.Proofs.someNotNone ∀ (value: Nat) (wrong: Some value = None): Void := cases

--| A list with a first item isn't empty.
theorem Doc.Proofs.consNotNil ∀ (first: Text) (more: List Text) (wrong: [first, ..more] = []): Void := cases

--| A word put at a line start starts the line, at the indentation owed.
theorem Doc.Proofs.putStart ∀ (printer: Printer) (text: Text) (width at: Nat) (carry: Carry) (trace: List Event)
    (agrees: Agrees printer (AtStart at carry) trace)
    (word: isLayout text = False):
    Agrees (printer.put text width) (Mid at (floorAfter text carry)) (trace ++ [{ word = text, start = Some at }]) :=
  match printer, agrees with
    | {
        width = total,
        out,
        column,
        owed,
        atLineStart,
        suffixes,
        lineIndent,
        newlinesAtEnd,
        started,
        modes,
        heldSpaces,
        carry
      }, (start, none, blank, empty, owes, indent, same, floors) =>
      match owed, owes with
        | None, owes => (
          byComputing,
          none,
          (blankWord text out word),
          byComputing,
          indent,
          (rewrite <- owes, eventsWord text out word, blank, empty, same),
          byComputing,
          (rewrite floors)
        )
        | Some Zero, owes => (
          byComputing,
          none,
          (blankWord text out word),
          byComputing,
          indent,
          (rewrite <- owes, eventsWord text out word, blank, empty, same),
          byComputing,
          (rewrite floors)
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
            byComputing,
            (rewrite floors)
          )

--| A word put after words on its line doesn't start the line.
theorem Doc.Proofs.putMid ∀ (printer: Printer) (text: Text) (width at: Nat) (carry: Carry) (trace: List Event)
    (agrees: Agrees printer (Mid at carry) trace)
    (word: isLayout text = False):
    Agrees (printer.put text width) (Mid at (floorAfter text carry)) (trace ++ [{ word = text, start = None }]) :=
  match printer, agrees with
    | {
        width = total,
        out,
        column,
        owed,
        atLineStart,
        suffixes,
        lineIndent,
        newlinesAtEnd,
        started,
        modes,
        heldSpaces,
        carry
      }, (start, none, blank, owes, indent, same, _, floors) =>
      match owed, owes with
        | Some value, never => (someNotNone value never).impossible
        | None, _ => (
          byComputing,
          none,
          (blankWord text out word),
          byComputing,
          indent,
          (rewrite eventsWord text out word, blank, same),
          byComputing,
          (rewrite floors)
        )

--| Spaces put after words change nothing but the width, and end a
--| comment floor.
theorem Doc.Proofs.putSpaces ∀ (printer: Printer) (text: Text) (width at: Nat) (carry: Carry) (trace: List Event)
    (agrees: Agrees printer (Mid at carry) trace)
    (gap: text.all (char => char == ' ') = True):
    Agrees (printer.put text width) (Mid at (floorAfter text carry)) trace :=
  match printer, agrees with
    | {
        width = total,
        out,
        column,
        owed,
        atLineStart,
        suffixes,
        lineIndent,
        newlinesAtEnd,
        started,
        modes,
        heldSpaces,
        carry
      }, (start, none, blank, owes, indent, same, _, floors) =>
      match owed, owes with
        | Some value, never => (someNotNone value never).impossible
        | None, _ => (
          byComputing,
          none,
          (Eq.trans (blankGap text out gap) blank),
          byComputing,
          indent,
          (Eq.trans same (eventsGap text out gap).flipped),
          byComputing,
          (rewrite floors)
        )

--| After the line break that ends a line of words the printer is at the
--| start of a line indented as asked, or at the comment floor if deeper,
--| with one line break behind it, and a comment that waited is written
--| where the trace has it.
theorem Doc.Proofs.newlineBroken ∀ (printer: Printer) (indent: Nat) (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace)
    (mid: place.midLine = True):
    Agrees (printer.newline indent) (Broken (floored place.carry indent) (place.carry.breakTo indent)) trace :=
  match printer, place, agrees, mid with
    | {
        width = total,
        out,
        column,
        owed,
        atLineStart,
        suffixes,
        lineIndent,
        newlinesAtEnd,
        started,
        modes,
        heldSpaces,
        carry
      }, Mid at carry, (start, none, blank, owes, same, events, zero, floors), _ =>
      match suffixes, none with
        | [first, ..more], never => (consNotNil first more never).impossible
        | [], _ =>
          let words: lineBlank (trimSpaces out) = False := Eq.trans (trimBlank out) blank
          rewrite floors then
            (
              byComputing,
              byComputing,
              byComputing,
              byComputing,
              byComputing,
              byComputing,
              (Eq.trans events (Eq.flipped (Eq.trans (eventsBreak (trimSpaces out) words) (trimEvents out)))),
              byComputing,
              (Eq.cong ((count: Nat) => count + 1) zero),
              byComputing
            )
    | {
        width = total,
        out,
        column,
        owed,
        atLineStart,
        suffixes,
        lineIndent,
        newlinesAtEnd,
        started,
        modes,
        heldSpaces,
        carry
      }, Held at carry, (start, (Witness comment (Both one (Both word events))), blank, owes, same, floors), _ =>
      let written: eventsOf [comment, " ", ..trimSpaces out] = eventsOf out ++ [{ word = comment, start = None }] :=
        rewrite eventsWord comment [" ", ..trimSpaces out] word, trimBlank out, blank, trimEvents out
      let ended: eventsOf ["\n", comment, " ", ..trimSpaces out] = eventsOf [comment, " ", ..trimSpaces out] :=
        eventsBreak [comment, " ", ..trimSpaces out] (blankWord comment [" ", ..trimSpaces out] word)
      rewrite one, start, floors then
        (
          byComputing,
          byComputing,
          byComputing,
          byComputing,
          byComputing,
          byComputing,
          (Eq.trans events (Eq.trans ended written).flipped),
          byComputing,
          byComputing,
          byComputing
        )

--| A place that allows a `Blank` is a line start.
theorem Doc.Proofs.brokenStart ∀ (printer: Printer) (at: Nat) (carry: Carry) (trace: List Event)
    (agrees: Agrees printer (Broken at carry) trace):
    Agrees printer (AtStart at carry) trace :=
  match agrees with
    | (start, none, blank, empty, owes, indent, events, _, _, floors) =>
      (start, none, blank, empty, owes, indent, events, floors)

--| A line break from the middle of a line leaves the printer at the start of a
--| line with the same trace.
theorem Doc.Proofs.newlineAgrees ∀ (printer: Printer) (indent: Nat) (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace)
    (mid: place.midLine = True):
    Agrees (printer.newline indent) (AtStart (floored place.carry indent) (place.carry.breakTo indent)) trace :=
  brokenStart
    (printer.newline indent)
    (floored place.carry indent)
    (place.carry.breakTo indent)
    trace
    (newlineBroken printer indent place trace agrees mid)

--| The printer carrying what its place carries, both changed alike.
theorem Doc.Proofs.carryAgrees ∀ (printer: Printer) (place: Place) (carry: Carry) (trace: List Event)
    (agrees: Agrees printer place trace):
    Agrees { printer | carry = carry } (place.withCarry carry) trace :=
  match place, agrees with
    | AtStart at _, (start, none, blank, empty, owes, indent, events, _) =>
      (start, none, blank, empty, owes, indent, events, byComputing)
    | Broken at _, (start, none, blank, empty, owes, indent, events, started, newlines, _) =>
      (start, none, blank, empty, owes, indent, events, started, newlines, byComputing)
    | Mid at _, (start, none, blank, owes, indent, events, newlines, _) =>
      (start, none, blank, owes, indent, events, newlines, byComputing)
    | Held at _, (start, waits, blank, owes, indent, _) => (start, waits, blank, owes, indent, byComputing)

--| A place with its carry replaced still has words on its line exactly
--| if it had.
theorem Doc.Proofs.withCarryMid ∀ (place: Place) (carry: Carry): (place.withCarry carry).midLine = place.midLine :=
  match place with | AtStart _ _ | Broken _ _ | Mid _ _ | Held _ _ => byComputing

--| A place with its carry replaced carries the new one.
theorem Doc.Proofs.withCarryCarry ∀ (place: Place) (carry: Carry): (place.withCarry carry).carry = carry :=
  match place with | AtStart _ _ | Broken _ _ | Mid _ _ | Held _ _ => byComputing

--| A `Mark` leaves the printer where it was, carrying the mark.
theorem Doc.Proofs.markStays ∀ (next: Place → List Event → Prop) (printer: Printer) (key: Nat)
    (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace) (after: next (place.withCarry (place.carry.mark key place.indent)) trace):
    Stays next { printer | carry = printer.carry.mark key printer.lineIndent } :=
  let moved: next (place.withCarry (printer.carry.mark key printer.lineIndent)) trace :=
    rewrite agreesFloor printer place trace agrees, agreesIndent printer place trace agrees then after
  (
    (place.withCarry (printer.carry.mark key printer.lineIndent)),
    trace,
    (carryAgrees printer place (printer.carry.mark key printer.lineIndent) trace agrees),
    moved
  )

--| A closer's line at a line start with no comment waiting moves that
--| line to where the open marks say, with the closer's mark closed and no
--| comment floor.
theorem Doc.Proofs.closerLineMoves ∀ (printer: Printer) (key indent: Nat)
    (start: printer.atLineStart = True)
    (clear: printer.suffixes = []):
    printer.closerLine key indent
      = { printer |
        owed = Some (printer.carry.closerAt key indent),
        lineIndent = printer.carry.closerAt key indent,
        carry = (printer.carry.close key).breakTo (printer.carry.closerAt key indent)
      } :=
  match at: printer.atLineStart, start with | True, _ => rewrite clear

--| After words, the closer's line is right after a line break.
theorem Doc.Proofs.closerLineMid ∀ (place: Place) (key indent: Nat)
    (mid: place.midLine = True):
    place.closerLine key indent
      = Broken (place.carry.closerAt key indent) ((place.carry.close key).breakTo (place.carry.closerAt key indent)) :=
  match place, mid with
    | AtStart _ _ | Broken _ _, never => (Bool.falseNotTrue never).impossible
    | Mid _ _ | Held _ _, _ => byComputing

--| At a line start no comment waits.
theorem Doc.Proofs.startClear ∀ (printer: Printer) (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace)
    (start: printer.atLineStart = True):
    printer.suffixes = [] :=
  match place, agrees with
    | AtStart _ _ | Broken _ _, (_, none, _) => none
    | Mid _ _ | Held _ _, Both other _ => Void.impossible (Bool.falseNotTrue (Eq.trans other.flipped start))

--| A closer's line at a line start: the line moved, as the place says.
theorem Doc.Proofs.closerMoveAgrees ∀ (printer: Printer) (key indent: Nat) (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace)
    (start: printer.atLineStart = True):
    Agrees (printer.closerLine key indent) (place.closerLine key indent) trace :=
  rewrite closerLineMoves printer key indent start (startClear printer place trace agrees start),
      agreesFloor printer place trace agrees then
    match place, agrees with
      | AtStart at carry, (_, none, blank, empty, _, _, events, _) =>
        (start, none, blank, empty, byComputing, byComputing, events, byComputing)
      | Broken at carry, (_, none, blank, empty, _, _, events, started, newlines, _) =>
        (start, none, blank, empty, byComputing, byComputing, events, started, newlines, byComputing)
      | Mid _ _ | Held _ _, Both other _ => Void.impossible (Bool.falseNotTrue (Eq.trans other.flipped start))

--| A `CloserLine` leaves the printer where its puts say: after words a
--| line break where the open marks say, at a line start that line moved
--| there, with its mark closed and no comment floor.
theorem Doc.Proofs.closerStays ∀ (next: Place → List Event → Prop) (printer: Printer) (key indent: Nat)
    (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace)
    (puts: CloserPuts key indent place trace next):
    Stays next (printer.closerLine key indent) :=
  match start: printer.atLineStart with
    | True => (place.closerLine key indent, trace, (closerMoveAgrees printer key indent place trace agrees start), puts)
    | False =>
      let mid := startMid printer place trace agrees start
      let closed := place.carry.close key
      let column := place.carry.closerAt key indent
      let moved := carryAgrees printer place closed trace agrees
      let midMoved: (place.withCarry closed).midLine = True := Eq.trans (withCarryMid place closed) mid
      let broken := newlineBroken { printer | carry = closed } column (place.withCarry closed) trace moved midMoved
      let lands: Agrees ({ printer | carry = closed }.newline column) (Broken column (closed.breakTo column)) trace :=
        rewrite withCarryCarry place closed at broken
      let after: next (Broken column (closed.breakTo column)) trace :=
        rewrite closerLineMid place key indent mid at puts
      rewrite agreesFloor printer place trace agrees then (Broken column (closed.breakTo column), trace, lands, after)

--| A carry set at a line start (a new comment floor) is the place's.
theorem Doc.Proofs.floorAgrees ∀ (printer: Printer) (at: Nat) (carry other: Carry) (trace: List Event)
    (agrees: Agrees printer (AtStart at carry) trace):
    Agrees { printer | carry = other } (AtStart at other) trace :=
  match agrees with
    | (start, none, blank, empty, owes, indent, events, _) =>
      (start, none, blank, empty, owes, indent, events, byComputing)

--| A carry set right after a line break (a new comment floor) is the
--| place's.
theorem Doc.Proofs.floorBroken ∀ (printer: Printer) (at: Nat) (carry other: Carry) (trace: List Event)
    (agrees: Agrees printer (Broken at carry) trace):
    Agrees { printer | carry = other } (Broken at other) trace :=
  match agrees with
    | (start, none, blank, empty, owes, indent, events, started, newlines, _) =>
      (start, none, blank, empty, owes, indent, events, started, newlines, byComputing)

--| A printer agreeing with a place has the place's indentation as its line's.
theorem Doc.Proofs.agreesIndent ∀ (printer: Printer) (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace):
    printer.lineIndent = place.indent :=
  match place, agrees with
    | AtStart _ _ | Broken _ _, (_, _, _, _, _, indent, _) => indent
    | Mid _ _ | Held _ _, (_, _, _, _, indent, _) => indent

--| A printer agreeing with a place carries what the place does.
theorem Doc.Proofs.agreesFloor ∀ (printer: Printer) (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace):
    printer.carry = place.carry :=
  match place, agrees with
    | AtStart at carry, (_, _, _, _, _, _, _, floors) => floors
    | Broken at carry, (_, _, _, _, _, _, _, _, _, floors) => floors
    | Mid at carry, (_, _, _, _, _, _, _, floors) => floors
    | Held at carry, (_, _, _, _, _, floors) => floors

--| No comment waits at a line start or after plain words; one does at
--| `Held`.
theorem Doc.Proofs.agreesClear ∀ (printer: Printer) (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace):
    printer.suffixes.isEmpty
      = (match place with
        | AtStart _ _ | Broken _ _ | Mid _ _ => True
        | Held _ _ => False) :=
  match place, agrees with
    | AtStart _ _ | Broken _ _ | Mid _ _, Both _ (Both none _) => rewrite none
    | Held at carry, Both _ (Both (Witness comment (Both one _)) _) => rewrite one

--| A printer agreeing with a place is at a line start exactly at the places
--| that start a line.
theorem Doc.Proofs.agreesStart ∀ (printer: Printer) (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace):
    printer.atLineStart
      = (match place with
        | AtStart _ _ | Broken _ _ => True
        | Mid _ _ => False
        | Held _ _ => False) :=
  match place, agrees with | AtStart _ _ | Broken _ _ | Mid _ _ | Held _ _, Both start _ => start

--| Text that isn't only spaces or a line break is a word.
theorem Doc.Proofs.wordNotLayout ∀ (text: Text)
    (word: text.all (char => char == ' ') = False)
    (oneLine: (text == "\n") = False):
    isLayout text = False :=
  match gap: text.all (char => char == ' '), word with
    | False, _ => oneLine
    | True, never =>
      match never with
        | ()

--| A line break from the middle of a line leaves the printer right after
--| it, at a place that satisfies what follows.
theorem Doc.Proofs.newlineStays ∀ (next: Place → List Event → Prop) (printer: Printer) (indent: Nat)
    (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace)
    (mid: place.midLine = True) (after: next (Broken (floored place.carry indent) (place.carry.breakTo indent)) trace):
    Stays next (printer.newline indent) :=
  (
    (Broken (floored place.carry indent) (place.carry.breakTo indent)),
    trace,
    (newlineBroken printer indent place trace agrees mid),
    after
  )

--| A comment break: a line break to deeper than the line it breaks.
theorem Doc.Proofs.breakStays ∀ (next: Place → List Event → Prop) (printer: Printer) (indent: Nat)
    (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace)
    (mid: place.midLine = True)
    (after: next
      (Broken
        (floored place.carry (Nat.max indent (place.indent + 2)))
        (place.carry.breakTo (Nat.max indent (place.indent + 2))))
      trace):
    Stays next (printer.newline (printer.continuation indent)) :=
  let deeper: next
    (Broken
      (floored place.carry (Nat.max indent (printer.lineIndent + 2)))
      (place.carry.breakTo (Nat.max indent (printer.lineIndent + 2))))
    trace :=
    rewrite agreesIndent printer place trace agrees then after
  newlineStays next printer (printer.continuation indent) place trace agrees mid deeper

--| Writing at a line start, with no comment waiting, leaves the printer at a
--| place that satisfies what follows.
theorem Doc.Proofs.writeStart ∀ (next: Place → List Event → Prop) (printer: Printer) (indent: Nat) (text: Text)
    (width at: Nat) (carry: Carry) (trace: List Event)
    (agrees: Agrees printer (AtStart at carry) trace)
    (clear: printer.suffixes.isEmpty = True)
    (lays: WritePuts indent text (AtStart at carry) trace next):
    Stays next (printer.write indent text width) :=
  match empty: text.isEmpty, lays with
    | True, lays => ((AtStart at carry), trace, agrees, lays)
    | False, lays =>
      match spaces: text.all (char => char == ' '), lays with
        | True, never => (Bool.falseNotTrue never).impossible
        | False, Both oneLine lays =>
          match waiting: printer.suffixes.isEmpty, clear with
            | True, _ => (
              (Mid at (floorAfter text carry)),
              _,
              (putStart printer text width at carry trace agrees (wordNotLayout text spaces oneLine)),
              lays
            )

--| Writing in the middle of a line, with no comment waiting, leaves the printer
--| at a place that satisfies what follows.
theorem Doc.Proofs.writeMid ∀ (next: Place → List Event → Prop) (printer: Printer) (indent: Nat) (text: Text)
    (width at: Nat) (carry: Carry) (trace: List Event)
    (agrees: Agrees printer (Mid at carry) trace)
    (clear: printer.suffixes.isEmpty = True)
    (lays: WritePuts indent text (Mid at carry) trace next):
    Stays next (printer.write indent text width) :=
  match empty: text.isEmpty, lays with
    | True, lays => ((Mid at carry), trace, agrees, lays)
    | False, lays =>
      match spaces: text.all (char => char == ' '), lays with
        | True, lays =>
          match waiting: printer.suffixes.isEmpty, clear with
            | True, _ => (
              (Mid at (floorAfter text carry)),
              trace,
              (putSpaces printer text width at carry trace agrees spaces),
              lays
            )
        | False, Both oneLine lays =>
          match waiting: printer.suffixes.isEmpty, clear with
            | True, _ => (
              (Mid at (floorAfter text carry)),
              _,
              (putMid printer text width at carry trace agrees (wordNotLayout text spaces oneLine)),
              lays
            )

--| Spaces held after a waiting comment leave the printer where it was.
theorem Doc.Proofs.holdAgrees ∀ (printer: Printer) (held: Nat) (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace):
    Agrees { printer | heldSpaces = held } place trace :=
  agrees

--| Writing while a comment waits leaves the printer at a place that satisfies
--| what follows.
theorem Doc.Proofs.writeHeld ∀ (next: Place → List Event → Prop) (printer: Printer) (indent: Nat) (text: Text)
    (width at: Nat) (carry: Carry) (trace: List Event)
    (agrees: Agrees printer (Held at carry) trace)
    (waits: printer.suffixes.isEmpty = False)
    (lays: WritePuts indent text (Held at carry) trace next):
    Stays next (printer.write indent text width) :=
  match empty: text.isEmpty, lays with
    | True, lays => ((Held at carry), trace, agrees, lays)
    | False, lays =>
      match spaces: text.all (char => char == ' '), lays with
        | True, lays =>
          match waiting: printer.suffixes.isEmpty, waits with
            | False, _ => (
              (Held at carry),
              trace,
              (holdAgrees printer (printer.heldSpaces + text.length) (Held at carry) trace agrees),
              lays
            )
        | False, Both oneLine lays =>
          let broken := floored carry (Nat.max indent (printer.lineIndent + 2))
          let deeper: next
            (Mid broken (floorAfter text (carry.breakTo (Nat.max indent (printer.lineIndent + 2)))))
            (trace ++ [{ word = text, start = Some broken }]) :=
            rewrite agreesIndent printer (Held at carry) trace agrees then lays
          match waiting: printer.suffixes.isEmpty, waits with
            | False, _ => (
              (Mid broken (floorAfter text (carry.breakTo (Nat.max indent (printer.lineIndent + 2))))),
              _,
              (putStart
                (printer.newline (printer.continuation indent))
                text
                width
                broken
                (carry.breakTo (printer.continuation indent))
                trace
                (newlineAgrees printer (printer.continuation indent) (Held at carry) trace agrees byComputing)
                (wordNotLayout text spaces oneLine)),
              deeper
            )

--| Writing after a blank line, with no comment waiting, leaves the printer at a
--| place that satisfies what follows.
theorem Doc.Proofs.writeBroken ∀ (next: Place → List Event → Prop) (printer: Printer) (indent: Nat) (text: Text)
    (width at: Nat) (carry: Carry) (trace: List Event)
    (agrees: Agrees printer (Broken at carry) trace)
    (clear: printer.suffixes.isEmpty = True)
    (lays: WritePuts indent text (Broken at carry) trace next):
    Stays next (printer.write indent text width) :=
  match empty: text.isEmpty, lays with
    | True, lays => ((Broken at carry), trace, agrees, lays)
    | False, lays =>
      match spaces: text.all (char => char == ' '), lays with
        | True, never => (Bool.falseNotTrue never).impossible
        | False, Both oneLine lays =>
          match waiting: printer.suffixes.isEmpty, clear with
            | True, _ => (
              (Mid at (floorAfter text carry)),
              _,
              (putStart printer text width at carry trace
                (brokenStart printer at carry trace agrees)
                (wordNotLayout text spaces oneLine)),
              lays
            )

--| A chunk written where the document said.
theorem Doc.Proofs.writeStays ∀ (next: Place → List Event → Prop) (printer: Printer) (indent: Nat) (text: Text)
    (width: Nat) (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace)
    (lays: WritePuts indent text place trace next):
    Stays next (printer.write indent text width) :=
  match place, agrees, lays with
    | AtStart at carry, agrees, lays =>
      writeStart next printer indent text width at carry trace agrees
        (agreesClear printer (AtStart at carry) trace agrees)
        lays
    | Broken at carry, agrees, lays =>
      writeBroken next printer indent text width at carry trace agrees
        (agreesClear printer (Broken at carry) trace agrees)
        lays
    | Mid at carry, agrees, lays =>
      writeMid next printer indent text width at carry trace agrees
        (agreesClear printer (Mid at carry) trace agrees)
        lays
    | Held at carry, agrees, lays =>
      writeHeld next printer indent text width at carry trace agrees
        (agreesClear printer (Held at carry) trace agrees)
        lays

--| A comment tucked into events that end with `last` goes before `last`.
theorem Doc.Proofs.tuckedSnoc ∀ (event last: Event) (before: List Event):
    tucked event (before ++ [last]) = before ++ [event, last] :=
  match before with
    | [first, second, ..rest] => rewrite repeatedly [tuckedSnoc event last [second, ..rest]]
    | _ => cases

--| A word put on a line where a comment waits goes before the comment,
--| which still waits.
theorem Doc.Proofs.putHeld ∀ (printer: Printer) (text: Text) (width at: Nat) (carry: Carry) (trace: List Event)
    (agrees: Agrees printer (Held at carry) trace)
    (word: isLayout text = False):
    Agrees (printer.put text width) (Held at (floorAfter text carry)) (tucked { word = text, start = None } trace) :=
  match printer, agrees with
    | {
        width = total,
        out,
        column,
        owed,
        atLineStart,
        suffixes,
        lineIndent,
        newlinesAtEnd,
        started,
        modes,
        heldSpaces,
        carry
      }, (start, (Witness comment (Both one (Both isWord same))), blank, owes, indent, floors) =>
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
          indent,
          (rewrite floors)
        )

--| The spaces held, written before a closer on a comment's line, leave
--| the printer where it was.
theorem Doc.Proofs.heldAgrees ∀ (printer: Printer) (at: Nat) (carry: Carry) (trace: List Event)
    (agrees: Agrees printer (Held at carry) trace):
    Agrees printer.writeHeld (Held at carry) trace :=
  match start: printer.atLineStart with
    | True => agrees
    | False =>
      match held: printer.heldSpaces with
        | Zero => agrees
        | Succ less =>
          match agrees with
            | (start, (Witness comment (Both one (Both isWord same))), blank, owes, indent, floors) =>
              let gap := " ".repeat (Succ less)
              let spaces := indentSpaces (Succ less)
              (
                start,
                ((comment, one, isWord, (rewrite eventsGap gap printer.out spaces then same))),
                (Eq.trans (blankGap gap printer.out spaces) blank),
                owes,
                indent,
                floors
              )

--| A closer written where the document said.
theorem Doc.Proofs.closeStays ∀ (next: Place → List Event → Prop) (printer: Printer) (indent: Nat) (text: Text)
    (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace)
    (lays: ClosePuts indent text place trace next):
    Stays next (printer.close text) :=
  match place, agrees, lays with
    | AtStart at carry, agrees, lays =>
      rewrite closeClear printer indent text (agreesClear printer (AtStart at carry) trace agrees) then
        writeStays next printer indent text text.length (AtStart at carry) trace agrees lays
    | Broken at carry, agrees, lays =>
      rewrite closeClear printer indent text (agreesClear printer (Broken at carry) trace agrees) then
        writeStays next printer indent text text.length (Broken at carry) trace agrees lays
    | Mid at carry, agrees, lays =>
      rewrite closeClear printer indent text (agreesClear printer (Mid at carry) trace agrees) then
        writeStays next printer indent text text.length (Mid at carry) trace agrees lays
    | Held at carry, agrees, (word, lays) =>
      rewrite closePut printer text (wordFilled text word) (agreesClear printer (Held at carry) trace agrees) then
        (
          (Held at (floorAfter text carry)),
          (tucked { word = text, start = None } trace),
          (putHeld printer.writeHeld text text.length at carry trace (heldAgrees printer at carry trace agrees) word),
          lays
        )

--| A separator's puts, where it breaks, hold `next` at the start of a line.
theorem Doc.Proofs.sepBroken ∀ (next: Place → List Event → Prop) (indent: Nat) (place: Place) (trace: List Event)
    (lays: SepPuts indent place trace next):
    next (Broken (floored place.carry indent) (place.carry.breakTo indent)) trace :=
  match place, lays with
    | AtStart _ _ | Broken _ _, never => (Bool.falseNotTrue never).impossible
    | Mid _ _ | Held _ _, Both _ broken => broken

--| A separator's puts are only met in the middle of a line.
theorem Doc.Proofs.sepMid ∀ (next: Place → List Event → Prop) (indent: Nat) (place: Place) (trace: List Event)
    (lays: SepPuts indent place trace next):
    place.midLine = True :=
  match place, lays with
    | AtStart _ _ | Broken _ _, never => never
    | _, _ => cases

--| A soft line's puts are only met in the middle of a line.
theorem Doc.Proofs.softMid ∀ (next: Place → List Event → Prop) (indent: Nat) (place: Place) (trace: List Event)
    (lays: SoftPuts indent place trace next):
    place.midLine = True :=
  match place, lays with
    | AtStart _ _ | Broken _ _, never => never
    | _, _ => cases

--| With nothing at the start of its line the printer is after words.
theorem Doc.Proofs.startMid ∀ (printer: Printer) (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace)
    (start: printer.atLineStart = False):
    place.midLine = True :=
  match place, agrees with
    | AtStart _ _ | Broken _ _, Both other _ => Eq.trans start.flipped other
    | _, _ => cases

--| A separator written as a space, with no comment waiting.
theorem Doc.Proofs.sepSpace ∀ (next: Place → List Event → Prop) (printer: Printer) (indent: Nat)
    (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace)
    (clear: printer.suffixes.isEmpty = True)
    (lays: SepPuts indent place trace next):
    Stays next (printer.write indent " " 1) :=
  match place, agrees, lays with
    | AtStart _ _ | Broken _ _, _, never => (Bool.falseNotTrue never).impossible
    | Mid at carry, agrees, Both same _ =>
      match waiting: printer.suffixes.isEmpty, clear with
        | True, _ =>
          ((Mid at { carry | floor = None }), trace, (putSpaces printer " " 1 at carry trace agrees byComputing), same)
    | Held at carry, agrees, _ =>
      Void.impossible
        (Bool.falseNotTrue (Eq.trans (Eq.flipped (agreesClear printer (Held at carry) trace agrees)) clear))

--| A flat `Line`: a space, or held where a comment waits.
theorem Doc.Proofs.sepStays ∀ (next: Place → List Event → Prop) (printer: Printer) (indent: Nat)
    (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace)
    (lays: SepPuts indent place trace next):
    Stays next (printer.write indent " " 1) :=
  match place, agrees, lays with
    | Held at carry, agrees, Both held _ =>
      let waits: printer.suffixes.isEmpty = False := agreesClear printer (Held at carry) trace agrees
      rewrite spacesAfterComment printer indent " " 1 byComputing waits byComputing then
        (
          (Held at carry),
          trace,
          (holdAgrees printer (printer.heldSpaces + " ".length) (Held at carry) trace agrees),
          held
        )
    | Mid at carry, agrees, lays =>
      sepSpace next printer indent (Mid at carry) trace agrees (agreesClear printer (Mid at carry) trace agrees) lays
    | AtStart _ _ | Broken _ _, _, never => (Bool.falseNotTrue never).impossible

--| A soft line's puts, where it breaks, hold `next` at the start of a line.
theorem Doc.Proofs.softBroken ∀ (next: Place → List Event → Prop) (indent: Nat) (place: Place) (trace: List Event)
    (lays: SoftPuts indent place trace next):
    next (Broken (floored place.carry indent) (place.carry.breakTo indent)) trace :=
  match place, lays with
    | AtStart _ _ | Broken _ _, never => (Bool.falseNotTrue never).impossible
    | Mid _ _ | Held _ _, Both _ broken => broken

--| A soft line's puts, where it stays flat, hold `next` at the place as
--| it was.
theorem Doc.Proofs.softSame ∀ (next: Place → List Event → Prop) (indent: Nat) (place: Place) (trace: List Event)
    (lays: SoftPuts indent place trace next):
    next place trace :=
  match place, lays with
    | AtStart _ _ | Broken _ _, never => (Bool.falseNotTrue never).impossible
    | Mid _ _ | Held _ _, Both same _ => same

--| A line start at a line's start changes nothing.
theorem Doc.Proofs.lineStartSame ∀ (printer: Printer) (indent: Nat)
    (start: printer.atLineStart = True):
    printer.lineStart indent = printer :=
  match at: printer.atLineStart, start with | True, _ => byComputing

--| A line start after text breaks the line at the continuation indentation,
--| which is the comment floor from there.
theorem Doc.Proofs.lineStartBreaks ∀ (printer: Printer) (indent: Nat)
    (start: printer.atLineStart = False):
    printer.lineStart indent
      = { printer.newline (printer.continuation indent) |
        carry = printer.carry.startFloor (printer.continuation indent)
      } :=
  match at: printer.atLineStart, start with | False, _ => byComputing

--| A line start leaves the printer at a place that satisfies what follows.
theorem Doc.Proofs.lineStartStays ∀ (next: Place → List Event → Prop) (printer: Printer) (indent: Nat)
    (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace)
    (lays: StartPuts indent place trace next):
    Stays next (printer.lineStart indent) :=
  match place, agrees, lays with
    | AtStart at carry, agrees, lays =>
      rewrite lineStartSame printer indent (agreesStart printer (AtStart at carry) trace agrees) then
        ((AtStart at carry), trace, agrees, lays)
    | Broken at carry, agrees, lays =>
      rewrite lineStartSame printer indent (agreesStart printer (Broken at carry) trace agrees) then
        ((Broken at carry), trace, agrees, lays)
    | Mid at carry, agrees, lays =>
      let broken := Nat.max indent (printer.lineIndent + 2)
      let deeper: next (Broken (floored carry broken) (printer.carry.startFloor broken)) trace :=
        rewrite agreesIndent printer (Mid at carry) trace agrees, agreesFloor printer (Mid at carry) trace agrees then
          lays
      rewrite lineStartBreaks printer indent (agreesStart printer (Mid at carry) trace agrees) then
        (
          (Broken (floored carry broken) (printer.carry.startFloor broken)),
          trace,
          (floorBroken
            (printer.newline broken)
            (floored carry broken)
            (carry.breakTo broken)
            (printer.carry.startFloor broken)
            trace
            (newlineBroken printer broken (Mid at carry) trace agrees byComputing)),
          deeper
        )
    | Held at carry, agrees, lays =>
      let broken := Nat.max indent (printer.lineIndent + 2)
      let deeper: next (Broken (floored carry broken) (printer.carry.startFloor broken)) trace :=
        rewrite agreesIndent printer (Held at carry) trace agrees, agreesFloor printer (Held at carry) trace agrees then
          lays
      rewrite lineStartBreaks printer indent (agreesStart printer (Held at carry) trace agrees) then
        (
          (Broken (floored carry broken) (printer.carry.startFloor broken)),
          trace,
          (floorBroken
            (printer.newline broken)
            (floored carry broken)
            (carry.breakTo broken)
            (printer.carry.startFloor broken)
            trace
            (newlineBroken printer broken (Held at carry) trace agrees byComputing)),
          deeper
        )

--| The line start a place is at, moved to `indent`: still right after a
--| line break if it was. A place after words has no line start to move,
--| and is taken as a plain one.
def Doc.Proofs.Place.movedTo (place: Place) (indent: Nat): Place := match place with
  | Broken _ carry => Broken indent carry
  | _ => AtStart indent place.carry

--| Indentation set at the start of a line.
theorem Doc.Proofs.hereAgrees ∀ (printer: Printer) (indent: Nat) (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace)
    (start: printer.atLineStart = True):
    Agrees { printer | owed = Some indent, lineIndent = indent } (place.movedTo indent) trace :=
  match place, agrees with
    | AtStart at carry, (_, none, blank, empty, _, _, events, floors) =>
      (start, none, blank, empty, byComputing, byComputing, events, floors)
    | Broken at carry, (_, none, blank, empty, _, _, events, started, newlines, floors) =>
      (start, none, blank, empty, byComputing, byComputing, events, started, newlines, floors)
    | Mid _ _ | Held _ _, Both other _ => Void.impossible (Bool.falseNotTrue (Eq.trans other.flipped start))

--| A `LineStartHere` at a line's start moves the line; its puts hold there.
theorem Doc.Proofs.herePlace ∀ (next: Place → List Event → Prop) (indent: Nat) (place: Place) (trace: List Event)
    (start: place.midLine = False)
    (lays: HerePuts indent place trace next):
    next (place.movedTo indent) trace :=
  match place, start, lays with
    | AtStart _ _ | Broken _ _, _, lays => lays
    | Mid _ _ | Held _ _, never, _ => (Bool.falseNotTrue never.flipped).impossible

--| A `LineStartHere` after words breaks the line; its puts hold there.
theorem Doc.Proofs.hereBroken ∀ (next: Place → List Event → Prop) (indent: Nat) (place: Place) (trace: List Event)
    (mid: place.midLine = True)
    (lays: HerePuts indent place trace next):
    next (Broken (floored place.carry indent) (place.carry.breakTo indent)) trace :=
  match place, mid, lays with
    | AtStart _ _ | Broken _ _, never, _ => (Bool.falseNotTrue never).impossible
    | Mid _ _ | Held _ _, _, lays => lays

--| At a line start the place doesn't have words on its line.
theorem Doc.Proofs.startNotMid ∀ (printer: Printer) (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace)
    (start: printer.atLineStart = True):
    place.midLine = False :=
  match place, agrees with
    | Mid _ _ | Held _ _, Both other _ => Eq.trans start.flipped other
    | _, _ => cases

--| A blank line after text, not at a line start, changes nothing.
theorem Doc.Proofs.blankSame ∀ (printer: Printer) (start: printer.atLineStart = False): printer.blank = printer :=
  match at: printer.atLineStart, start with | False, _ => byComputing

--| One line break behind it and something printed, the printer adds the
--| line break that leaves a blank line.
theorem Doc.Proofs.blankAdds ∀ (printer: Printer)
    (start: printer.atLineStart = True)
    (started: printer.started = True)
    (one: printer.newlinesAtEnd = 1):
    printer.blank = { printer | out = ["\n", ..printer.out], newlinesAtEnd = printer.newlinesAtEnd + 1 } :=
  match at: printer.atLineStart, begun: printer.started, start, started with | True, True, _, _ => rewrite one

--| A `Blank` leaves a blank line right after a line of words, and
--| nothing after words.
theorem Doc.Proofs.blankStays ∀ (next: Place → List Event → Prop) (printer: Printer) (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace)
    (lays: BlankPuts place trace next):
    Stays next printer.blank :=
  match place, agrees, lays with
    | AtStart at carry, _, never => (Bool.falseNotTrue never).impossible
    | Broken at carry, (start, none, blank, empty, owes, indent, events, started, one, floors), lays =>
      rewrite blankAdds printer start started one then
        (
          (AtStart at carry),
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
              (eventsBlank printer.out blank).flipped),
            floors
          )),
          lays
        )
    | Mid at carry, agrees, lays =>
      rewrite blankSame printer (agreesStart printer (Mid at carry) trace agrees) then
        ((Mid at carry), trace, agrees, lays)
    | Held at carry, agrees, lays =>
      rewrite blankSame printer (agreesStart printer (Held at carry) trace agrees) then
        ((Held at carry), trace, agrees, lays)

--| A trailing comment starts waiting, already in the trace.
theorem Doc.Proofs.suffixStays ∀ (next: Place → List Event → Prop) (printer: Printer) (comment: Text)
    (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace)
    (word: isLayout comment = False)
    (lays: SuffixPuts comment place trace next):
    Stays next { printer | suffixes = printer.suffixes ++ [comment] } :=
  match place, agrees, lays with
    | AtStart _ _ | Broken _ _ | Held _ _, _, never => (Bool.falseNotTrue never).impossible
    | Mid at carry, (start, none, blank, owes, indent, events, _, floors), lays =>
      let one: printer.suffixes ++ [comment] = [comment] := rewrite none
      (
        (Held at carry),
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
          indent,
          floors
        )),
        lays
      )

--| A step that goes one way or the other leaves the printer at a place that
--| satisfies what follows if each way does.
theorem Doc.Proofs.eitherStays ∀ (spec: Place → List Event → Prop) (flat: Bool) (yes no: Printer) (rest: List Cmd)
    (whenYes: Stays (place trace => StackPuts spec rest place trace) yes)
    (whenNo: Stays (place trace => StackPuts spec rest place trace) no):
    Stays
      (place trace => StackPuts spec (if flat then (yes, rest) else (no, rest)).snd place trace)
      (if flat then (yes, rest) else (no, rest)).fst :=
  match flat with
    | True => whenYes
    | False => whenNo

--| A step of a reading keeps the printer where the work list said, and
--| the work list it leaves lays from there.
theorem Doc.Proofs.stepPuts ∀ (spec: Place → List Event → Prop) (printer: Printer) (cmd: Cmd) (rest: List Cmd)
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
        | Doc.Nothing | BreakParent, steps, lays => rewrite steps then (place, trace, agrees, lays)
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
            eitherStays spec mode.isFlat
              (printer.write indent " " 1)
              (printer.newline indent)
              rest
              (sepStays (after later => StackPuts spec rest after later) printer indent place trace agrees lays)
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
            eitherStays spec mode.isFlat printer
              (printer.newline indent)
              rest
              (
                place,
                trace,
                agrees,
                (softSame (after later => StackPuts spec rest after later) indent place trace lays)
              )
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
          rewrite steps then
            (
              (Broken (floored place.carry indent) (place.carry.breakTo indent)),
              trace,
              (newlineBroken printer indent place trace agrees mid),
              broken
            )
        | HardLine, steps, Both mid (Inr started) =>
          rewrite steps then
            (
              (AtStart (floored place.carry indent) (place.carry.breakTo indent)),
              trace,
              (newlineAgrees printer indent place trace agrees mid),
              started
            )
        | LineStart, steps, lays =>
          rewrite steps then
            lineStartStays (after later => StackPuts spec rest after later) printer indent place trace agrees lays
        | LineStartHere, steps, lays =>
          match start: printer.atLineStart with
            | True =>
              rewrite steps then
                (
                  (place.movedTo indent),
                  trace,
                  (hereAgrees printer indent place trace agrees start),
                  (herePlace
                    (after later => StackPuts spec rest after later)
                    indent
                    place
                    trace
                    (startNotMid printer place trace agrees start)
                    lays)
                )
            | False =>
              let mid := startMid printer place trace agrees start
              rewrite steps then
                newlineStays
                  (after later => StackPuts spec rest after later)
                  printer
                  indent
                  place
                  trace
                  agrees
                  mid
                  (hereBroken (after later => StackPuts spec rest after later) indent place trace mid lays)
        | Blank, steps, lays =>
          rewrite steps then blankStays (after later => StackPuts spec rest after later) printer place trace agrees lays
        | Mark key, steps, lays =>
          rewrite steps then
            markStays (after later => StackPuts spec rest after later) printer key place trace agrees lays
        | CloserLine key, steps, lays =>
          rewrite steps then
            closerStays (after later => StackPuts spec rest after later) printer key indent place trace agrees lays
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
        | OneLineBelow inner, steps, Both mid lays => rewrite steps then (place, trace, agrees, mid, (Inl lays))
        | Flatten inner, steps, lays => rewrite steps then (place, trace, agrees, lays)
        | LineSuffix comment, steps, Both word lays =>
          rewrite steps then
            suffixStays (after later => StackPuts spec rest after later) printer comment place trace agrees word lays
        | Group _ _ | NarrowGroup _ _ _ | IdGroup _ _ _, Inl (Both _ flat) | Inr (Both _ flat), lays =>
          rewrite flat then (place, trace, agrees, lays)
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
theorem Doc.Proofs.pickPuts ∀ (modes: List (Nat, Mode)) (id: Nat) (broken flat: Doc) (indent: Nat) (place: Place)
    (trace: List Event) (next: Place → List Event → Prop)
    (puts: Puts (IfBroken id broken flat) indent place trace next):
    Puts (pickBranch modes id broken flat) indent place trace next :=
  match pickEither modes id broken flat, puts with
    | Inl isBroken, Both brokenPuts _ => rewrite isBroken then brokenPuts
    | Inr isFlat, Both _ flatPuts => rewrite isFlat then flatPuts

--| An `Align` at a line start indents its line breaks to `atStart`.
theorem Doc.Proofs.alignAtStart ∀ (printer: Printer) (atStart: Nat)
    (start: printer.atLineStart = True):
    printer.alignAt atStart = atStart :=
  match at: printer.atLineStart, start with | True, _ => byComputing

--| An `Align`'s contents hold at the indentation the printer gives them.
theorem Doc.Proofs.alignHere ∀ (printer: Printer) (atStart: Nat) (place: Place) (trace: List Event) (inner: Nat → Prop)
    (agrees: Agrees printer place trace)
    (holds: AlignHolds atStart place inner):
    inner (printer.alignAt atStart) :=
  match place, agrees, holds with
    | AtStart at carry, agrees, holds =>
      rewrite alignAtStart printer atStart (agreesStart printer (AtStart at carry) trace agrees) then holds
    | Broken at carry, agrees, holds =>
      rewrite alignAtStart printer atStart (agreesStart printer (Broken at carry) trace agrees) then holds
    | Mid _ _ | Held _ _, _, holds => holds (printer.alignAt atStart)

--| With no comment waiting, a `Displaced` element changes nothing before
--| it.
theorem Doc.Proofs.displaceClear ∀ (printer: Printer) (indent: Nat)
    (clear: printer.suffixes.isEmpty = True):
    printer.displace indent = printer :=
  match empty: printer.suffixes.isEmpty, clear with | True, _ => byComputing

--| A `Displaced` element after a waiting comment starts a line first.
theorem Doc.Proofs.displaceWaiting ∀ (printer: Printer) (indent: Nat)
    (waiting: printer.suffixes.isEmpty = False):
    printer.displace indent = printer.commentBreak indent :=
  match empty: printer.suffixes.isEmpty, waiting with | False, _ => byComputing

--| A comment break after text breaks the line at the continuation
--| indentation.
theorem Doc.Proofs.commentBreakBreaks ∀ (printer: Printer) (indent: Nat)
    (start: printer.atLineStart = False):
    printer.commentBreak indent = printer.newline (printer.continuation indent) :=
  match at: printer.atLineStart, start with | False, _ => byComputing

--| At a line start, a `Displaced` element's line breaks go to the line's
--| indentation, if deeper.
theorem Doc.Proofs.displacedAtStart ∀ (printer: Printer) (indent at: Nat)
    (start: printer.atLineStart = True)
    (owes: printer.owed.getOrElse 0 = at):
    printer.displacedAt indent = Nat.max indent at :=
  match on: printer.atLineStart, start with | True, _ => rewrite owes

--| After words, with no comment waiting, a `Displaced` element's line
--| breaks go to the construct's indentation.
theorem Doc.Proofs.displacedAtMid ∀ (printer: Printer) (indent: Nat)
    (start: printer.atLineStart = False)
    (clear: printer.suffixes.isEmpty = True):
    printer.displacedAt indent = indent :=
  match on: printer.atLineStart, start with
    | False, _ =>
      match empty: printer.suffixes.isEmpty, clear with
        | True, _ => byComputing

--| After a waiting comment, a `Displaced` element's line breaks go to the
--| comment break's indentation.
theorem Doc.Proofs.displacedAtHeld ∀ (printer: Printer) (indent: Nat)
    (start: printer.atLineStart = False)
    (waiting: printer.suffixes.isEmpty = False):
    printer.displacedAt indent = printer.continuation indent :=
  match on: printer.atLineStart, start with
    | False, _ =>
      match empty: printer.suffixes.isEmpty, waiting with
        | False, _ => byComputing

--| A `Displaced` element leaves the printer where its contents start, as
--| `DisplacedHolds` says.
theorem Doc.Proofs.displacedStays ∀ (printer: Printer) (indent: Nat) (place: Place)
    (trace: List Event) (put: Nat → Place → List Event → Prop)
    (agrees: Agrees printer place trace)
    (holds: DisplacedHolds indent place (column start => put column start trace)):
    Stays (put (printer.displacedAt indent)) (printer.displace indent) :=
  match place, agrees, holds with
    | AtStart at carry, agrees, holds =>
      let start := agreesStart printer (AtStart at carry) trace agrees
      let clear := agreesClear printer (AtStart at carry) trace agrees
      match agrees with
        | Both _ (Both _ (Both _ (Both _ (Both owes _)))) =>
          rewrite displaceClear printer indent clear, (displacedAtStart printer indent at start owes) then
            ((AtStart at carry), trace, agrees, holds)
    | Broken at carry, agrees, holds =>
      let start := agreesStart printer (Broken at carry) trace agrees
      let clear := agreesClear printer (Broken at carry) trace agrees
      match agrees with
        | Both _ (Both _ (Both _ (Both _ (Both owes _)))) =>
          rewrite displaceClear printer indent clear, (displacedAtStart printer indent at start owes) then
            ((Broken at carry), trace, agrees, holds)
    | Mid at carry, agrees, holds =>
      let start := agreesStart printer (Mid at carry) trace agrees
      let clear := agreesClear printer (Mid at carry) trace agrees
      rewrite displaceClear printer indent clear, displacedAtMid printer indent start clear then
        ((Mid at carry), trace, agrees, holds)
    | Held at carry, agrees, holds =>
      let start := agreesStart printer (Held at carry) trace agrees
      let waiting := agreesClear printer (Held at carry) trace agrees
      let deeper: put
        (printer.continuation indent)
        (Broken (floored carry (Nat.max indent (at + 2))) (carry.breakTo (Nat.max indent (at + 2))))
        trace :=
        rewrite agreesIndent printer (Held at carry) trace agrees then holds
      rewrite displaceWaiting printer indent waiting,
          commentBreakBreaks printer indent start,
          displacedAtHeld printer indent start waiting then
        breakStays (put (printer.continuation indent)) printer indent (Held at carry) trace agrees byComputing deeper

--| A reading that has the steps to finish its work list ends where the
--| work list's last document leaves it, at a place and trace `spec`
--| holds of.
theorem Doc.Proofs.readingPuts ∀ (spec: Place → List Event → Prop) (printer: Printer) (fuel: Nat) (stack: List Cmd)
    (final: Printer) (place: Place) (trace: List Event)
    (reads: Doc.Proofs.Reads printer fuel stack final)
    (agrees: Agrees printer place trace)
    (lays: StackPuts spec stack place trace)
    (enough: stackCost stack ≤ fuel):
    Stays spec final :=
  match fuel, stack, reads, lays with
    | Zero | Succ _, [], reads, lays => (place, trace, (rewrite reads then agrees), lays)
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
theorem Doc.Proofs.flushAgrees ∀ (printer: Printer) (place: Place) (trace: List Event)
    (agrees: Agrees printer place trace):
    trace = eventsOf printer.flushSuffixes.out :=
  match printer, place, agrees with
    | {
        width = total,
        out,
        column,
        owed,
        atLineStart,
        suffixes,
        lineIndent,
        newlinesAtEnd,
        started,
        modes,
        ..
      }, AtStart at carry, Both _ (Both none (Both _ (Both _ (Both _ (Both _ (Both events _)))))) =>
      rewrite none then events
    | { width = total, out, column, owed, atLineStart, suffixes, lineIndent, newlinesAtEnd, started, modes, .. }, Broken
          at carry, Both _ (Both none (Both _ (Both _ (Both _ (Both _ (Both events _)))))) => rewrite none then events
    | { width = total, out, column, owed, atLineStart, suffixes, lineIndent, newlinesAtEnd, started, modes, .. }, Mid at
          carry, Both _ (Both none (Both _ (Both _ (Both _ (Both events _))))) => rewrite none then events
    | { width = total, out, column, owed, atLineStart, suffixes, lineIndent, newlinesAtEnd, started, modes, .. }, Held
          at carry, Both start (Both (Witness comment (Both one (Both word events))) (Both blank _)) =>
      let written: eventsOf [comment, " ", ..out] = eventsOf out ++ [{ word = comment, start = None }] :=
        rewrite eventsWord comment [" ", ..out] word, blank
      rewrite one, start then Eq.trans events written.flipped

--| The pieces `print` joins, in the order printed.
def Doc.Proofs.printedPieces (doc: Doc) (width: Nat): List Text :=
  ((Printer.start width).run (3 * doc.size + 3) (3 * doc.size + 3) [Print 0 Break doc] |> .flushSuffixes).out.reverse

--| `print` is the printer's pieces joined.
theorem Doc.Proofs.printIsPieces ∀ (doc: Doc) (width: Nat):
    Doc.print doc width = (printedPieces doc width).joinWith "" :=
  byComputing

--| A document that lays from the start of an unindented line, printed at
--| any width, puts each word where the document said: `spec` holds of the
--| words of the printed pieces in order, each with the column it starts
--| its line at, if it does.
theorem Doc.Proofs.printPuts ∀ (spec: Place → List Event → Prop) (doc: Doc) (width: Nat)
    (lays: Puts doc 0 (AtStart 0 Carry.none) [] spec):
    ∃ (place: Place) => spec place (eventsOf (printedPieces doc width).reverse) :=
  let fuel := 3 * doc.size + 3
  let ran := (Printer.start width).run fuel fuel [Print 0 Break doc]
  let bound := stepsUnderSize doc
  let start: Agrees (Printer.start width) (AtStart 0 Carry.none) [] :=
    (byComputing, byComputing, byComputing, byComputing, byComputing, byComputing, byComputing, byComputing)
  match readingPuts spec
    (Printer.start width)
    fuel
    [Print 0 Break doc]
    ran
    (AtStart 0 Carry.none)
    []
    (runIsReading (Printer.start width) fuel fuel [Print 0 Break doc])
    start
    lays
    (arithmetic) with
    | (place, trace, agrees, holds) =>
      (place, (rewrite List.reverseReverse ran.flushSuffixes.out, <- flushAgrees ran place trace agrees then holds))

--| `Puts` computes, and can be met: `f`, then `x` on a line of its own
--| two columns in, at every width.
theorem Doc.Proofs.printPutsExample ∀ (width: Nat):
    ∃ (place: Place) => eventsOf
      (printedPieces (Concat [Chunk "f" 1, Nest 2 (Concat [HardLine, Chunk "x" 1])]) width).reverse
      = [{ word = "f", start = Some 0 }, { word = "x", start = Some 2 }] :=
  printPuts
    (place trace => trace = [{ word = "f", start = Some 0 }, { word = "x", start = Some 2 }])
    (Concat [Chunk "f" 1, Nest 2 (Concat [HardLine, Chunk "x" 1])])
    width
    ((byComputing, byComputing, (Inr ((byComputing, byComputing)))))

--| A `Blank` right after a line break leaves a blank line: `f`, then
--| a blank line, then `-- c` two columns in, on the line a `LineStart`
--| starts, at every width.
theorem Doc.Proofs.blankAfterBreakExample ∀ (width: Nat):
    ∃ (place: Place) => eventsOf (printedPieces (Concat [Chunk "f" 1, LineStart, Blank, Chunk "-- c" 4]) width).reverse
      = [{ word = "f", start = Some 0 }, Event.blankLine, { word = "-- c", start = Some 2 }] :=
  printPuts
    (place trace => trace = [{ word = "f", start = Some 0 }, Event.blankLine, { word = "-- c", start = Some 2 }])
    (Concat [Chunk "f" 1, LineStart, Blank, Chunk "-- c" 4])
    width
    ((byComputing, (byComputing, byComputing)))

--| A closer after a trailing comment is printed before it: `x) -- c` at
--| every width, the comment last in the trace.
theorem Doc.Proofs.closerPutsExample ∀ (width: Nat):
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
theorem Doc.Proofs.midExample: Agrees ((Printer.start 80).put "f" 1) (Mid 0 Carry.none) [
      { word = "f", start = Some 0 }
    ] :=
  putStart
    (Printer.start 80)
    "f"
    1
    0
    Carry.none
    []
    ((byComputing, byComputing, byComputing, byComputing, byComputing, byComputing, byComputing, byComputing))
    byComputing

--| An instance of `putMid` with all its hypotheses met, so it isn't
--| vacuous: `g` after `f` doesn't start the line. The audit's random search
--| can't find one, since a random printer almost never agrees with a trace.
theorem Doc.Proofs.putMidExample: Agrees (((Printer.start 80).put "f" 1).put "g" 1) (Mid 0 Carry.none) [
      { word = "f", start = Some 0 },
      { word = "g", start = None }
    ] :=
  putMid ((Printer.start 80).put "f" 1) "g" 1 0 Carry.none [{ word = "f", start = Some 0 }] midExample byComputing

--| An instance of `putSpaces` with all its hypotheses met, as for
--| `putMidExample`: a space after `f` leaves the trace alone.
theorem Doc.Proofs.putSpacesExample: Agrees (((Printer.start 80).put "f" 1).put " " 1) (Mid 0 Carry.none) [
      { word = "f", start = Some 0 }
    ] :=
  putSpaces ((Printer.start 80).put "f" 1) " " 1 0 Carry.none [{ word = "f", start = Some 0 }] midExample byComputing
