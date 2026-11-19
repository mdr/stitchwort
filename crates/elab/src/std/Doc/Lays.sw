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

import Doc (..)
import Bool (not)
import Doc.Proofs (..)

--| `--` and the rest of its line: a trailing comment's text.
def Doc.Proofs.IsComment (text: Text): Prop :=
  ∃ (others: List Char) => text.toList = ['-', '-', ..others] ∧ others.all (char => char != '\n') = True

--| A comment's text starts with `--`.
theorem Doc.Proofs.commentStarts ∀ (text: Text) (comment: IsComment text): text.startsWith "--" = True :=
  match comment with
    | (others, chars, _) =>
      let starts: Text.startsWithChars "--".toList text.toList = True := rewrite chars
      starts

--| The texts `Closing` is for: a closing bracket or a comma.
def Doc.Proofs.closesText (text: Text): Bool := text == ")" || text == "]" || text == ","

--| A chunk in a construct indented `indent`: nothing if empty; spaces
--| after words (never at a line start, where they would move the next
--| word); a word where the place says, on a new line after a waiting
--| comment.
def Doc.Proofs.WriteLays (indent: Nat) (text: Text) (place: Place)
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

--| A closer in a construct indented `indent`: a chunk where no comment
--| waits; where one waits, a word on the comment's line, which the tree
--| has after the comment (the printer writes it before).
def Doc.Proofs.CloseLays (indent: Nat) (text: Text) (place: Place)
    (trace: List Event) (next: Place → List Event → Prop):
    Prop :=
  match place with
    | Held at carry =>
      closesText text = True ∧ next (Held at (floorAfter text carry)) (trace ++ [{ word = text, start = None }])
    | _ => WriteLays indent text place trace next

--| A `Line` or a fill's separator: a space or a line break, after words.
--| After a waiting comment the space is held, so the place stays.
def Doc.Proofs.SepLays (indent: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop): Prop :=
  match place with
    | AtStart _ _ | Broken _ _ => False
    | Mid at carry =>
      next (Mid at { carry | floor = None }) trace ∧ next (Broken (floored carry indent) (carry.breakTo indent)) trace
    | Held at carry => next (Held at carry) trace ∧ next (Broken (floored carry indent) (carry.breakTo indent)) trace

--| A `SoftLine`: nothing or a line break, after words.
def Doc.Proofs.SoftLays (indent: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop): Prop :=
  match place with
    | AtStart _ _ | Broken _ _ => False
    | Mid at carry => next (Mid at carry) trace ∧ next (Broken (floored carry indent) (carry.breakTo indent)) trace
    | Held at carry => next (Held at carry) trace ∧ next (Broken (floored carry indent) (carry.breakTo indent)) trace

--| A `LineStart`: a comment break, deeper than the line, unless a line
--| starts here; the break's indentation is the floor until the next
--| code.
def Doc.Proofs.StartLays (indent: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop): Prop :=
  match place with
    | AtStart at carry => next (AtStart at carry) trace
    | Broken at carry => next (Broken at carry) trace
    | Mid at carry | Held at carry =>
      let broken := Nat.max indent (at + 2)
      next (Broken (floored carry broken) (carry.startFloor broken)) trace

--| A trailing comment: after words on its line, with no other waiting.
def Doc.Proofs.SuffixLays (comment: Text) (place: Place) (trace: List Event) (next: Place → List Event → Prop): Prop :=
  match place with
    | AtStart _ _ | Broken _ _ => False
    | Mid at carry => next (Held at carry) (trace ++ [{ word = comment, start = None }])
    | Held _ _ => False

--| A `Blank`: a blank line right after the line break that ended a line
--| of words; nothing after words; at no other line start, where the
--| printer may or may not leave one.
def Doc.Proofs.BlankLays (place: Place) (trace: List Event) (next: Place → List Event → Prop): Prop := match place with
  | AtStart _ _ => False
  | Broken at carry => next (AtStart at carry) (trace ++ [Event.blankLine])
  | Mid at carry => next (Mid at carry) trace
  | Held at carry => next (Held at carry) trace

--| From `place` with `trace` laid, every way `doc` may print in a
--| construct indented `indent` puts its words where `next` is told, and
--| every place it may leave satisfies `next`. A line break that isn't a
--| `Line` or `SoftLine` comes only after words (at a line start it would
--| leave a blank line). Every line break after words leaves `Broken`, as
--| the printer is then (one line break behind it), so a `Blank` may
--| follow; after a `HardLine` the document may say instead that none
--| does (`AtStart`).
def Doc.Proofs.Lays (doc: Doc) (indent: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop):
    Prop :=
  match doc with
    | Doc.Nothing | BreakParent => next place trace
    | Blank => BlankLays place trace next
    | Chunk text _ => WriteLays indent text place trace next
    | Closing text => CloseLays indent text place trace next
    | Line => SepLays indent place trace next
    | SoftLine => SoftLays indent place trace next
    | HardLine =>
      let broken := floored place.carry indent
      place.midLine = True
        ∧ (next (Broken broken (place.carry.breakTo indent)) trace
          ∨ next (AtStart broken (place.carry.breakTo indent)) trace)
    | LineStart => StartLays indent place trace next
    | LineStartHere => HerePuts indent place trace next
    | Mark key => next (place.withCarry (place.carry.mark key place.indent)) trace
    | CloserLine key => CloserPuts key indent place trace next
    | Nest more inner => Lays inner (indent + more) place trace next
    | Align inner => AlignHolds indent place (column => Lays inner column place trace next)
    | AlignInset inner => AlignHolds (indent + 2) place (column => Lays inner column place trace next)
    | Displaced inner => DisplacedHolds indent place (column start => Lays inner column start trace next)
    | Group inner _ | NarrowGroup _ inner _ | IdGroup _ inner _ => Lays inner indent place trace next
    | IfBroken _ broken flat => Lays broken indent place trace next ∧ Lays flat indent place trace next
    | Flatten inner => Lays inner indent place trace next
    | OneLineBelow inner =>
      place.midLine = True
        ∧ Lays inner
          (indent + 2)
          (Broken (floored place.carry (indent + 2)) (place.carry.breakTo (indent + 2)))
          trace
          next
    | Concat docs => LaysAll docs indent place trace next
    | Fill items => FillLays items indent place trace next
    | Choice options => OptionsLay options indent place trace next
    | LineSuffix comment => IsComment comment ∧ isLayout comment = False ∧ SuffixLays comment place trace next

--| Each of the docs in turn lays out, from the place and trace the one before
--| left.
def Doc.Proofs.LaysAll (docs: List Doc) (indent: Nat) (place: Place)
    (trace: List Event) (next: Place → List Event → Prop):
    Prop :=
  match docs with
    | [] => next place trace
    | [doc, ..rest] => Lays doc indent place trace (after later => LaysAll rest indent after later next)

--| The items of a fill lay out, each after a separator that is a space or a
--| line break.
def Doc.Proofs.FillLays (items: List Doc) (indent: Nat) (place: Place)
    (trace: List Event) (next: Place → List Event → Prop):
    Prop :=
  match items with
    | [] => next place trace
    | [first, ..others] => Lays first indent place trace (after later => SepsLay others indent after later next)

--| The separators before the items of a fill, and the items, lay out in turn.
def Doc.Proofs.SepsLay (items: List Doc) (indent: Nat) (place: Place)
    (trace: List Event) (next: Place → List Event → Prop):
    Prop :=
  match items with
    | [] => next place trace
    | [item, ..more] => SepLays indent place trace (middle between =>
      Lays item indent middle between (after later => SepsLay more indent after later next))

--| Every option a choice may take lays out.
def Doc.Proofs.OptionsLay (options: List Doc) (indent: Nat) (place: Place)
    (trace: List Event) (next: Place → List Event → Prop):
    Prop :=
  match options with
    | [] => next place trace
    | [last] => Lays last indent place trace next
    | [option, ..others] => Lays option indent place trace next ∧ OptionsLay others indent place trace next

-- A weaker continuation still holds.

--| `WriteLays` holds with a weaker requirement on what follows, if it holds
--| with a stronger one.
theorem Doc.Proofs.writeLaysWeaker ∀ (indent: Nat) (text: Text) (place: Place) (trace: List Event)
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
            | AtStart _ _ | Broken _ _, never => never
            | Mid _ _ | Held _ _, lays => implies _ _ lays
        | False, Both oneLine lays =>
          match place, lays with
            | AtStart _ _ | Broken _ _ | Mid _ _ | Held _ _, lays => (oneLine, (implies _ _ lays))

--| `CloseLays` holds with a weaker requirement on what follows, if it holds
--| with a stronger one.
theorem Doc.Proofs.closeLaysWeaker ∀ (indent: Nat) (text: Text) (place: Place) (trace: List Event)
    (strong weak: Place → List Event → Prop)
    (implies: ∀ (after: Place) (later: List Event) => strong after later → weak after later)
    (lays: CloseLays indent text place trace strong):
    CloseLays indent text place trace weak :=
  match place, lays with
    | Held at carry, (closes, lays) => (closes, (implies _ _ lays))
    | AtStart at carry, lays => writeLaysWeaker indent text (AtStart at carry) trace strong weak implies lays
    | Broken at carry, lays => writeLaysWeaker indent text (Broken at carry) trace strong weak implies lays
    | Mid at carry, lays => writeLaysWeaker indent text (Mid at carry) trace strong weak implies lays

--| `SepLays` holds with a weaker requirement on what follows, if it holds with
--| a stronger one.
theorem Doc.Proofs.sepLaysWeaker ∀ (indent: Nat) (place: Place) (trace: List Event)
    (strong weak: Place → List Event → Prop)
    (implies: ∀ (after: Place) (later: List Event) => strong after later → weak after later)
    (lays: SepLays indent place trace strong):
    SepLays indent place trace weak :=
  match place, lays with
    | AtStart _ _ | Broken _ _, never => never
    | Mid _ _ | Held _ _, Both same broken => ((implies _ _ same), (implies _ _ broken))

--| `SoftLays` holds with a weaker requirement on what follows, if it holds with
--| a stronger one.
theorem Doc.Proofs.softLaysWeaker ∀ (indent: Nat) (place: Place) (trace: List Event)
    (strong weak: Place → List Event → Prop)
    (implies: ∀ (after: Place) (later: List Event) => strong after later → weak after later)
    (lays: SoftLays indent place trace strong):
    SoftLays indent place trace weak :=
  match place, lays with
    | AtStart _ _ | Broken _ _, never => never
    | Mid _ _ | Held _ _, Both same broken => ((implies _ _ same), (implies _ _ broken))

--| `StartLays` holds with a weaker requirement on what follows, if it holds
--| with a stronger one.
theorem Doc.Proofs.startLaysWeaker ∀ (indent: Nat) (place: Place) (trace: List Event)
    (strong weak: Place → List Event → Prop)
    (implies: ∀ (after: Place) (later: List Event) => strong after later → weak after later)
    (lays: StartLays indent place trace strong):
    StartLays indent place trace weak :=
  match place, lays with | AtStart _ _ | Broken _ _ | Mid _ _ | Held _ _, lays => implies _ _ lays

--| `SuffixLays` holds with a weaker requirement on what follows, if it holds
--| with a stronger one.
theorem Doc.Proofs.suffixLaysWeaker ∀ (comment: Text) (place: Place) (trace: List Event)
    (strong weak: Place → List Event → Prop)
    (implies: ∀ (after: Place) (later: List Event) => strong after later → weak after later)
    (lays: SuffixLays comment place trace strong):
    SuffixLays comment place trace weak :=
  match place, lays with
    | AtStart _ _ | Broken _ _, never => never
    | Mid at carry, lays => implies _ _ lays
    | Held at carry, never => never

--| `BlankLays` holds with a weaker requirement on what follows, if it holds
--| with a stronger one.
theorem Doc.Proofs.blankLaysWeaker ∀ (place: Place) (trace: List Event) (strong weak: Place → List Event → Prop)
    (implies: ∀ (after: Place) (later: List Event) => strong after later → weak after later)
    (lays: BlankLays place trace strong):
    BlankLays place trace weak :=
  match place, lays with
    | AtStart at carry, never => never
    | Broken _ _ | Mid _ _ | Held _ _, lays => implies _ _ lays

--| What holds with a continuation holds with any it implies.
theorem Doc.Proofs.laysWeaker ∀ (doc: Doc) (indent: Nat) (place: Place) (trace: List Event)
    (strong weak: Place → List Event → Prop)
    (implies: ∀ (after: Place) (later: List Event) => strong after later → weak after later)
    (lays: Lays doc indent place trace strong):
    Lays doc indent place trace weak :=
  match doc, lays with
    | Doc.Nothing | BreakParent, lays => implies _ _ lays
    | Blank, lays => blankLaysWeaker place trace strong weak implies lays
    | Chunk text width, lays => writeLaysWeaker indent text place trace strong weak implies lays
    | Closing text, lays => closeLaysWeaker indent text place trace strong weak implies lays
    | Line, lays => sepLaysWeaker indent place trace strong weak implies lays
    | SoftLine, lays => softLaysWeaker indent place trace strong weak implies lays
    | HardLine, Both mid (Inl broken) => (mid, (Inl (implies _ _ broken)))
    | HardLine, Both mid (Inr started) => (mid, (Inr (implies _ _ started)))
    | LineStart, lays => startLaysWeaker indent place trace strong weak implies lays
    | LineStartHere, lays => herePutsWeaker indent place trace strong weak implies lays
    | Mark _ | CloserLine _, lays => implies _ _ lays
    | Nest more inner, lays => laysWeaker inner (indent + more) place trace strong weak implies lays
    | Align inner, lays =>
      match place, lays with
        | AtStart at carry, lays => laysWeaker inner indent (AtStart at carry) trace strong weak implies lays
        | Broken at carry, lays => laysWeaker inner indent (Broken at carry) trace strong weak implies lays
        | Mid at carry, lays => column => laysWeaker inner column (Mid at carry) trace strong weak implies (lays column)
        | Held at carry, lays => column =>
          laysWeaker inner column (Held at carry) trace strong weak implies (lays column)
    | AlignInset inner, lays =>
      match place, lays with
        | AtStart at carry, lays => laysWeaker inner (indent + 2) (AtStart at carry) trace strong weak implies lays
        | Broken at carry, lays => laysWeaker inner (indent + 2) (Broken at carry) trace strong weak implies lays
        | Mid at carry, lays => column => laysWeaker inner column (Mid at carry) trace strong weak implies (lays column)
        | Held at carry, lays => column =>
          laysWeaker inner column (Held at carry) trace strong weak implies (lays column)
    | Displaced inner, lays =>
      match place, lays with
        | AtStart at carry, lays =>
          laysWeaker inner (Nat.max indent at) (AtStart at carry) trace strong weak implies lays
        | Broken at carry, lays => laysWeaker inner (Nat.max indent at) (Broken at carry) trace strong weak implies lays
        | Mid at carry, lays => laysWeaker inner indent (Mid at carry) trace strong weak implies lays
        | Held at carry, lays =>
          laysWeaker inner
            (Nat.max indent (at + 2))
            (Broken (floored carry (Nat.max indent (at + 2))) (carry.breakTo (Nat.max indent (at + 2))))
            trace
            strong
            weak
            implies
            lays
    | Group inner _ | NarrowGroup _ inner _ | IdGroup _ inner _, lays =>
      laysWeaker inner indent place trace strong weak implies lays
    | IfBroken id broken flat, Both brokenLays flatLays => (
      (laysWeaker broken indent place trace strong weak implies brokenLays),
      (laysWeaker flat indent place trace strong weak implies flatLays)
    )
    | Flatten inner, lays => laysWeaker inner indent place trace strong weak implies lays
    | OneLineBelow inner, Both mid lays => (
      mid,
      (laysWeaker inner
        (indent + 2)
        (Broken (floored place.carry (indent + 2)) (place.carry.breakTo (indent + 2)))
        trace
        strong
        weak
        implies
        lays)
    )
    | Concat docs, lays => allLaysWeaker docs indent place trace strong weak implies lays
    | Fill items, lays => fillLaysWeaker items indent place trace strong weak implies lays
    | Choice options, lays => optionsLayWeaker options indent place trace strong weak implies lays
    | LineSuffix comment, (isComment, word, lays) =>
      (isComment, word, (suffixLaysWeaker comment place trace strong weak implies lays))

--| `LaysAll` holds with a weaker requirement on what follows, if it holds with
--| a stronger one.
theorem Doc.Proofs.allLaysWeaker ∀ (docs: List Doc) (indent: Nat) (place: Place) (trace: List Event)
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

--| `FillLays` holds with a weaker requirement on what follows, if it holds with
--| a stronger one.
theorem Doc.Proofs.fillLaysWeaker ∀ (items: List Doc) (indent: Nat) (place: Place) (trace: List Event)
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

--| `SepsLay` holds with a weaker requirement on what follows, if it holds with
--| a stronger one.
theorem Doc.Proofs.sepsLayWeaker ∀ (items: List Doc) (indent: Nat) (place: Place) (trace: List Event)
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

--| `OptionsLay` holds with a weaker requirement on what follows, if it holds
--| with a stronger one.
theorem Doc.Proofs.optionsLayWeaker ∀ (options: List Doc) (indent: Nat) (place: Place) (trace: List Event)
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

--| Items with a `Line` between each two lay out if the first does and then the
--| rest, each after a separator.
theorem Doc.Proofs.linesLay ∀ (first: Doc) (others: List Doc) (indent: Nat) (place: Place)
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
type Doc.Proofs.Stretch =
  | Kept (event: Event)
  | Tucked (comment: Event) (closers: List Event)

--| The stretch as the document has it: the comment, then the closers.
def Doc.Proofs.Stretch.laid: Stretch → List Event
  | Kept event => [event]
  | Tucked comment closers => [comment, ..closers]

--| The stretch as it is printed: the closers, then the comment.
def Doc.Proofs.Stretch.printed: Stretch → List Event
  | Kept event => [event]
  | Tucked comment closers => closers ++ [comment]

--| A closer written on a waiting comment's line: after other words.
def Doc.Proofs.Closer (event: Event): Prop := event.start = None ∧ closesText event.word = True

--| A tucked stretch is a trailing comment and closers on its line.
def Doc.Proofs.Stretch.Fits: Stretch → Prop
  | Kept event => True
  | Tucked comment closers => comment.start = None ∧ IsComment comment.word ∧ List.All Closer closers

--| The laid events of the stretches, in order.
def Doc.Proofs.laidOf: List Stretch → List Event
  | [] => []
  | [first, ..rest] => first.laid ++ laidOf rest

--| The printed events of the stretches, in order.
def Doc.Proofs.printedOf: List Stretch → List Event
  | [] => []
  | [first, ..rest] => first.printed ++ printedOf rest

--| An event that starts a line, or a blank line: what follows a
--| trailing comment's line.
def Doc.Proofs.Stretch.Starts: Stretch → Prop
  | Kept event => (∃ (at: Nat) => event.start = Some at) ∨ event.word = "\n"
  | Tucked _ _ => False

--| After a trailing comment's stretch the next line starts: no word
--| follows a comment on its line but the closers tucked before it.
def Doc.Proofs.LineEnded: List Stretch → Prop
  | [] | [_] => True
  | [Tucked comment closers, next, ..rest] => next.Starts ∧ LineEnded [next, ..rest]
  | [Kept event, next, ..rest] => LineEnded [next, ..rest]

--| Whether the stretch is a single kept event.
def Doc.Proofs.Stretch.IsKept: Stretch → Prop
  | Kept event => True
  | Tucked comment closers => False

--| The last stretch is one event (or there is none): no comment has
--| just been written.
def Doc.Proofs.EndsKept: List Stretch → Prop
  | [] => True
  | [last] => last.IsKept
  | [first, next, ..rest] => EndsKept [next, ..rest]

--| `printed` is `laid` with each trailing comment after the closers that
--| were written on its line.
def Doc.Proofs.Tucks (laid printed: List Event): Prop :=
  ∃ (stretches: List Stretch) => List.All Stretch.Fits stretches
    ∧ LineEnded stretches
    ∧ laid = laidOf stretches
    ∧ printed = printedOf stretches

--| As `Tucks`, after a word on its line: no comment was written last.
def Doc.Proofs.Settles (laid printed: List Event): Prop :=
  ∃ (stretches: List Stretch) => List.All Stretch.Fits stretches
    ∧ LineEnded stretches
    ∧ EndsKept stretches
    ∧ laid = laidOf stretches
    ∧ printed = printedOf stretches

--| As `Tucks`, where a comment still waits: the last stretch is its.
def Doc.Proofs.Waits (laid printed: List Event): Prop :=
  ∃ (stretches: List Stretch) => ∃ (comment: Event) => ∃ (closers: List Event) => List.All Stretch.Fits stretches
    ∧ LineEnded stretches
    ∧ EndsKept stretches
    ∧ Stretch.Fits (Tucked comment closers)
    ∧ laid = laidOf stretches ++ [comment, ..closers]
    ∧ printed = printedOf stretches ++ (closers ++ [comment])

--| The two traces at a place the printer is at.
def Doc.Proofs.Tracks (place: Place) (laid printed: List Event): Prop := match place with
  | Held _ _ => Waits laid printed
  | Mid _ _ => Settles laid printed
  | _ => Tucks laid printed

--| A stretch that fits, added to the end of stretches that do, keeps them
--| fitting.
theorem Doc.Proofs.fitsSnoc ∀ (stretches: List Stretch) (last: Stretch)
    (all: List.All Stretch.Fits stretches) (fits: last.Fits):
    List.All Stretch.Fits (stretches ++ [last]) :=
  match stretches, all with
    | [], _ => (fits, ())
    | [first, ..rest], (firstFits, others) => (firstFits, (fitsSnoc rest last others fits))

--| A closer added to the end of closers is still all closers.
theorem Doc.Proofs.closersSnoc ∀ (closers: List Event) (last: Event)
    (all: List.All Closer closers)
    (closer: Closer last):
    List.All Closer (closers ++ [last]) :=
  match closers, all with
    | [], _ => (closer, ())
    | [first, ..rest], (firstCloser, others) => (firstCloser, (closersSnoc rest last others closer))

--| One more stretch keeps the stretches spaced, after an event or if it
--| starts a line.
theorem Doc.Proofs.lineEndedSnoc ∀ (stretches: List Stretch) (last: Stretch)
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

--| Stretches that end with a kept event, after one is added, end kept.
theorem Doc.Proofs.endsKeptSnoc ∀ (stretches: List Stretch) (event: Event): EndsKept (stretches ++ [Kept event]) :=
  match stretches with
    | [first, next, ..rest] => endsKeptSnoc [next, ..rest] event
    | _ => cases

--| A stretch added at the end adds its laid events at the end.
theorem Doc.Proofs.laidSnoc ∀ (stretches: List Stretch) (last: Stretch):
    laidOf (stretches ++ [last]) = laidOf stretches ++ last.laid :=
  match stretches with
    | [] => List.appendNil last.laid
    | [first, ..rest] =>
      calc first.laid ++ laidOf (rest ++ [last])
        _ = first.laid ++ (laidOf rest ++ last.laid) :=
          Eq.cong ((later: List Event) => first.laid ++ later) (laidSnoc rest last)
        _ = (first.laid ++ laidOf rest) ++ last.laid := (List.appendAssoc first.laid (laidOf rest) last.laid).flipped

--| A stretch added at the end adds its printed events at the end.
theorem Doc.Proofs.printedSnoc ∀ (stretches: List Stretch) (last: Stretch):
    printedOf (stretches ++ [last]) = printedOf stretches ++ last.printed :=
  match stretches with
    | [] => List.appendNil last.printed
    | [first, ..rest] =>
      calc first.printed ++ printedOf (rest ++ [last])
        _ = first.printed ++ (printedOf rest ++ last.printed) :=
          Eq.cong ((later: List Event) => first.printed ++ later) (printedSnoc rest last)
        _ = (first.printed ++ printedOf rest) ++ last.printed :=
          (List.appendAssoc first.printed (printedOf rest) last.printed).flipped

--| Stretches that settle laid into printed tuck the trailing comments.
theorem Doc.Proofs.settlesTucks ∀ (laid printed: List Event) (settles: Settles laid printed): Tucks laid printed :=
  match settles with
    | (stretches, fits, spaced, ends, sameLaid, samePrinted) => (stretches, fits, spaced, sameLaid, samePrinted)

--| An event after a word on its line, after both traces.
theorem Doc.Proofs.settlesSnoc ∀ (laid printed: List Event) (event: Event)
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
theorem Doc.Proofs.tucksSnoc ∀ (laid printed: List Event) (event: Event)
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
theorem Doc.Proofs.waitsTucks ∀ (laid printed: List Event) (waits: Waits laid printed): Tucks laid printed :=
  match waits with
    | (stretches, comment, closers, fits, spaced, ends, last, sameLaid, samePrinted) => (
      (stretches ++ [Tucked comment closers]),
      (fitsSnoc stretches (Tucked comment closers) fits last),
      (lineEndedSnoc stretches (Tucked comment closers) spaced (Inl ends)),
      (rewrite sameLaid then (laidSnoc stretches (Tucked comment closers)).flipped),
      (rewrite samePrinted then (printedSnoc stretches (Tucked comment closers)).flipped)
    )

--| Traces that track each other at a place tuck the trailing comments.
theorem Doc.Proofs.tracksTucks ∀ (place: Place) (laid printed: List Event)
    (tracks: Tracks place laid printed):
    Tucks laid printed :=
  match place, tracks with
    | AtStart _ _ | Broken _ _, tucks => tucks
    | Mid at carry, settles => settlesTucks laid printed settles
    | Held at carry, waits => waitsTucks laid printed waits

--| Traces that track each other at a place track each other at the start
--| of a closer's line from there: every waiting comment has been written.
theorem Doc.Proofs.closerTracks ∀ (place: Place) (key indent: Nat) (laid printed: List Event)
    (tracks: Tracks place laid printed):
    Tracks (place.closerLine key indent) laid printed :=
  let tucks := tracksTucks place laid printed tracks
  match place with | AtStart _ _ | Broken _ _ | Mid _ _ | Held _ _ => tucks

--| A trailing comment starts to wait: it is in both traces, last.
theorem Doc.Proofs.settlesWaits ∀ (laid printed: List Event) (comment: Text)
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
theorem Doc.Proofs.waitsClose ∀ (laid printed: List Event) (text: Text)
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

--| A closer's text (`)`, `]` or `,`) is a word, not layout.
theorem Doc.Proofs.closesWord ∀ (text: Text) (closes: closesText text = True): isLayout text = False :=
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
theorem Doc.Proofs.closesWordExample: isLayout ")" = False := closesWord ")" byComputing

-- Every `Lays` is a `Puts`.

--| `WriteLays` gives `WritePuts`, in the printer's own trace, given how the
--| traces track each other and that what follows carries over.
theorem Doc.Proofs.writeLaysPuts ∀ (indent: Nat) (text: Text) (place: Place) (laid printed: List Event)
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
            | AtStart _ _ | Broken _ _, _, never => never
            | Mid _ _ | Held _ _, tracks, lays => onward _ _ _ tracks lays
        | False, Both oneLine lays =>
          match place, tracks, lays with
            | AtStart at _ | Broken at _, tracks, lays =>
              (oneLine, (onward _ _ _ (tucksSnoc laid printed _ tracks (Inl ((at, byComputing)))) lays))
            | Mid at carry, tracks, lays => (oneLine, (onward _ _ _ (settlesSnoc laid printed _ tracks) lays))
            | Held at carry, tracks, lays => (
              oneLine,
              (onward _ _ _
                (tucksSnoc laid printed _
                  (waitsTucks laid printed tracks)
                  (Inl (((floored carry (Nat.max indent (at + 2))), byComputing))))
                lays)
            )

--| `CloseLays` gives `ClosePuts`, in the printer's own trace, given how the
--| traces track each other and that what follows carries over.
theorem Doc.Proofs.closeLaysPuts ∀ (indent: Nat) (text: Text) (place: Place) (laid printed: List Event)
    (next put: Place → List Event → Prop)
    (onward: ∀ (after: Place) (later written: List Event) => Tracks after later written
      → next after later
      → put after written)
    (tracks: Tracks place laid printed)
    (lays: CloseLays indent text place laid next):
    ClosePuts indent text place printed put :=
  match place, tracks, lays with
    | Held at carry, tracks, (closes, lays) =>
      ((closesWord text closes), (onward _ _ _ (waitsClose laid printed text tracks closes) lays))
    | AtStart at carry, tracks, lays =>
      writeLaysPuts indent text (AtStart at carry) laid printed next put onward tracks lays
    | Broken at carry, tracks, lays =>
      writeLaysPuts indent text (Broken at carry) laid printed next put onward tracks lays
    | Mid at carry, tracks, lays => writeLaysPuts indent text (Mid at carry) laid printed next put onward tracks lays

--| `SepLays` gives `SepPuts`, in the printer's own trace, given how the traces
--| track each other and that what follows carries over.
theorem Doc.Proofs.sepLaysPuts ∀ (indent: Nat) (place: Place) (laid printed: List Event)
    (next put: Place → List Event → Prop)
    (onward: ∀ (after: Place) (later written: List Event) => Tracks after later written
      → next after later
      → put after written)
    (tracks: Tracks place laid printed)
    (lays: SepLays indent place laid next):
    SepPuts indent place printed put :=
  match place, tracks, lays with
    | AtStart _ _ | Broken _ _, _, never => never
    | Mid at carry, tracks, Both same broken =>
      ((onward _ _ _ tracks same), (onward _ _ _ (settlesTucks laid printed tracks) broken))
    | Held at carry, tracks, Both same broken =>
      ((onward _ _ _ tracks same), (onward _ _ _ (waitsTucks laid printed tracks) broken))

--| `SoftLays` gives `SoftPuts`, in the printer's own trace, given how the
--| traces track each other and that what follows carries over.
theorem Doc.Proofs.softLaysPuts ∀ (indent: Nat) (place: Place) (laid printed: List Event)
    (next put: Place → List Event → Prop)
    (onward: ∀ (after: Place) (later written: List Event) => Tracks after later written
      → next after later
      → put after written)
    (tracks: Tracks place laid printed)
    (lays: SoftLays indent place laid next):
    SoftPuts indent place printed put :=
  match place, tracks, lays with
    | AtStart _ _ | Broken _ _, _, never => never
    | Mid at carry, tracks, Both same broken =>
      ((onward _ _ _ tracks same), (onward _ _ _ (settlesTucks laid printed tracks) broken))
    | Held at carry, tracks, Both same broken =>
      ((onward _ _ _ tracks same), (onward _ _ _ (waitsTucks laid printed tracks) broken))

--| Traces that track each other at a place do at the place with its
--| carry replaced.
theorem Doc.Proofs.carryTracks ∀ (place: Place) (carry: Carry) (laid printed: List Event)
    (tracks: Tracks place laid printed):
    Tracks (place.withCarry carry) laid printed :=
  match place, tracks with | AtStart _ _ | Broken _ _ | Mid _ _ | Held _ _, tracks => tracks

--| A `LineStartHere`'s puts carry over to the printer's own trace.
theorem Doc.Proofs.hereLaysPuts ∀ (indent: Nat) (place: Place) (laid printed: List Event)
    (next put: Place → List Event → Prop)
    (onward: ∀ (after: Place) (later written: List Event) => Tracks after later written
      → next after later
      → put after written)
    (tracks: Tracks place laid printed)
    (lays: HerePuts indent place laid next):
    HerePuts indent place printed put :=
  match place, tracks, lays with
    | AtStart _ _ | Broken _ _, tracks, lays => onward _ _ _ tracks lays
    | Mid at carry, tracks, lays => onward _ _ _ (settlesTucks laid printed tracks) lays
    | Held at carry, tracks, lays => onward _ _ _ (waitsTucks laid printed tracks) lays

--| `StartLays` gives `StartPuts`, in the printer's own trace, given how the
--| traces track each other and that what follows carries over.
theorem Doc.Proofs.startLaysPuts ∀ (indent: Nat) (place: Place) (laid printed: List Event)
    (next put: Place → List Event → Prop)
    (onward: ∀ (after: Place) (later written: List Event) => Tracks after later written
      → next after later
      → put after written)
    (tracks: Tracks place laid printed)
    (lays: StartLays indent place laid next):
    StartPuts indent place printed put :=
  match place, tracks, lays with
    | AtStart _ _ | Broken _ _, tracks, lays => onward _ _ _ tracks lays
    | Mid at carry, tracks, lays => onward _ _ _ (settlesTucks laid printed tracks) lays
    | Held at carry, tracks, lays => onward _ _ _ (waitsTucks laid printed tracks) lays

--| `SuffixLays` gives `SuffixPuts`, in the printer's own trace, given how the
--| traces track each other and that what follows carries over.
theorem Doc.Proofs.suffixLaysPuts ∀ (comment: Text) (place: Place) (laid printed: List Event)
    (next put: Place → List Event → Prop)
    (onward: ∀ (after: Place) (later written: List Event) => Tracks after later written
      → next after later
      → put after written)
    (tracks: Tracks place laid printed)
    (isComment: IsComment comment)
    (lays: SuffixLays comment place laid next):
    SuffixPuts comment place printed put :=
  match place, tracks, lays with
    | AtStart _ _ | Broken _ _, _, never => never
    | Mid at carry, tracks, lays => onward _ _ _ (settlesWaits laid printed comment tracks isComment) lays
    | Held at carry, _, never => never

--| `BlankLays` gives `BlankPuts`, in the printer's own trace, given how the
--| traces track each other and that what follows carries over.
theorem Doc.Proofs.blankLaysPuts ∀ (place: Place) (laid printed: List Event) (next put: Place → List Event → Prop)
    (onward: ∀ (after: Place) (later written: List Event) => Tracks after later written
      → next after later
      → put after written)
    (tracks: Tracks place laid printed)
    (lays: BlankLays place laid next):
    BlankPuts place printed put :=
  match place, tracks, lays with
    | AtStart at carry, _, never => never
    | Broken at carry, tracks, lays =>
      onward _ _ _ (settlesTucks _ _ (tucksSnoc laid printed Event.blankLine tracks (Inr byComputing))) lays
    | Mid _ _ | Held _ _, tracks, lays => onward _ _ _ tracks lays

--| What a document lays, the printer puts: from traces that track each
--| other, every way the document may print leaves traces that do. By
--| induction on the document; only a closer where a comment waits puts
--| its word elsewhere than it lays it (`waitsClose`).
theorem Doc.Proofs.laysPuts ∀ (doc: Doc) (indent: Nat) (place: Place) (laid printed: List Event)
    (next put: Place → List Event → Prop)
    (onward: ∀ (after: Place) (later written: List Event) => Tracks after later written
      → next after later
      → put after written)
    (tracks: Tracks place laid printed)
    (lays: Lays doc indent place laid next):
    Puts doc indent place printed put :=
  match doc, lays with
    | Doc.Nothing | BreakParent, lays => onward _ _ _ tracks lays
    | Blank, lays => blankLaysPuts place laid printed next put onward tracks lays
    | Chunk text width, lays => writeLaysPuts indent text place laid printed next put onward tracks lays
    | Closing text, lays => closeLaysPuts indent text place laid printed next put onward tracks lays
    | Line, lays => sepLaysPuts indent place laid printed next put onward tracks lays
    | SoftLine, lays => softLaysPuts indent place laid printed next put onward tracks lays
    | HardLine, Both mid (Inl broken) => (mid, (Inl (onward _ _ _ (tracksTucks place laid printed tracks) broken)))
    | HardLine, Both mid (Inr started) => (mid, (Inr (onward _ _ _ (tracksTucks place laid printed tracks) started)))
    | LineStart, lays => startLaysPuts indent place laid printed next put onward tracks lays
    | LineStartHere, lays => hereLaysPuts indent place laid printed next put onward tracks lays
    | Mark key, lays => onward _ _ _ (carryTracks place (place.carry.mark key place.indent) laid printed tracks) lays
    | CloserLine key, lays => onward _ _ _ (closerTracks place key indent laid printed tracks) lays
    | Nest more inner, lays => laysPuts inner (indent + more) place laid printed next put onward tracks lays
    | Align inner, lays =>
      match place, tracks, lays with
        | AtStart at carry, tracks, lays =>
          laysPuts inner indent (AtStart at carry) laid printed next put onward tracks lays
        | Broken at carry, tracks, lays =>
          laysPuts inner indent (Broken at carry) laid printed next put onward tracks lays
        | Mid at carry, tracks, lays => column =>
          laysPuts inner column (Mid at carry) laid printed next put onward tracks (lays column)
        | Held at carry, tracks, lays => column =>
          laysPuts inner column (Held at carry) laid printed next put onward tracks (lays column)
    | AlignInset inner, lays =>
      match place, tracks, lays with
        | AtStart at carry, tracks, lays =>
          laysPuts inner (indent + 2) (AtStart at carry) laid printed next put onward tracks lays
        | Broken at carry, tracks, lays =>
          laysPuts inner (indent + 2) (Broken at carry) laid printed next put onward tracks lays
        | Mid at carry, tracks, lays => column =>
          laysPuts inner column (Mid at carry) laid printed next put onward tracks (lays column)
        | Held at carry, tracks, lays => column =>
          laysPuts inner column (Held at carry) laid printed next put onward tracks (lays column)
    | Displaced inner, lays =>
      match place, tracks, lays with
        | AtStart at carry, tracks, lays =>
          laysPuts inner (Nat.max indent at) (AtStart at carry) laid printed next put onward tracks lays
        | Broken at carry, tracks, lays =>
          laysPuts inner (Nat.max indent at) (Broken at carry) laid printed next put onward tracks lays
        | Mid at carry, tracks, lays => laysPuts inner indent (Mid at carry) laid printed next put onward tracks lays
        | Held at carry, tracks, lays =>
          laysPuts inner
            (Nat.max indent (at + 2))
            (Broken (floored carry (Nat.max indent (at + 2))) (carry.breakTo (Nat.max indent (at + 2))))
            laid
            printed
            next
            put
            onward
            (waitsTucks laid printed tracks)
            lays
    | Group inner _ | NarrowGroup _ inner _ | IdGroup _ inner _, lays =>
      laysPuts inner indent place laid printed next put onward tracks lays
    | IfBroken id broken flat, Both brokenLays flatLays => (
      (laysPuts broken indent place laid printed next put onward tracks brokenLays),
      (laysPuts flat indent place laid printed next put onward tracks flatLays)
    )
    | Flatten inner, lays => laysPuts inner indent place laid printed next put onward tracks lays
    | OneLineBelow inner, Both mid lays => (
      mid,
      (laysPuts inner
        (indent + 2)
        (Broken (floored place.carry (indent + 2)) (place.carry.breakTo (indent + 2)))
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

--| `LaysAll` gives `PutsAll`, in the printer's own trace, given how the traces
--| track each other and that what follows carries over.
theorem Doc.Proofs.allLaysPuts ∀ (docs: List Doc) (indent: Nat) (place: Place) (laid printed: List Event)
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

--| `FillLays` gives `FillPuts`, in the printer's own trace, given how the
--| traces track each other and that what follows carries over.
theorem Doc.Proofs.fillLaysPuts ∀ (items: List Doc) (indent: Nat) (place: Place) (laid printed: List Event)
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

--| `SepsLay` gives `SepsPut`, in the printer's own trace, given how the traces
--| track each other and that what follows carries over.
theorem Doc.Proofs.sepsLayPuts ∀ (items: List Doc) (indent: Nat) (place: Place) (laid printed: List Event)
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

--| `OptionsLay` gives `OptionsPut`, in the printer's own trace, given how the
--| traces track each other and that what follows carries over.
theorem Doc.Proofs.optionsLayPuts ∀ (options: List Doc) (indent: Nat) (place: Place) (laid printed: List Event)
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
theorem Doc.Proofs.printLays ∀ (spec: Place → List Event → Prop) (doc: Doc) (width: Nat)
    (lays: Lays doc 0 (AtStart 0 Carry.none) [] spec):
    ∃ (place: Place) => ∃ (laid: List Event) => spec place laid
      ∧ Tucks laid (eventsOf (printedPieces doc width).reverse) :=
  let put: Place → List Event → Prop := place printed => ∃ (laid: List Event) => spec place laid ∧ Tucks laid printed
  let puts: Puts doc 0 (AtStart 0 Carry.none) [] put :=
    laysPuts doc 0
      (AtStart 0 Carry.none)
      []
      []
      spec
      put
      (after later written tracked holds => (later, holds, (tracksTucks after later written tracked)))
      (([], (), byComputing, byComputing, byComputing))
      lays
  match printPuts put doc width puts with | (place, laid, holds, tucks) => (place, laid, holds, tucks)

--| A `Blank` after a `Line` lays where the line breaks: `f`, a blank
--| line and `x`, or `f x` where it doesn't.
theorem Doc.Proofs.blankAfterLineExample ∀ (width: Nat):
    ∃ (place: Place) => ∃ (laid: List Event) => (laid = [{ word = "f", start = Some 0 }, { word = "x", start = None }]
      ∨ laid = [{ word = "f", start = Some 0 }, Event.blankLine, { word = "x", start = Some 0 }])
      ∧ Tucks laid (eventsOf (printedPieces (Concat [Chunk "f" 1, Line, Blank, Chunk "x" 1]) width).reverse) :=
  printLays
    (place laid =>
      laid = [{ word = "f", start = Some 0 }, { word = "x", start = None }]
        ∨ laid = [{ word = "f", start = Some 0 }, Event.blankLine, { word = "x", start = Some 0 }])
    (Concat [Chunk "f" 1, Line, Blank, Chunk "x" 1])
    width
    ((byComputing, ((byComputing, (Inl byComputing)), (byComputing, (Inr byComputing)))))
