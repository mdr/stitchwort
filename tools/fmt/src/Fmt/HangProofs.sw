--| The rules' half of `printedHangs` (docs/proposals/self-hosted-fmt-s1-sketch.md §1.4, ticket 18d): the words the
--| printer puts down for a slice 1 declaration keep the parser's line rule, `Fmt.hangs`.
--|
--| `hangs` is a fold of `HangState.step` over leaves. The printer's own account of where it puts each word is its
--| trace (`Doc.Proofs.Event`: a word and the column it starts its line at, if it does), and `HangState.step` reads
--| a leaf's column only when the leaf starts its line, so the same fold runs over the trace (`hangOf`), skipping
--| comments and blank lines, which aren't leaves. The rules prove triples over it (`HangLays kinds doc indent pre
--| post`: from every place and fold that satisfy `pre`, every way `doc` may lay out leaves a place and fold that
--| satisfy `post`), one per rule function, as `JoinProofs` does for the joins; `printLays` then takes the triple of a
--| declaration's document to the printed trace (`hangsPrinted`).

namespace Fmt.HangProofs
import Std (Bool, Char, DecEq, Doc, Eq, List, Nat, Option, Text, Void)
import Std.Doc (..)
import Std.Doc.Proofs (..)
import Syntax (Leaf, Tok)
import Fmt (..)

-- The fold over a trace.

--| An event the parser reads: no comment and no blank line.
def codeEvent (event: Event): Bool := !event.word.startsWith "--" && event.word != "\n"

--| The leaf `HangState.step` reads of an event: its kind, and where it starts its line, if it does.
def eventLeaf (kinds: Text → Tok) (event: Event): Leaf := {
  token = {
    kind = kinds event.word,
    text = event.word,
    column = event.start.getOrElse 0,
    lineStart = event.start.isSome
  },
  trivia = { leading = [], blankLines = 0, trailing = None }
}

--| Where the fold of `hangs` is in a declaration's trace: before its `def`, at a state, or broken.
type Hang = | Opening | At (state: HangState) | Broke

--| A code event: the declaration's `def` at column 0 first, then `HangState.step`.
def hangCode (kinds: Text → Tok) (hang: Hang) (event: Event): Hang := match hang with
  | Opening => if kinds event.word == KwDef && event.start == Some 0 then At HangState.initial else Broke
  | At state => Hang.ofStep (state.step (eventLeaf kinds event))
  | Broke => Broke

def Hang.ofStep: Option HangState → Hang
  | Some state => At state
  | None => Broke

def hangStep (kinds: Text → Tok) (hang: Hang) (event: Event): Hang :=
  if codeEvent event then hangCode kinds hang event else hang

--| The fold over a trace, from before the `def`.
def hangOf (kinds: Text → Tok) (trace: List Event): Hang := trace.foldLeft Opening (hangStep kinds)

theorem hangSnoc ∀ (kinds: Text → Tok) (trace: List Event) (event: Event):
    hangOf kinds (trace ++ [event]) = hangStep kinds (hangOf kinds trace) event :=
  List.foldLeftAppend trace Opening [event] (hangStep kinds)

theorem hangsFromSnoc ∀ (kinds: Text → Tok) (trace more: List Event) (hang: Hang):
    (trace ++ more).foldLeft hang (hangStep kinds)
      = more.foldLeft (trace.foldLeft hang (hangStep kinds)) (hangStep kinds) :=
  List.foldLeftAppend trace hang more (hangStep kinds)

--| A comment is skipped.
theorem commentSkips ∀ (kinds: Text → Tok) (hang: Hang) (event: Event)
    (comment: IsComment event.word):
    hangStep kinds hang event = hang :=
  match comment with
    | (others, chars, _) =>
      let starts: Text.startsWithChars "--".toList event.word.toList = True := rewrite chars
      let skipped: codeEvent event = False := rewrite starts
      rewrite skipped

theorem blankSkips ∀ (kinds: Text → Tok) (hang: Hang): hangStep kinds hang Event.blankLine = hang := byComputing

-- The laid order against the printed order.

--| The fold is the same over a stretch as the document has it and as it is printed: the comment is skipped.
theorem stretchesHang ∀ (kinds: Text → Tok) (stretches: List Stretch) (hang: Hang)
    (fits: List.All Stretch.Fits stretches):
    (laidOf stretches).foldLeft hang (hangStep kinds) = (printedOf stretches).foldLeft hang (hangStep kinds) :=
  match stretches, fits with
    | [], _ => byComputing
    | [Kept event, ..rest], (_, more) => stretchesHang kinds rest (hangStep kinds hang event) more
    | [Tucked comment closers, ..rest], ((_, isComment, _), more) =>
      calc (laidOf [Tucked comment closers, ..rest]).foldLeft hang (hangStep kinds)
        _ = (laidOf rest).foldLeft (closers.foldLeft (hangStep kinds hang comment) (hangStep kinds)) (hangStep kinds) :=
          hangsFromSnoc kinds closers (laidOf rest) (hangStep kinds hang comment)
        _ = (laidOf rest).foldLeft (closers.foldLeft hang (hangStep kinds)) (hangStep kinds) :=
          rewrite commentSkips kinds hang comment isComment
        _ = (printedOf rest).foldLeft (closers.foldLeft hang (hangStep kinds)) (hangStep kinds) :=
          stretchesHang kinds rest (closers.foldLeft hang (hangStep kinds)) more
        _ = (printedOf rest).foldLeft ((closers ++ [comment]).foldLeft hang (hangStep kinds)) (hangStep kinds) :=
          rewrite hangsFromSnoc kinds closers [comment] hang,
              commentSkips kinds (closers.foldLeft hang (hangStep kinds)) comment isComment
        _ = _ := Eq.flipped (hangsFromSnoc kinds (closers ++ [comment]) (printedOf rest) hang)

theorem tucksHang ∀ (kinds: Text → Tok) (laid printed: List Event)
    (tucks: Tucks laid printed):
    hangOf kinds laid = hangOf kinds printed :=
  match tucks with
    | (stretches, fits, _, laidIs, printedIs) =>
      rewrite laidIs, printedIs then stretchesHang kinds stretches Opening fits

-- The triples.

--| From every place and fold that satisfy `pre`, every way `doc` may lay out in a construct indented `indent`
--| leaves a place and fold that satisfy `post`.
def HangLays (kinds: Text → Tok) (doc: Doc) (indent: Nat) (pre post: Place → Hang → Prop): Prop :=
  ∀ (place: Place) (trace: List Event) (next: Place → List Event → Prop) => pre place (hangOf kinds trace)
    → (∀ (after: Place) (later: List Event) => post after (hangOf kinds later) → next after later)
    → Lays doc indent place trace next

def HangLaysAll (kinds: Text → Tok) (docs: List Doc) (indent: Nat) (pre post: Place → Hang → Prop): Prop :=
  ∀ (place: Place) (trace: List Event) (next: Place → List Event → Prop) => pre place (hangOf kinds trace)
    → (∀ (after: Place) (later: List Event) => post after (hangOf kinds later) → next after later)
    → LaysAll docs indent place trace next

--| A declaration's document that lays from the start of the output with the fold never broken prints words that
--| keep the line rule: the printed trace, comments put after the closers on their line, folds alike.
theorem hangsPrinted ∀ (kinds: Text → Tok) (doc: Doc) (width: Nat)
    (lays: HangLays kinds doc 0 (place hang => place = AtStart 0 Carry.none ∧ hang = Opening) (place hang =>
      hang ≠ Broke)):
    hangOf kinds (eventsOf (printedPieces doc width).reverse) ≠ Broke :=
  let spec: Place → List Event → Prop := place laid => hangOf kinds laid ≠ Broke
  let laid: Lays doc 0 (AtStart 0 Carry.none) [] spec :=
    lays (AtStart 0 Carry.none) [] spec (byComputing, byComputing) (after later holds => holds)
  match printLays spec doc width laid with
    | (place, laid, holds, tucks) =>
      rewrite (tucksHang kinds laid (eventsOf (printedPieces doc width).reverse) tucks).flipped then holds

theorem hangsFrom ∀ (kinds: Text → Tok) (doc: Doc) (indent: Nat) (pre weaker post: Place → Hang → Prop)
    (lays: HangLays kinds doc indent pre post)
    (implies: ∀ (place: Place) (hang: Hang) => weaker place hang → pre place hang):
    HangLays kinds doc indent weaker post :=
  place trace next holds after => lays place trace next (implies place (hangOf kinds trace) holds) after

theorem hangsTo ∀ (kinds: Text → Tok) (doc: Doc) (indent: Nat) (pre post weaker: Place → Hang → Prop)
    (lays: HangLays kinds doc indent pre post)
    (implies: ∀ (place: Place) (hang: Hang) => post place hang → weaker place hang):
    HangLays kinds doc indent pre weaker :=
  place trace next holds after =>
    lays place trace next holds (left later reached => after left later (implies left (hangOf kinds later) reached))

theorem allHangsFrom ∀ (kinds: Text → Tok) (docs: List Doc) (indent: Nat) (pre weaker post: Place → Hang → Prop)
    (lays: HangLaysAll kinds docs indent pre post)
    (implies: ∀ (place: Place) (hang: Hang) => weaker place hang → pre place hang):
    HangLaysAll kinds docs indent weaker post :=
  place trace next holds after => lays place trace next (implies place (hangOf kinds trace) holds) after

theorem allHangsTo ∀ (kinds: Text → Tok) (docs: List Doc) (indent: Nat) (pre post weaker: Place → Hang → Prop)
    (lays: HangLaysAll kinds docs indent pre post)
    (implies: ∀ (place: Place) (hang: Hang) => post place hang → weaker place hang):
    HangLaysAll kinds docs indent pre weaker :=
  place trace next holds after =>
    lays place trace next holds (left later reached => after left later (implies left (hangOf kinds later) reached))

theorem hangsNil ∀ (kinds: Text → Tok) (indent: Nat)
    (pre post: Place → Hang → Prop) (implies: ∀ (place: Place) (hang: Hang) => pre place hang → post place hang):
    HangLaysAll kinds [] indent pre post :=
  place trace next holds after => after place trace (implies place (hangOf kinds trace) holds)

theorem hangsCons ∀ (kinds: Text → Tok) (doc: Doc) (docs: List Doc) (indent: Nat) (pre middle post: Place → Hang → Prop)
    (first: HangLays kinds doc indent pre middle)
    (rest: HangLaysAll kinds docs indent middle post):
    HangLaysAll kinds [doc, ..docs] indent pre post :=
  place trace next holds after =>
    first place trace (between later => LaysAll docs indent between later next) holds (between later reached =>
      rest between later next reached after)

theorem hangsLast ∀ (kinds: Text → Tok) (doc: Doc) (indent: Nat) (pre post: Place → Hang → Prop)
    (only: HangLays kinds doc indent pre post):
    HangLaysAll kinds [doc] indent pre post :=
  hangsCons kinds doc [] indent pre post post only (hangsNil kinds indent post post (place hang holds => holds))

theorem hangsTwo ∀ (kinds: Text → Tok) (first second: Doc) (indent: Nat) (pre middle post: Place → Hang → Prop)
    (one: HangLays kinds first indent pre middle)
    (other: HangLays kinds second indent middle post):
    HangLaysAll kinds [first, second] indent pre post :=
  hangsCons kinds first [second] indent pre middle post one (hangsLast kinds second indent middle post other)

--| Documents one after another, then more: the first lot, then the second from where the first leaves off.
theorem laysAllAppend ∀ (front back: List Doc) (indent: Nat) (place: Place)
    (trace: List Event) (next: Place → List Event → Prop)
    (lays: LaysAll front indent place trace (between later => LaysAll back indent between later next)):
    LaysAll (front ++ back) indent place trace next :=
  match front, lays with
    | [], lays => lays
    | [doc, ..rest], lays =>
      laysWeaker doc indent place trace
        (between later => LaysAll rest indent between later (after more => LaysAll back indent after more next))
        (between later => LaysAll (rest ++ back) indent between later next)
        (between later reached => laysAllAppend rest back indent between later next reached)
        lays

theorem hangsAppend ∀ (kinds: Text → Tok) (front back: List Doc) (indent: Nat) (pre middle post: Place → Hang → Prop)
    (first: HangLaysAll kinds front indent pre middle)
    (second: HangLaysAll kinds back indent middle post):
    HangLaysAll kinds (front ++ back) indent pre post :=
  place trace next holds after =>
    laysAllAppend front back indent place trace next
      (first place trace (between later => LaysAll back indent between later next) holds (between later reached =>
        second between later next reached after))

theorem emptyLays ∀ (doc: Doc) (indent: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop)
    (empty: doc.isEmpty = True)
    (lays: Lays doc indent place trace next):
    next place trace :=
  match doc, empty, lays with | Doc.Nothing, _, lays => lays

theorem filterLays ∀ (docs: List Doc) (indent: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop)
    (lays: LaysAll docs indent place trace next):
    LaysAll (docs.filter (doc => not doc.isEmpty)) indent place trace next :=
  match docs, lays with
    | [], lays => lays
    | [doc, ..rest], lays =>
      match empty: doc.isEmpty with
        | True =>
          filterLays rest indent place trace next
            (emptyLays doc indent place trace (after later => LaysAll rest indent after later next) empty lays)
        | False =>
          laysWeaker doc indent place trace
            (after later => LaysAll rest indent after later next)
            (after later => LaysAll (rest.filter (doc => not doc.isEmpty)) indent after later next)
            (after later others => filterLays rest indent after later next others)
            lays

--| `Doc.concat` lays as the documents one after another.
theorem concatLays ∀ (docs: List Doc) (indent: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop)
    (lays: LaysAll docs indent place trace next):
    Lays (Doc.concat docs) indent place trace next :=
  let kept := filterLays docs indent place trace next lays
  match found: docs.filter (doc => not doc.isEmpty) with
    | [] => kept
    | [only] =>
      laysWeaker only indent place trace
        (after later => LaysAll [] indent after later next)
        next
        (after later reached => reached)
        kept
    | [first, second, ..rest] => kept

theorem hangsConcat ∀ (kinds: Text → Tok) (docs: List Doc) (indent: Nat) (pre post: Place → Hang → Prop)
    (each: HangLaysAll kinds docs indent pre post):
    HangLays kinds (Doc.concat docs) indent pre post :=
  place trace next holds after => concatLays docs indent place trace next (each place trace next holds after)

theorem hangsConcatOf ∀ (kinds: Text → Tok) (docs: List Doc) (indent: Nat) (pre post: Place → Hang → Prop)
    (each: HangLaysAll kinds docs indent pre post):
    HangLays kinds (Concat docs) indent pre post :=
  each

-- The document's constructors that put down no word.

theorem hangsNothing ∀ (kinds: Text → Tok) (indent: Nat) (pre: Place → Hang → Prop):
    HangLays kinds Doc.Nothing indent pre pre :=
  place trace next holds after => after place trace holds

theorem hangsBreakParent ∀ (kinds: Text → Tok) (indent: Nat) (pre: Place → Hang → Prop):
    HangLays kinds BreakParent indent pre pre :=
  place trace next holds after => after place trace holds

theorem hangsMark ∀ (kinds: Text → Tok) (key indent: Nat) (pre post: Place → Hang → Prop)
    (keeps: ∀ (place: Place) (hang: Hang) => pre place hang
      → post (place.withCarry (place.carry.mark key place.indent)) hang):
    HangLays kinds (Mark key) indent pre post :=
  place trace next holds after => after _ trace (keeps place (hangOf kinds trace) holds)

theorem hangsNest ∀ (kinds: Text → Tok) (more indent: Nat) (inner: Doc) (pre post: Place → Hang → Prop)
    (lays: HangLays kinds inner (indent + more) pre post):
    HangLays kinds (Nest more inner) indent pre post :=
  lays

theorem hangsGroup ∀ (kinds: Text → Tok) (inner: Doc) (hard: Bool) (indent: Nat) (pre post: Place → Hang → Prop)
    (lays: HangLays kinds inner indent pre post):
    HangLays kinds (Group inner hard) indent pre post :=
  lays

theorem hangsIdGroup ∀ (kinds: Text → Tok) (id: Nat) (inner: Doc) (hard: Bool)
    (indent: Nat) (pre post: Place → Hang → Prop)
    (lays: HangLays kinds inner indent pre post):
    HangLays kinds (IdGroup id inner hard) indent pre post :=
  lays

theorem hangsFlatten ∀ (kinds: Text → Tok) (inner: Doc) (indent: Nat) (pre post: Place → Hang → Prop)
    (lays: HangLays kinds inner indent pre post):
    HangLays kinds (Flatten inner) indent pre post :=
  lays

theorem hangsIfBroken ∀ (kinds: Text → Tok) (id: Nat) (broken flat: Doc) (indent: Nat) (pre post: Place → Hang → Prop)
    (brokenLays: HangLays kinds broken indent pre post)
    (flatLays: HangLays kinds flat indent pre post):
    HangLays kinds (IfBroken id broken flat) indent pre post :=
  place trace next holds after => (brokenLays place trace next holds after, flatLays place trace next holds after)

--| Each option of a choice, from the same places to the same places.
def EachHangs (kinds: Text → Tok) (indent: Nat) (pre post: Place → Hang → Prop): List Doc → Prop
  | [] => True
  | [option, ..others] => HangLays kinds option indent pre post ∧ EachHangs kinds indent pre post others

theorem optionsHang ∀ (kinds: Text → Tok) (options: List Doc) (indent: Nat) (pre post: Place → Hang → Prop)
    (each: EachHangs kinds indent pre post options)
    (keeps: ∀ (place: Place) (hang: Hang) => pre place hang → post place hang) (place: Place) (trace: List Event)
    (next: Place → List Event → Prop) (holds: pre place (hangOf kinds trace))
    (after: ∀ (left: Place) (later: List Event) => post left (hangOf kinds later) → next left later):
    OptionsLay options indent place trace next :=
  match options, each with
    | [], _ => after place trace (keeps place (hangOf kinds trace) holds)
    | [last], (lays, _) => lays place trace next holds after
    | [option, second, ..others], (lays, rest) => (
      lays place trace next holds after,
      optionsHang kinds [second, ..others] indent pre post rest keeps place trace next holds after
    )

--| A choice whose options all lay out, from places where doing nothing would too.
theorem hangsChoice ∀ (kinds: Text → Tok) (options: List Doc) (indent: Nat) (pre post: Place → Hang → Prop)
    (each: EachHangs kinds indent pre post options)
    (keeps: ∀ (place: Place) (hang: Hang) => pre place hang → post place hang):
    HangLays kinds (Choice options) indent pre post :=
  place trace next holds after => optionsHang kinds options indent pre post each keeps place trace next holds after

--| A `HardLine`, after words: to the start of a line at the indentation.
theorem hangsHard ∀ (kinds: Text → Tok) (indent: Nat) (pre post: Place → Hang → Prop)
    (moves: ∀ (place: Place) (hang: Hang) => pre place hang
      → place.midLine = True ∧ post (AtStart (floored place.carry indent) (place.carry.breakTo indent)) hang):
    HangLays kinds HardLine indent pre post :=
  place trace next holds after =>
    match moves place (hangOf kinds trace) holds with | (mid, started) => (mid, Inr (after _ trace started))

--| A `HardLine` a `Blank` may follow: right after the line break.
theorem hangsHardBroken ∀ (kinds: Text → Tok) (indent: Nat) (pre post: Place → Hang → Prop)
    (moves: ∀ (place: Place) (hang: Hang) => pre place hang
      → place.midLine = True ∧ post (Broken (floored place.carry indent) (place.carry.breakTo indent)) hang):
    HangLays kinds HardLine indent pre post :=
  place trace next holds after =>
    match moves place (hangOf kinds trace) holds with | (mid, broken) => (mid, Inl (after _ trace broken))

--| A `Blank`: a blank line after a line break, which the fold skips; nothing after words.
theorem hangsBlank ∀ (kinds: Text → Tok) (indent: Nat) (pre post: Place → Hang → Prop)
    (moves: ∀ (place: Place) (trace: List Event) => pre place (hangOf kinds trace)
      → BlankLays place trace (after later => post after (hangOf kinds later))):
    HangLays kinds Blank indent pre post :=
  place trace next holds after =>
    blankLaysWeaker place trace (left later => post left (hangOf kinds later)) next after (moves place trace holds)

--| The fold after a blank line is the fold before it.
theorem blankHang ∀ (kinds: Text → Tok) (trace: List Event):
    hangOf kinds (trace ++ [Event.blankLine]) = hangOf kinds trace :=
  rewrite hangSnoc kinds trace Event.blankLine then blankSkips kinds (hangOf kinds trace)

--| A `Line`: a space or a line break, after words.
theorem hangsLine ∀ (kinds: Text → Tok) (indent: Nat) (pre post: Place → Hang → Prop)
    (moves: ∀ (place: Place) (trace: List Event) => pre place (hangOf kinds trace)
      → SepLays indent place trace (after later => post after (hangOf kinds later))):
    HangLays kinds Line indent pre post :=
  place trace next holds after =>
    sepLaysWeaker indent place trace (left later => post left (hangOf kinds later)) next after (moves place trace holds)

--| A `SoftLine`: nothing or a line break, after words.
theorem hangsSoft ∀ (kinds: Text → Tok) (indent: Nat) (pre post: Place → Hang → Prop)
    (moves: ∀ (place: Place) (trace: List Event) => pre place (hangOf kinds trace)
      → SoftLays indent place trace (after later => post after (hangOf kinds later))):
    HangLays kinds SoftLine indent pre post :=
  place trace next holds after =>
    softLaysWeaker indent place trace
      (left later => post left (hangOf kinds later))
      next
      after
      (moves place trace holds)

--| A `LineStart`: a comment break, unless a line starts here.
theorem hangsStart ∀ (kinds: Text → Tok) (indent: Nat) (pre post: Place → Hang → Prop)
    (moves: ∀ (place: Place) (trace: List Event) => pre place (hangOf kinds trace)
      → StartLays indent place trace (after later => post after (hangOf kinds later))):
    HangLays kinds LineStart indent pre post :=
  place trace next holds after =>
    startLaysWeaker indent place trace
      (left later => post left (hangOf kinds later))
      next
      after
      (moves place trace holds)

--| A `LineStartHere`: a line at the indentation, unless a line starts here.
theorem hangsStartHere ∀ (kinds: Text → Tok) (indent: Nat) (pre post: Place → Hang → Prop)
    (moves: ∀ (place: Place) (trace: List Event) => pre place (hangOf kinds trace)
      → HerePuts indent place trace (after later => post after (hangOf kinds later))):
    HangLays kinds LineStartHere indent pre post :=
  place trace next holds after =>
    herePutsWeaker indent place trace
      (left later => post left (hangOf kinds later))
      next
      after
      (moves place trace holds)

--| A `CloserLine`: a line break after words, to where the open marks put the closer.
theorem hangsCloserLine ∀ (kinds: Text → Tok) (key indent: Nat) (pre post: Place → Hang → Prop)
    (moves: ∀ (place: Place) (hang: Hang) => pre place hang
      → place.midLine = True
        ∧ post
          (AtStart
            (place.carry.closerAt key indent)
            ((place.carry.close key).breakTo (place.carry.closerAt key indent)))
          hang):
    HangLays kinds (CloserLine key) indent pre post :=
  place trace next holds after =>
    match moves place (hangOf kinds trace) holds with | (mid, reached) => (mid, after _ trace reached)

theorem hangsDisplaced ∀ (kinds: Text → Tok) (inner: Doc) (indent: Nat)
    (pre post: Place → Hang → Prop) (seat: Nat → Place → Hang → Prop)
    (lays: ∀ (column: Nat) => HangLays kinds inner column (seat column) post)
    (moves: ∀ (place: Place) (hang: Hang) => pre place hang
      → DisplacedHolds indent place (column start => seat column start hang)):
    HangLays kinds (Displaced inner) indent pre post :=
  place trace next holds after =>
    match place, moves place (hangOf kinds trace) holds with
      | AtStart at carry, seated => lays _ (AtStart at carry) trace next seated after
      | Broken at carry, seated => lays _ (Broken at carry) trace next seated after
      | Mid at carry, seated => lays _ (Mid at carry) trace next seated after
      | Held at carry, seated => lays _ _ trace next seated after

--| A `OneLineBelow`: after words, its contents start a line at 2 deeper.
theorem hangsOneLineBelow ∀ (kinds: Text → Tok) (inner: Doc) (indent: Nat) (pre below post: Place → Hang → Prop)
    (lays: HangLays kinds inner (indent + 2) below post)
    (moves: ∀ (place: Place) (hang: Hang) => pre place hang
      → place.midLine = True
        ∧ below (AtStart (floored place.carry (indent + 2)) (place.carry.breakTo (indent + 2))) hang):
    HangLays kinds (OneLineBelow inner) indent pre post :=
  place trace next holds after =>
    match moves place (hangOf kinds trace) holds with | (mid, started) => (mid, lays _ trace next started after)

--| The separators and items after a fill's first item: a separator from where an item ends, then the item.
def SepsHang (kinds: Text → Tok) (indent: Nat) (gap ended: Place → Hang → Prop): List Doc → Prop
  | [] => True
  | [item, ..more] => HangLays kinds item indent gap ended ∧ SepsHang kinds indent gap ended more

theorem sepsHang ∀ (kinds: Text → Tok) (items: List Doc) (indent: Nat) (gap ended: Place → Hang → Prop)
    (each: SepsHang kinds indent gap ended items)
    (separates: ∀ (place: Place) (trace: List Event) => ended place (hangOf kinds trace)
      → SepLays indent place trace (after later => gap after (hangOf kinds later)))
    (place: Place) (trace: List Event) (next: Place → List Event → Prop) (holds: ended place (hangOf kinds trace))
    (after: ∀ (left: Place) (later: List Event) => ended left (hangOf kinds later) → next left later):
    SepsLay items indent place trace next :=
  match items, each with
    | [], _ => after place trace holds
    | [item, ..more], (lays, rest) =>
      sepLaysWeaker indent place trace
        (middle between => gap middle (hangOf kinds between))
        (middle between => Lays item indent middle between (left later => SepsLay more indent left later next))
        (middle between spaced =>
          lays middle between (left later => SepsLay more indent left later next) spaced (left later reached =>
            sepsHang kinds more indent gap ended rest separates left later next reached after))
        (separates place trace holds)

--| A fill: its first item, then each later one after a space or a line break.
theorem hangsFill ∀ (kinds: Text → Tok) (first: Doc) (others: List Doc)
    (indent: Nat) (pre gap ended: Place → Hang → Prop)
    (lays: HangLays kinds first indent pre ended)
    (each: SepsHang kinds indent gap ended others)
    (separates: ∀ (place: Place) (trace: List Event) => ended place (hangOf kinds trace)
      → SepLays indent place trace (after later => gap after (hangOf kinds later))):
    HangLays kinds (Fill [first, ..others]) indent pre ended :=
  place trace next holds after =>
    lays place trace (left later => SepsLay others indent left later next) holds (left later reached =>
      sepsHang kinds others indent gap ended each separates left later next reached after)

-- Words.

--| Where a word written at `place` starts its line, if it does: at the line's indentation if nothing is on the
--| line, and on a new line, a comment break, after a waiting comment.
def wordStart (indent: Nat) (place: Place): Option Nat := match place with
  | AtStart at _ => Some at
  | Broken at _ => Some at
  | Mid _ _ => None
  | Held at carry => Some (floored carry (Nat.max indent (at + 2)))

--| Where the printer is after the word `text`.
def wordAfter (indent: Nat) (text: Text) (place: Place): Place := match place with
  | AtStart at carry => Mid at (floorAfter text carry)
  | Broken at carry => Mid at (floorAfter text carry)
  | Mid at carry => Mid at (floorAfter text carry)
  | Held at carry =>
    Mid (floored carry (Nat.max indent (at + 2))) (floorAfter text (carry.breakTo (Nat.max indent (at + 2))))

theorem solidSpaces ∀ (text: Text) (solid: isLayout text = False): text.all (char => char == ' ') = False :=
  match spaces: text.all (char => char == ' ') with | False => byComputing

theorem solidLine ∀ (text: Text) (solid: isLayout text = False): (text == "\n") = False :=
  Bool.orFalseRight (text.all (char => char == ' ')) (text == "\n") solid

--| A word is one event, where the place says.
theorem writeOne ∀ (indent: Nat) (text: Text) (place: Place) (trace: List Event) (next: Place → List Event → Prop)
    (solid: isLayout text = False)
    (reached: next (wordAfter indent text place) (trace ++ [{ word = text, start = wordStart indent place }])):
    WriteLays indent text place trace next :=
  rewrite wordFilled text solid, solidSpaces text solid then
    (
      solidLine text solid,
      match place, reached with
        | AtStart at carry, reached => reached
        | Broken at carry, reached => reached
        | Mid at carry, reached => reached
        | Held at carry, reached => reached
    )

theorem hangsChunk ∀ (kinds: Text → Tok) (text: Text) (width indent: Nat) (pre post: Place → Hang → Prop)
    (solid: isLayout text = False)
    (moves: ∀ (place: Place) (trace: List Event) => pre place (hangOf kinds trace)
      → post
        (wordAfter indent text place)
        (hangStep kinds (hangOf kinds trace) { word = text, start = wordStart indent place })):
    HangLays kinds (Chunk text width) indent pre post :=
  place trace next holds after =>
    writeOne indent text place trace next solid
      (after _ _
        (rewrite hangSnoc kinds trace { word = text, start = wordStart indent place } then moves place trace holds))

--| Where a closer or comma written at `place` starts its line: on a waiting comment's line, it doesn't.
def closeStart (indent: Nat) (place: Place): Option Nat := match place with
  | Held _ _ => None
  | other => wordStart indent other

def closeAfter (indent: Nat) (text: Text) (place: Place): Place := match place with
  | Held at carry => Held at (floorAfter text carry)
  | other => wordAfter indent text other

theorem hangsClosing ∀ (kinds: Text → Tok) (text: Text) (indent: Nat) (pre post: Place → Hang → Prop)
    (solid: isLayout text = False)
    (closes: closesText text = True)
    (moves: ∀ (place: Place) (trace: List Event) => pre place (hangOf kinds trace)
      → post
        (closeAfter indent text place)
        (hangStep kinds (hangOf kinds trace) { word = text, start = closeStart indent place })):
    HangLays kinds (Closing text) indent pre post :=
  place trace next holds after =>
    let reached: next (closeAfter indent text place) (trace ++ [{ word = text, start = closeStart indent place }]) :=
      after _ _
        (rewrite hangSnoc kinds trace { word = text, start = closeStart indent place } then moves place trace holds)
    match place, reached with
      | AtStart at carry, reached => writeOne indent text (AtStart at carry) trace next solid reached
      | Broken at carry, reached => writeOne indent text (Broken at carry) trace next solid reached
      | Mid at carry, reached => writeOne indent text (Mid at carry) trace next solid reached
      | Held at carry, reached => (closes, reached)

--| A trailing comment, after words on its line: the fold skips it.
theorem hangsSuffix ∀ (kinds: Text → Tok) (comment: Text) (indent: Nat) (pre post: Place → Hang → Prop)
    (isComment: IsComment comment)
    (solid: isLayout comment = False)
    (moves: ∀ (place: Place) (hang: Hang) => pre place hang
      → ∃ (at: Nat) => ∃ (carry: Carry) => place = Mid at carry ∧ post (Held at carry) hang):
    HangLays kinds (LineSuffix comment) indent pre post :=
  place trace next holds after =>
    match moves place (hangOf kinds trace) holds with
      | (at, carry, (isMid, reached)) =>
        let skipped: hangOf kinds (trace ++ [{ word = comment, start = None }]) = hangOf kinds trace :=
          rewrite hangSnoc kinds trace { word = comment, start = None } then
            commentSkips kinds (hangOf kinds trace) { word = comment, start = None } isComment
        (isComment, solid, rewrite isMid then after (Held at carry) _ (rewrite skipped then reached))

-- Steps of the fold.

--| A token kind the fold takes as it takes a name: no bracket, comma, `:`, `:=` or `->`.
def Plain (kind: Tok): Prop :=
  kind.isCloser = False
    ∧ kind.isOpener = False
    ∧ (kind == Comma) = False
    ∧ (kind == ColonEq) = False
    ∧ (kind == Colon) = False
    ∧ (kind == Arrow) = False

--| A word may start its line at `start`, if it does: not after `->`, and right of the block column in force.
def Room (state: HangState) (start: Option Nat): Prop := match start with
  | None => True
  | Some column => state.glue = False ∧ (column > inForce state.blocks state.top) = True

--| The fold after one plain token, or an element whose brackets are closed again, whose first token starts its
--| line at `start`, if it does: that column is the block's if the token starts an item, the type or the body.
def openedBy (state: HangState) (start: Option Nat): HangState :=
  state.past (start.getOrElse 0) (state.start && start.isSome) False False

theorem stepPlain ∀ (kinds: Text → Tok) (state: HangState) (word: Text) (start: Option Nat)
    (code: codeEvent { word, start } = True)
    (plain: Plain (kinds word))
    (room: Room state start):
    hangStep kinds (At state) { word, start } = At (openedBy state start) :=
  match plain with
    | (closer, opener, comma, assign, colon, arrow) =>
      match start, room with
        | None, _ =>
          rewrite code, Bool.andFalse state.glue, closer, comma, assign, colon, opener, arrow, Bool.andFalse state.start
        | Some column, (unglued, right) =>
          rewrite code, unglued, closer, comma, assign, right, colon, opener, arrow, Bool.andTrue state.start

--| An opening bracket: as a plain token, then a block of its own whose first item starts next.
def openingBy (state: HangState) (start: Option Nat): HangState :=
  state.past (start.getOrElse 0) (state.start && start.isSome) True False

theorem stepOpener ∀ (kinds: Text → Tok) (state: HangState) (word: Text) (start: Option Nat)
    (code: codeEvent { word, start } = True)
    (opener: (kinds word).isOpener = True)
    (closer: (kinds word).isCloser = False)
    (comma: (kinds word == Comma) = False)
    (assign: (kinds word == ColonEq) = False)
    (colon: (kinds word == Colon) = False)
    (arrow: (kinds word == Arrow) = False)
    (room: Room state start):
    hangStep kinds (At state) { word, start } = At (openingBy state start) :=
  match start, room with
    | None, _ =>
      rewrite code, Bool.andFalse state.glue, closer, comma, assign, colon, opener, arrow, Bool.andFalse state.start
    | Some column, (unglued, right) =>
      rewrite code, unglued, closer, comma, assign, right, colon, opener, arrow, Bool.andTrue state.start

--| `->`: as a plain token, and the next token must not start a line.
def gluedBy (state: HangState) (start: Option Nat): HangState :=
  state.past (start.getOrElse 0) (state.start && start.isSome) False True

theorem stepArrow ∀ (kinds: Text → Tok) (state: HangState) (word: Text) (start: Option Nat)
    (code: codeEvent { word, start } = True)
    (arrow: kinds word = Arrow)
    (room: Room state start):
    hangStep kinds (At state) { word, start } = At (gluedBy state start) :=
  match start, room with
    | None, _ => rewrite code, Bool.andFalse state.glue, arrow, Bool.andFalse state.start
    | Some column, (unglued, right) => rewrite code, unglued, arrow, right, Bool.andTrue state.start

--| A closer that starts its line at `start`, if it does, may: not after `->`, and left of the column its bracket's
--| current item started a line at.
def CloserRoom (state: HangState) (block start: Option Nat): Prop := match start with
  | None => True
  | Some column => state.glue = False ∧ leftOf column block = True

--| The fold after a closer: its bracket's block is gone.
def closedFrom (state: HangState) (outer: List (Option Nat)): HangState :=
  { blocks = outer, top = state.top, start = False, glue = False }

theorem stepCloser ∀ (kinds: Text → Tok) (state: HangState) (block: Option Nat) (outer: List (Option Nat))
    (word: Text) (start: Option Nat)
    (code: codeEvent { word, start } = True)
    (closer: (kinds word).isCloser = True)
    (open: state.blocks = [block, ..outer])
    (room: CloserRoom state block start):
    hangStep kinds (At state) { word, start } = At (closedFrom state outer) :=
  match start, room with
    | None, _ => rewrite code, Bool.andFalse state.glue, closer, open
    | Some column, (unglued, left) => rewrite code, unglued, closer, open, left

--| The fold after a comma: the bracket's next item starts.
def commaFrom (state: HangState) (outer: List (Option Nat)): HangState :=
  { blocks = [None, ..outer], top = state.top, start = True, glue = False }

theorem stepComma ∀ (kinds: Text → Tok) (state: HangState) (block: Option Nat) (outer: List (Option Nat)) (word: Text)
    (code: codeEvent { word, start = None } = True)
    (comma: kinds word = Comma)
    (open: state.blocks = [block, ..outer]):
    hangStep kinds (At state) { word, start = None } = At (commaFrom state outer) :=
  rewrite code, Bool.andFalse state.glue, comma, open

--| The fold after the header's `:` or `:=`: the type or the body starts.
def topFrom: HangState := { blocks = [], top = None, start = True, glue = False }

theorem stepColon ∀ (kinds: Text → Tok) (state: HangState) (word: Text) (start: Option Nat)
    (code: codeEvent { word, start } = True)
    (colon: kinds word = Colon)
    (top: state.blocks = [])
    (room: Room state start):
    hangStep kinds (At state) { word, start } = At topFrom :=
  match start, room with
    | None, _ => rewrite code, Bool.andFalse state.glue, colon, top
    | Some column, (unglued, right) => rewrite code, unglued, colon, right, top

theorem stepAssign ∀ (kinds: Text → Tok) (state: HangState) (word: Text) (start: Option Nat)
    (code: codeEvent { word, start } = True)
    (assign: kinds word = ColonEq)
    (top: state.blocks = [])
    (unglued: start.isSome = True → state.glue = False):
    hangStep kinds (At state) { word, start } = At topFrom :=
  match start with
    | None => rewrite code, Bool.andFalse state.glue, assign, top
    | Some column => rewrite code, unglued byComputing, assign, top

--| A token's text is code: not a comment and not a line break.
theorem tokenCode ∀ (text: Text) (start: Option Nat)
    (token: text.startsWith "--" = False)
    (solid: isLayout text = False):
    codeEvent { word = text, start } = True :=
  rewrite token, solidLine text solid
