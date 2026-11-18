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
import Syntax (Expr, Leaf, Note, Tok, Word)
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

theorem hangsPre ∀ (kinds: Text → Tok) (doc: Doc) (indent: Nat) (pre weaker post: Place → Hang → Prop)
    (lays: HangLays kinds doc indent pre post)
    (implies: ∀ (place: Place) (hang: Hang) => weaker place hang → pre place hang):
    HangLays kinds doc indent weaker post :=
  place trace next holds after => lays place trace next (implies place (hangOf kinds trace) holds) after

theorem hangsPost ∀ (kinds: Text → Tok) (doc: Doc) (indent: Nat) (pre post weaker: Place → Hang → Prop)
    (lays: HangLays kinds doc indent pre post)
    (implies: ∀ (place: Place) (hang: Hang) => post place hang → weaker place hang):
    HangLays kinds doc indent pre weaker :=
  place trace next holds after =>
    lays place trace next holds (left later reached => after left later (implies left (hangOf kinds later) reached))

theorem allHangsPre ∀ (kinds: Text → Tok) (docs: List Doc) (indent: Nat) (pre weaker post: Place → Hang → Prop)
    (lays: HangLaysAll kinds docs indent pre post)
    (implies: ∀ (place: Place) (hang: Hang) => weaker place hang → pre place hang):
    HangLaysAll kinds docs indent weaker post :=
  place trace next holds after => lays place trace next (implies place (hangOf kinds trace) holds) after

theorem allHangsPost ∀ (kinds: Text → Tok) (docs: List Doc) (indent: Nat) (pre post weaker: Place → Hang → Prop)
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
          (Broken (place.carry.closerAt key indent) ((place.carry.close key).breakTo (place.carry.closerAt key indent)))
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
        ∧ below (Broken (floored place.carry (indent + 2)) (place.carry.breakTo (indent + 2))) hang):
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

-- Elements.

--| Where an element may start in a construct indented `indent`: at the start of a line at the indentation (a
--| comment floor no deeper), mid-line, or after a waiting comment only if the code before ends its line with one
--| (`before`); mid-line no comment floor, and nothing in force right of the line's indentation, so a comment break
--| is right of it.
def Seated (indent: Nat) (before: Bool) (state: HangState) (place: Place): Prop := match place with
  | AtStart at carry => at = indent ∧ floored carry indent = indent
  | Broken at carry => at = indent ∧ floored carry indent = indent
  | Mid at carry => carry.floor = None ∧ (inForce state.blocks state.top <= at) = True
  | Held at carry => before = True ∧ carry.floor = None ∧ (inForce state.blocks state.top <= at) = True

--| Where an element ends: after words, a trailing comment waiting only if it ends with one (`trails`), no comment
--| floor, and nothing in force right of the line's indentation.
def Ended (state: HangState) (trails: Bool) (place: Place): Prop := match place with
  | AtStart _ _ => False
  | Broken _ _ => False
  | Mid at carry => carry.floor = None ∧ (inForce state.blocks state.top <= at) = True
  | Held at carry => trails = True ∧ carry.floor = None ∧ (inForce state.blocks state.top <= at) = True

--| What the fold must allow where an element starts: nothing in force right of the construct's indentation (its
--| later lines are right of it), and room for its first word to start a line at `first`, if it does.
def Seat (indent: Nat) (before: Bool) (state: HangState) (entry: Place) (first: Option Nat): Prop :=
  Seated indent before state entry ∧ (inForce state.blocks state.top <= indent) = True ∧ Room state first

--| At the element's entry, with the fold at `state` and a seat there.
def Entered (indent: Nat) (before: Bool) (state: HangState) (entry: Place) (first: Option Nat): Place → Hang → Prop :=
  place hang => place = entry ∧ hang = At state ∧ Seat indent before state entry first

--| `doc` is one element that folds as one plain token: from a seat in a construct indented `indent`, its first word
--| written where `start` says, it ends after words with the fold as after that one token.
def ElHangs (kinds: Text → Tok) (doc: Doc) (indent: Nat) (before trails: Bool) (start: Nat → Place → Option Nat):
    Prop :=
  ∀ (state: HangState) (entry: Place) => HangLays kinds doc indent
    (Entered indent before state entry (start indent entry))
    (place hang =>
      Ended (openedBy state (start indent entry)) trails place ∧ hang = At (openedBy state (start indent entry)))

theorem floorAfterToken ∀ (text: Text) (carry: Carry)
    (token: text.startsWith "--" = False):
    (floorAfter text carry).floor = None :=
  rewrite token

theorem staleBlocks ∀ (column: Nat) (blocks: List (Option Nat)): startBlocks False column blocks = blocks :=
  match blocks with
    | [] => byComputing
    | [block, ..outer] => byComputing

--| After an element that starts no line, what is in force is what was.
theorem openedNone ∀ (state: HangState):
    inForce (openedBy state None).blocks (openedBy state None).top = inForce state.blocks state.top :=
  rewrite Bool.andFalse state.start, staleBlocks 0 state.blocks

--| After an element that starts a line at `column`, nothing is in force right of it.
theorem openedSome ∀ (state: HangState) (column: Nat)
    (left: (inForce state.blocks state.top <= column) = True):
    (inForce (openedBy state (Some column)).blocks (openedBy state (Some column)).top <= column) = True :=
  match state, left with
    | { blocks, top, start = False, glue }, left => rewrite staleBlocks column blocks then left
    | { blocks = [], top, start = True, glue }, _ => rewrite Nat.leRefl column
    | { blocks = [block, ..outer], top, start = True, glue }, _ => rewrite Nat.leRefl column

--| After a word written at a seat, nothing is in force right of the line's indentation.
--|
--| Proof idea: mid-line the fold doesn't move; at a line start, or on the comment break after a waiting comment,
--| the word starts the line, right of what is in force, and is the most the fold can put in force (`openedSome`).
theorem wordEnded ∀ (indent: Nat) (before: Bool) (text: Text) (state: HangState) (place: Place)
    (token: text.startsWith "--" = False)
    (seated: Seated indent before state place)
    (room: Room state (wordStart indent place)):
    Ended (openedBy state (wordStart indent place)) False (wordAfter indent text place) :=
  match place, seated, room with
    | AtStart at carry, (_, _), (_, right) => (floorAfterToken text carry token, openedSome state at arithmetic)
    | Broken at carry, (_, _), (_, right) => (floorAfterToken text carry token, openedSome state at arithmetic)
    | Mid at carry, (_, left), _ => (floorAfterToken text carry token, rewrite openedNone state then left)
    | Held at carry, (_, _, _), (_, right) => (
      floorAfterToken text (carry.breakTo (Nat.max indent (at + 2))) token,
      openedSome state (floored carry (Nat.max indent (at + 2))) arithmetic
    )

--| A plain token's text, written where the place says, folds as one plain token, and leaves the printer after it.
theorem plainStep ∀ (kinds: Text → Tok) (text: Text) (indent: Nat) (before: Bool) (state: HangState) (entry: Place)
    (plain: Plain (kinds text))
    (token: text.startsWith "--" = False)
    (solid: isLayout text = False):
    HangLays kinds (Doc.text text) indent (Entered indent before state entry (wordStart indent entry)) (place hang =>
      place = wordAfter indent text entry
        ∧ Ended (openedBy state (wordStart indent entry)) False place
        ∧ hang = At (openedBy state (wordStart indent entry))) :=
  hangsChunk kinds text text.length indent
    (Entered indent before state entry (wordStart indent entry))
    (place hang =>
      place = wordAfter indent text entry
        ∧ Ended (openedBy state (wordStart indent entry)) False place
        ∧ hang = At (openedBy state (wordStart indent entry)))
    solid
    (place trace (isEntry, hang, seat) =>
      match seat with
        | (seated, _, room) =>
          rewrite isEntry, hang then
            (
              byComputing,
              wordEnded indent before text state entry token seated room,
              stepPlain kinds state text
                (wordStart indent entry)
                (tokenCode text (wordStart indent entry) token solid)
                plain
                room
            ))

theorem plainHangs ∀ (kinds: Text → Tok) (text: Text) (indent: Nat) (before: Bool)
    (plain: Plain (kinds text))
    (token: text.startsWith "--" = False)
    (solid: isLayout text = False):
    ElHangs kinds (Doc.text text) indent before False wordStart :=
  state entry =>
    hangsPost kinds
      (Doc.text text)
      indent
      (Entered indent before state entry (wordStart indent entry))
      (place hang =>
        place = wordAfter indent text entry
          ∧ Ended (openedBy state (wordStart indent entry)) False place
          ∧ hang = At (openedBy state (wordStart indent entry)))
      (place hang =>
        Ended (openedBy state (wordStart indent entry)) False place
          ∧ hang = At (openedBy state (wordStart indent entry)))
      (plainStep kinds text indent before state entry plain token solid)
      (place hang (_, ended, folded) => (ended, folded))

--| After a word the printer is mid-line.
theorem wordAfterMid ∀ (indent: Nat) (text: Text) (place: Place):
    ∃ (at: Nat) => ∃ (carry: Carry) => wordAfter indent text place = Mid at carry :=
  match place with
    | AtStart at carry => (at, floorAfter text carry, byComputing)
    | Broken at carry => (at, floorAfter text carry, byComputing)
    | Mid at carry => (at, floorAfter text carry, byComputing)
    | Held at carry =>
      (floored carry (Nat.max indent (at + 2)), floorAfter text (carry.breakTo (Nat.max indent (at + 2))), byComputing)

--| A word's trailing comment, if it has one, is one the lexer reads as a comment.
def TrailsComment (word: Word): Prop := match word.comments.after with
  | Some comment => IsComment comment ∧ isLayout comment = False
  | None => True

theorem leafIsText ∀ (word: Word) (around: Around) (key: Nat)
    (closer: isCloserText word.text = False)
    (comma: (word.text == ",") = False)
    (bare: word.leading around key = []):
    word.leaf around key = Doc.concat ([Doc.text word.text] ++ word.trailing) :=
  rewrite bare, closer, comma

--| A plain token on its own, its own-line comments written elsewhere or none: one plain token, then its trailing
--| comment, if any.
theorem plainLeafHangs ∀ (kinds: Text → Tok) (word: Word) (around: Around) (key indent: Nat)
    (plain: Plain (kinds word.text))
    (token: word.text.startsWith "--" = False)
    (solid: isLayout word.text = False)
    (closer: isCloserText word.text = False)
    (comma: (word.text == ",") = False)
    (bare: word.leading around key = [])
    (trails: TrailsComment word):
    ElHangs kinds (word.leaf around key) indent around.before word.trails wordStart :=
  state entry =>
    let step := plainStep kinds word.text indent around.before state entry plain token solid
    let pre := Entered indent around.before state entry (wordStart indent entry)
    let opened := openedBy state (wordStart indent entry)
    let mid: Place → Hang → Prop := place hang =>
      place = wordAfter indent word.text entry ∧ Ended opened False place ∧ hang = At opened
    let post: Bool → Place → Hang → Prop := flag place hang => Ended opened flag place ∧ hang = At opened
    let mids: ∀ (place: Place) => place = wordAfter indent word.text entry
      → ∃ (at: Nat) => ∃ (carry: Carry) => place = Mid at carry :=
      place isAfter =>
        match wordAfterMid indent word.text entry with
          | (at, carry, written) => (at, carry, rewrite isAfter then written)
    rewrite leafIsText word around key closer comma bare then
      match after: word.comments.after, trails with
        | None, _ =>
          hangsConcat kinds
            [Doc.text word.text]
            indent
            pre
            (post False)
            (hangsLast kinds
              (Doc.text word.text)
              indent
              pre
              (post False)
              (hangsPost kinds (Doc.text word.text) indent pre mid (post False) step (place hang (_, ended, folded) =>
                (ended, folded))))
        | Some comment, (isComment, layout) =>
          hangsConcat kinds
            [Doc.text word.text, LineSuffix comment]
            indent
            pre
            (post True)
            (hangsTwo kinds
              (Doc.text word.text)
              (LineSuffix comment)
              indent
              pre
              mid
              (post True)
              step
              (hangsSuffix kinds comment indent mid (post True) isComment layout (place hang (isAfter, ended, folded) =>
                match mids place isAfter with
                  | (at, carry, isMid) =>
                    match carry, rewrite isMid at ended then ended with
                      | carry, (floor, left) => (at, carry, (isMid, (byComputing, floor, left), folded)))))

--| With no item, type or body starting and nothing glued, an element leaves the fold as it found it.
theorem openedQuiet ∀ (state: HangState) (start: Option Nat)
    (quiet: state.start = False)
    (unglued: state.glue = False):
    openedBy state start = state :=
  match state, quiet, unglued with
    | { blocks = [], top, start = False, glue = False }, _, _ => byComputing
    | { blocks = [block, ..outer], top, start = False, glue = False }, _, _ => byComputing

--| `doc`, a later part of an element, after words, folds back to where it started: from where an element ended
--| (a comment waiting only if `before`), with nothing in force right of the construct's indentation and no item,
--| type or body starting, it ends after words with the fold unchanged.
def PartHangs (kinds: Text → Tok) (doc: Doc) (indent: Nat) (before trails: Bool): Prop :=
  ∀ (state: HangState) (entry: Place) => state.start = False
    → state.glue = False
    → HangLays kinds doc indent
      (place hang =>
        place = entry ∧ hang = At state ∧ Ended state before entry ∧ (inForce state.blocks state.top <= indent) = True)
      (place hang => Ended state trails place ∧ hang = At state)

--| Where an element ended, another may start: mid-line, or on the comment break after the waiting comment, right of
--| the line, so with room for its first word but for `->`'s glue.
theorem endedSeat ∀ (indent: Nat) (before: Bool) (state: HangState) (place: Place)
    (unglued: state.glue = False)
    (ended: Ended state before place)
    (clear: (inForce state.blocks state.top <= indent) = True):
    Seat indent before state place (wordStart indent place) :=
  match place, ended with
    | Mid at carry, ended => (ended, clear, byComputing)
    | Held at carry, (trails, floor, left) =>
      let landed: floored carry (Nat.max indent (at + 2)) = Nat.max indent (at + 2) := rewrite floor
      ((trails, floor, left), clear, (unglued, rewrite landed then arithmetic))

--| The fold after an element starts nothing and glues nothing.
theorem openedQuietStart ∀ (state: HangState) (start: Option Nat): (openedBy state start).start = False := byComputing

theorem openedUnglued ∀ (state: HangState) (start: Option Nat): (openedBy state start).glue = False := byComputing

--| An element after words is a part.
theorem elPart ∀ (kinds: Text → Tok) (doc: Doc) (indent: Nat) (before trails: Bool)
    (el: ElHangs kinds doc indent before trails wordStart):
    PartHangs kinds doc indent before trails :=
  state entry quiet unglued =>
    let pre: Place → Hang → Prop := place hang =>
      place = entry ∧ hang = At state ∧ Ended state before entry ∧ (inForce state.blocks state.top <= indent) = True
    let opened := openedBy state (wordStart indent entry)
    hangsPost kinds doc indent pre
      (place hang => Ended opened trails place ∧ hang = At opened)
      (place hang => Ended state trails place ∧ hang = At state)
      (hangsPre kinds doc indent
        (Entered indent before state entry (wordStart indent entry))
        pre
        (place hang => Ended opened trails place ∧ hang = At opened)
        (el state entry)
        (place hang (isEntry, folded, ended, clear) =>
          (isEntry, folded, endedSeat indent before state entry unglued ended clear)))
      (place hang (ended, folded) =>
        let same: opened = state := openedQuiet state (wordStart indent entry) quiet unglued
        (rewrite same at ended then ended, rewrite same at folded then folded))

--| An element that may start after a waiting comment may start anywhere else.
theorem elUnheld ∀ (kinds: Text → Tok) (doc: Doc) (indent: Nat) (before trails: Bool) (start: Nat → Place → Option Nat)
    (el: ElHangs kinds doc indent before trails start):
    ElHangs kinds doc indent False trails start :=
  state entry =>
    hangsPre kinds doc indent
      (Entered indent before state entry (start indent entry))
      (Entered indent False state entry (start indent entry))
      (place hang =>
        Ended (openedBy state (start indent entry)) trails place ∧ hang = At (openedBy state (start indent entry)))
      (el state entry)
      (place hang (isEntry, folded, (seated, clear, room)) =>
        let held: Seated indent before state entry := match entry, seated with
          | AtStart at carry, seated => seated
          | Broken at carry, seated => seated
          | Mid at carry, seated => seated
          | Held at carry, (never, _, _) => (Bool.falseNotTrue never).impossible
        (isEntry, folded, (held, clear, room)))

--| A displaced element: its contents start where it does, at the start of a line after a waiting comment, and
--| are indented from there.
--|
--| Proof idea: `DisplacedHolds` gives the contents a seat at the column their first word is written at; at a line
--| start that is the indentation (`at = indent`), after a waiting comment the comment break's, with no floor.
theorem displacedHangs ∀ (kinds: Text → Tok) (inner: Doc) (indent: Nat) (before trails: Bool)
    (el: ∀ (column: Nat) => ElHangs kinds inner column False trails wordStart):
    ElHangs kinds (Displaced inner) indent before trails wordStart :=
  state entry =>
    let post: Place → Hang → Prop := place hang =>
      Ended (openedBy state (wordStart indent entry)) trails place ∧ hang = At (openedBy state (wordStart indent entry))
    let seat: Nat → Place → Hang → Prop := column place hang =>
      Entered column False state place (wordStart column place) place hang
        ∧ wordStart column place = wordStart indent entry
    hangsDisplaced kinds inner indent
      (Entered indent before state entry (wordStart indent entry))
      post
      seat
      (column place trace next (entered, same) after =>
        el column state place place trace next entered (left later (ended, folded) =>
          after left later (rewrite same at ended then ended, rewrite same at folded then folded)))
      (place hang (isEntry, folded, (seated, clear, room)) =>
        rewrite isEntry then
          match entry, seated, room with
            | AtStart at carry, (atIndent, landed), room =>
              let wide: Nat.max indent at = at := Nat.maxRight indent at arithmetic
              rewrite wide then
                (
                  (byComputing, folded, (byComputing, rewrite atIndent then landed), rewrite atIndent then clear, room),
                  byComputing
                )
            | Broken at carry, (atIndent, landed), room =>
              let wide: Nat.max indent at = at := Nat.maxRight indent at arithmetic
              rewrite wide then
                (
                  (byComputing, folded, (byComputing, rewrite atIndent then landed), rewrite atIndent then clear, room),
                  byComputing
                )
            | Mid at carry, seated, room => ((byComputing, folded, seated, clear, room), byComputing)
            | Held at carry, (_, floor, _), room =>
              let broken := Nat.max indent (at + 2)
              let wide: (inForce state.blocks state.top <= broken) = True := arithmetic
              let landed: floored carry broken = broken := rewrite floor
              ((byComputing, folded, (landed, landed), wide, room), byComputing))

--| A node framed by its first token, whose own-line comments an enclosing element wrote, or that has none: the node,
--| displaced where a comment waits before it.
theorem framedHangs ∀ (kinds: Text → Tok) (first: Word) (around: Around) (doc: Doc) (indent: Nat) (trails: Bool)
    (bare: first.leading around around.at = [])
    (el: ∀ (column: Nat) => ElHangs kinds doc column False trails wordStart):
    ElHangs kinds (framedBy first around doc) indent around.before trails wordStart :=
  state entry =>
    let pre := Entered indent around.before state entry (wordStart indent entry)
    let post: Place → Hang → Prop := place hang =>
      Ended (openedBy state (wordStart indent entry)) trails place ∧ hang = At (openedBy state (wordStart indent entry))
    rewrite bare then
      match placed: first.noted || around.before with
        | True =>
          hangsConcat kinds
            [Doc.Nothing, Displaced doc]
            indent
            pre
            post
            (hangsCons kinds Doc.Nothing
              [Displaced doc]
              indent
              pre
              pre
              post
              (hangsNothing kinds indent pre)
              (hangsLast kinds
                (Displaced doc)
                indent
                pre
                post
                (displacedHangs kinds doc indent around.before trails el state entry)))
        | False =>
          let unheld: around.before = False := Bool.orFalseRight first.noted around.before placed
          hangsConcat kinds
            [Doc.Nothing, doc]
            indent
            pre
            post
            (hangsCons kinds Doc.Nothing
              [doc]
              indent
              pre
              pre
              post
              (hangsNothing kinds indent pre)
              (hangsLast kinds doc indent pre post (rewrite unheld then el indent state entry)))

--| Where no comment waits, an element's first word keeps what is in force at the indentation or left of it.
theorem openedBound ∀ (indent: Nat) (state: HangState) (entry: Place)
    (seated: Seated indent False state entry)
    (clear: (inForce state.blocks state.top <= indent) = True):
    (inForce (openedBy state (wordStart indent entry)).blocks (openedBy state (wordStart indent entry)).top <= indent)
      = True :=
  match entry, seated with
    | AtStart at carry, (atIndent, _) => rewrite atIndent then openedSome state indent clear
    | Broken at carry, (atIndent, _) => rewrite atIndent then openedSome state indent clear
    | Mid at carry, _ => rewrite openedNone state then clear
    | Held at carry, (never, _, _) => (Bool.falseNotTrue never).impossible

--| An element, then a part after it.
theorem elThen ∀ (kinds: Text → Tok) (first part: Doc) (indent: Nat) (middle trails: Bool)
    (head: ElHangs kinds first indent False middle wordStart)
    (rest: PartHangs kinds part indent middle trails):
    ElHangs kinds (Doc.concat [first, part]) indent False trails wordStart :=
  state entry place trace next entered after =>
    let pre := Entered indent False state entry (wordStart indent entry)
    let opened := openedBy state (wordStart indent entry)
    let mid: Place → Hang → Prop := place hang => Ended opened middle place ∧ hang = At opened
    let post: Place → Hang → Prop := place hang => Ended opened trails place ∧ hang = At opened
    match entered with
      | (_, _, (seated, clear, _)) =>
        let bound := openedBound indent state entry seated clear
        hangsConcat kinds
          [first, part]
          indent
          pre
          post
          (hangsTwo kinds first part indent pre mid post (head state entry) (between later next (ended,
            folded) onward =>
            rest opened between
              (openedQuietStart state (wordStart indent entry))
              (openedUnglued state (wordStart indent entry))
              between
              later
              next
              (byComputing, folded, ended, bound)
              onward))
          place
          trace
          next
          entered
          after

--| What a prefix operator puts before its operand: nothing, or a space.
def Gap (gap: Doc): Prop := gap = Doc.Nothing ∨ gap = Doc.text " "

theorem prefixGapIs ∀ (operator: Word) (operand: Expr): Gap (prefixGap operator operand) :=
  match spaced: operator.text == "-" && (operand.firstWord.text == "-" || operand.numeralApplication) with
    | True => Inr byComputing
    | False => Inl byComputing

--| A gap after words keeps the place where an element ended, and the fold.
theorem gapKeeps ∀ (kinds: Text → Tok) (gap: Doc) (indent: Nat) (state: HangState) (before: Bool) (bound: Prop)
    (isGap: Gap gap):
    HangLays kinds gap indent (place hang => Ended state before place ∧ hang = At state ∧ bound) (place hang =>
      Ended state before place ∧ hang = At state ∧ bound) :=
  place trace next holds after =>
    match isGap with
      | Inl isNothing => rewrite isNothing then after place trace holds
      | Inr isSpace =>
        rewrite isSpace then
          match place, holds with
            | Mid at carry, ((floor, left), folded, bound) =>
              after (Mid at (floorAfter " " carry)) trace ((byComputing, left), folded, bound)
            | Held at carry, holds => after (Held at carry) trace holds
            | AtStart at carry, (never, _, _) => (Bool.falseNotTrue never).impossible
            | Broken at carry, (never, _, _) => (Bool.falseNotTrue never).impossible

--| An element, a gap, then a part after it.
theorem elGapThen ∀ (kinds: Text → Tok) (first gap part: Doc) (indent: Nat) (middle trails: Bool)
    (head: ElHangs kinds first indent False middle wordStart)
    (isGap: Gap gap)
    (rest: PartHangs kinds part indent middle trails):
    ElHangs kinds (Doc.concat [first, gap, part]) indent False trails wordStart :=
  state entry place trace next entered after =>
    let pre := Entered indent False state entry (wordStart indent entry)
    let opened := openedBy state (wordStart indent entry)
    match entered with
      | (_, _, (seated, clear, _)) =>
        let bound := openedBound indent state entry seated clear
        let mid: Place → Hang → Prop := place hang =>
          Ended opened middle place ∧ hang = At opened ∧ (inForce opened.blocks opened.top <= indent) = True
        let post: Place → Hang → Prop := place hang => Ended opened trails place ∧ hang = At opened
        hangsConcat kinds
          [first, gap, part]
          indent
          pre
          post
          (hangsCons kinds first
            [gap, part]
            indent
            pre
            mid
            post
            (hangsPost kinds first indent pre
              (place hang => Ended opened middle place ∧ hang = At opened)
              mid
              (head state entry)
              (place hang (ended, folded) => (ended, folded, bound)))
            (hangsTwo kinds gap part indent mid mid post
              (gapKeeps kinds gap indent opened middle ((inForce opened.blocks opened.top <= indent) = True) isGap)
              (between later next (ended, folded, bound) onward =>
                rest opened between
                  (openedQuietStart state (wordStart indent entry))
                  (openedUnglued state (wordStart indent entry))
                  between
                  later
                  next
                  (byComputing, folded, ended, bound)
                  onward)))
          place
          trace
          next
          entered
          after

--| A prefix operator and its operand, the operator's own-line comments written elsewhere or none.
theorem prefixHangs ∀ (kinds: Text → Tok) (operator: Word) (operand: Expr) (around: Around) (indent: Nat) (trails: Bool)
    (plain: Plain (kinds operator.text))
    (token: operator.text.startsWith "--" = False)
    (solid: isLayout operator.text = False)
    (closer: isCloserText operator.text = False)
    (comma: (operator.text == ",") = False)
    (bare: operator.leading around around.at = [])
    (trailed: TrailsComment operator)
    (operandHangs: ∀ (column: Nat) => ElHangs kinds
      (operand.el (around.next operator.trails 1))
      column
      operator.trails
      trails
      wordStart):
    ElHangs kinds (Expr.el (Prefix operator operand) around) indent around.before trails wordStart :=
  let inside := { around | hoisted = True }
  framedHangs kinds operator around
    (Doc.concat [
      operator.leaf inside around.at,
      prefixGap operator operand,
      operand.el (around.next operator.trails 1)
    ])
    indent
    trails
    bare
    (column =>
      elGapThen kinds
        (operator.leaf inside around.at)
        (prefixGap operator operand)
        (operand.el (around.next operator.trails 1))
        column
        operator.trails
        trails
        (elUnheld kinds
          (operator.leaf inside around.at)
          column
          inside.before
          operator.trails
          wordStart
          (plainLeafHangs kinds operator inside around.at column plain token solid closer comma byComputing trailed))
        (prefixGapIs operator operand)
        (elPart kinds (operand.el (around.next operator.trails 1)) column operator.trails trails (operandHangs column)))

-- Own-line comments.

--| Own-line comments the lexer reads as comments.
def NotesComment: List Note → Prop
  | [] => True
  | [note, ..rest] => IsComment note.text ∧ isLayout note.text = False ∧ NotesComment rest

--| At the start of a line at `column`, whose breaks land there (`floored`), with the fold at `hang`.
def LineAt (indent column: Nat) (hang: Hang) (place: Place) (now: Hang): Prop := match place with
  | AtStart at carry => now = hang ∧ at = column ∧ floored carry indent = column
  | Broken at carry => now = hang ∧ at = column ∧ floored carry indent = column
  | _ => False = True

--| As `LineAt`, right after a line break, where a blank line may follow.
def BrokenAt (indent column: Nat) (hang: Hang) (place: Place) (now: Hang): Prop := match place with
  | Broken at carry => now = hang ∧ at = column ∧ floored carry indent = column
  | _ => False = True

--| After an own-line comment, on its line.
def WrittenAt (indent column: Nat) (hang: Hang) (place: Place) (now: Hang): Prop := match place with
  | Mid at carry => now = hang ∧ floored carry indent = column
  | _ => False = True

--| An own-line comment on its line, then a line break: the fold skips the comment.
theorem noteHangs ∀ (kinds: Text → Tok) (text: Text) (indent column: Nat) (hang: Hang)
    (comment: IsComment text)
    (solid: isLayout text = False):
    HangLaysAll kinds [Doc.text text, HardLine] indent (LineAt indent column hang) (BrokenAt indent column hang) :=
  let skips := (state: Hang) (start: Option Nat) => commentSkips kinds state { word = text, start } comment
  hangsTwo kinds
    (Doc.text text)
    HardLine
    indent
    (LineAt indent column hang)
    (WrittenAt indent column hang)
    (BrokenAt indent column hang)
    (hangsChunk kinds text text.length indent
      (LineAt indent column hang)
      (WrittenAt indent column hang)
      solid
      (place trace lined =>
        match place, lined with
          | AtStart at carry, (now, atColumn, landed) =>
            rewrite commentKeepsFloor text carry (commentStarts text comment), skips (hangOf kinds trace) (Some at) then
              (now, landed)
          | Broken at carry, (now, atColumn, landed) =>
            rewrite commentKeepsFloor text carry (commentStarts text comment), skips (hangOf kinds trace) (Some at) then
              (now, landed)))
    (hangsHardBroken kinds indent (WrittenAt indent column hang) (BrokenAt indent column hang) (place now holds =>
      match place, holds with
        | Mid at carry, (same, landed) => (byComputing, (same, landed, landed))
        | AtStart at carry, never => (Bool.falseNotTrue never).impossible
        | Broken at carry, never => (Bool.falseNotTrue never).impossible
        | Held at carry, never => (Bool.falseNotTrue never).impossible))

theorem brokenLine ∀ (indent column: Nat) (hang: Hang) (place: Place) (now: Hang)
    (broken: BrokenAt indent column hang place now):
    LineAt indent column hang place now :=
  match place, broken with
    | Broken at carry, holds => holds
    | AtStart at carry, never => (Bool.falseNotTrue never).impossible
    | Mid at carry, never => (Bool.falseNotTrue never).impossible
    | Held at carry, never => (Bool.falseNotTrue never).impossible

--| A blank line kept right after a line break.
theorem blankHangs ∀ (kinds: Text → Tok) (indent column: Nat) (hang: Hang):
    HangLays kinds Blank indent (BrokenAt indent column hang) (LineAt indent column hang) :=
  hangsBlank kinds indent (BrokenAt indent column hang) (LineAt indent column hang) (place trace broken =>
    match place, broken with
      | Broken at carry, holds => rewrite blankHang kinds trace then holds
      | AtStart at carry, never => (Bool.falseNotTrue never).impossible
      | Mid at carry, never => (Bool.falseNotTrue never).impossible
      | Held at carry, never => (Bool.falseNotTrue never).impossible)

--| Own-line comments after the first, each on its line, a blank line above one kept.
theorem laterNotesHang ∀ (kinds: Text → Tok) (notes: List Note) (indent column: Nat) (hang: Hang)
    (comments: NotesComment notes):
    HangLaysAll kinds (notesAbove True notes) indent (BrokenAt indent column hang) (BrokenAt indent column hang) :=
  match notes, comments with
    | [], _ =>
      hangsNil kinds indent (BrokenAt indent column hang) (BrokenAt indent column hang) (place now held => held)
    | [note, ..rest], (comment, solid, others) =>
      let line := noteHangs kinds note.text indent column hang comment solid
      let more := laterNotesHang kinds rest indent column hang others
      match blank: note.blankBefore with
        | True =>
          hangsCons kinds Blank
            ([Doc.text note.text, HardLine] ++ notesAbove True rest)
            indent
            (BrokenAt indent column hang)
            (LineAt indent column hang)
            (BrokenAt indent column hang)
            (blankHangs kinds indent column hang)
            (hangsAppend kinds
              [Doc.text note.text, HardLine]
              (notesAbove True rest)
              indent
              (LineAt indent column hang)
              (BrokenAt indent column hang)
              (BrokenAt indent column hang)
              line
              more)
        | False =>
          hangsAppend kinds
            [Doc.text note.text, HardLine]
            (notesAbove True rest)
            indent
            (BrokenAt indent column hang)
            (BrokenAt indent column hang)
            (BrokenAt indent column hang)
            (allHangsPre kinds
              [Doc.text note.text, HardLine]
              indent
              (LineAt indent column hang)
              (BrokenAt indent column hang)
              (BrokenAt indent column hang)
              line
              (brokenLine indent column hang))
            more

--| A token's own-line comments, each on its line, from the start of a line, with no blank line kept above the
--| first: at a line start that needn't follow a line break, a `Blank` may print nothing (`Doc.Proofs.BlankLays`).
theorem notesHang ∀ (kinds: Text → Tok) (keep: Bool) (note: Note) (rest: List Note) (indent column: Nat) (hang: Hang)
    (comments: NotesComment [note, ..rest])
    (quiet: (note.blankBefore && keep) = False):
    HangLaysAll kinds
      (notesAbove keep [note, ..rest])
      indent
      (LineAt indent column hang)
      (BrokenAt indent column hang) :=
  match comments with
    | (comment, solid, others) =>
      rewrite quiet then
        hangsAppend kinds
          [Doc.text note.text, HardLine]
          (notesAbove True rest)
          indent
          (LineAt indent column hang)
          (BrokenAt indent column hang)
          (BrokenAt indent column hang)
          (noteHangs kinds note.text indent column hang comment solid)
          (laterNotesHang kinds rest indent column hang others)

--| A token's own-line comments, each on its line, right after a line break, a blank line above the first kept or
--| not.
theorem notesHangBroken ∀ (kinds: Text → Tok) (keep: Bool) (note: Note) (rest: List Note)
    (indent column: Nat) (hang: Hang)
    (comments: NotesComment [note, ..rest]):
    HangLaysAll kinds
      (notesAbove keep [note, ..rest])
      indent
      (BrokenAt indent column hang)
      (BrokenAt indent column hang) :=
  match keep with
    | True => laterNotesHang kinds [note, ..rest] indent column hang comments
    | False =>
      allHangsPre kinds
        (notesAbove False [note, ..rest])
        indent
        (LineAt indent column hang)
        (BrokenAt indent column hang)
        (BrokenAt indent column hang)
        (notesHang kinds False note rest indent column hang comments
          (Bool.andFalseRight note.blankBefore False byComputing))
        (brokenLine indent column hang)

--| Whether the place is a line start that needn't follow a line break, where a `Blank` may print nothing.
def plainStart: Place → Bool
  | AtStart _ _ => True
  | _ => False

--| Where a token with own-line comments above it starts its line: at the line's start if it is at one, else on the
--| comment break `LineStart` makes.
def leadColumn (indent: Nat) (place: Place): Nat := match place with
  | AtStart at _ => at
  | Broken at _ => at
  | Mid at _ => Nat.max indent (at + 2)
  | Held at _ => Nat.max indent (at + 2)

def leadStart (indent: Nat) (place: Place): Option Nat := Some (leadColumn indent place)

--| A `LineStart` from a seat: to the start of a line at the token's column, the comment floor there.
theorem startHangs ∀ (kinds: Text → Tok) (indent: Nat) (before: Bool) (state: HangState) (entry: Place):
    HangLays kinds LineStart indent
      (place hang => place = entry ∧ hang = At state ∧ Seated indent before state entry)
      (LineAt indent (leadColumn indent entry) (At state)) :=
  hangsStart kinds indent
    (place hang => place = entry ∧ hang = At state ∧ Seated indent before state entry)
    (LineAt indent (leadColumn indent entry) (At state))
    (place trace (isEntry, folded, seated) =>
      rewrite isEntry then
        match entry, seated with
          | AtStart at carry, (atIndent, landed) => (folded, byComputing, rewrite atIndent then landed)
          | Broken at carry, (atIndent, landed) => (folded, byComputing, rewrite atIndent then landed)
          | Mid at carry, (floor, _) =>
            let broken := Nat.max indent (at + 2)
            let landed: floored carry broken = broken := rewrite floor
            (folded, landed, Nat.maxRight indent broken arithmetic)
          | Held at carry, (_, floor, _) =>
            let broken := Nat.max indent (at + 2)
            let landed: floored carry broken = broken := rewrite floor
            (folded, landed, Nat.maxRight indent broken arithmetic))

--| A `LineStart` from a seat that isn't a plain line start: right after the line break it makes, or the one before.
theorem startHangsBroken ∀ (kinds: Text → Tok) (indent: Nat) (before: Bool) (state: HangState) (entry: Place)
    (fresh: plainStart entry = False):
    HangLays kinds LineStart indent
      (place hang => place = entry ∧ hang = At state ∧ Seated indent before state entry)
      (BrokenAt indent (leadColumn indent entry) (At state)) :=
  hangsStart kinds indent
    (place hang => place = entry ∧ hang = At state ∧ Seated indent before state entry)
    (BrokenAt indent (leadColumn indent entry) (At state))
    (place trace (isEntry, folded, seated) =>
      rewrite isEntry then
        match entry, fresh, seated with
          | AtStart at carry, never, _ => (Bool.falseNotTrue never.flipped).impossible
          | Broken at carry, _, (atIndent, landed) => (folded, byComputing, rewrite atIndent then landed)
          | Mid at carry, _, (floor, _) =>
            let broken := Nat.max indent (at + 2)
            let landed: floored carry broken = broken := rewrite floor
            (folded, landed, Nat.maxRight indent broken arithmetic)
          | Held at carry, _, (_, floor, _) =>
            let broken := Nat.max indent (at + 2)
            let landed: floored carry broken = broken := rewrite floor
            (folded, landed, Nat.maxRight indent broken arithmetic))

--| A `LineStart` from a seat, then a token's own-line comments, each on its line: a blank line above the first is
--| kept except at a plain line start.
theorem startNotesHang ∀ (kinds: Text → Tok) (keep: Bool) (indent: Nat) (before: Bool) (state: HangState) (entry: Place)
    (note: Note) (rest: List Note)
    (comments: NotesComment [note, ..rest])
    (quiet: (plainStart entry && note.blankBefore && keep) = False):
    HangLaysAll kinds
      [LineStart, ..notesAbove keep [note, ..rest]]
      indent
      (place hang => place = entry ∧ hang = At state ∧ Seated indent before state entry)
      (BrokenAt indent (leadColumn indent entry) (At state)) :=
  let pre: Place → Hang → Prop := place hang => place = entry ∧ hang = At state ∧ Seated indent before state entry
  let column := leadColumn indent entry
  match plain: plainStart entry with
    | True =>
      hangsCons kinds LineStart
        (notesAbove keep [note, ..rest])
        indent
        pre
        (LineAt indent column (At state))
        (BrokenAt indent column (At state))
        (startHangs kinds indent before state entry)
        (notesHang kinds keep note rest indent column (At state) comments quiet)
    | False =>
      hangsCons kinds LineStart
        (notesAbove keep [note, ..rest])
        indent
        pre
        (BrokenAt indent column (At state))
        (BrokenAt indent column (At state))
        (startHangsBroken kinds indent before state entry plain)
        (notesHangBroken kinds keep note rest indent column (At state) comments)

--| A token with no comments above it, seated right after a line break: the blank line kept above an item is left,
--| and the token's line starts where it did.
theorem blankLeadHangs ∀ (kinds: Text → Tok) (word: Word) (around: Around) (key indent: Nat) (before: Bool)
    (state: HangState) (at: Nat) (carry: Carry)
    (hoisted: around.hoisted = False)
    (bare: word.comments.above = []):
    HangLaysAll kinds
      (word.leading around key)
      indent
      (place hang => place = Broken at carry ∧ hang = At state ∧ Seated indent before state (Broken at carry))
      (place hang => hang = At state ∧ Seated indent before state place ∧ place.midLine = False) :=
  let pre: Place → Hang → Prop := place hang =>
    place = Broken at carry ∧ hang = At state ∧ Seated indent before state (Broken at carry)
  let post: Place → Hang → Prop := place hang =>
    hang = At state ∧ Seated indent before state place ∧ place.midLine = False
  rewrite hoisted, bare then
    match blank: around.item && word.comments.blankBefore with
      | True =>
        hangsCons kinds BreakParent
          [Blank]
          indent
          pre
          pre
          post
          (hangsBreakParent kinds indent pre)
          (hangsLast kinds Blank indent pre post
            (hangsBlank kinds indent pre post (place trace (isEntry, folded, seated) =>
              rewrite isEntry, blankHang kinds trace then (folded, seated, byComputing))))
      | False => hangsNil kinds indent pre post (place hang (isEntry, folded, seated) =>
        rewrite isEntry then (folded, seated, byComputing))

--| A token's own-line comments and the blank line kept above it, from a seat: to the start of the token's line.
theorem leadingHangs ∀ (kinds: Text → Tok) (word: Word) (around: Around) (key indent: Nat) (before: Bool)
    (state: HangState) (entry: Place) (note: Note) (rest: List Note)
    (hoisted: around.hoisted = False)
    (noted: word.comments.above = [note, ..rest])
    (closer: isCloserText word.text = False)
    (comments: NotesComment [note, ..rest])
    (quiet: (plainStart entry && note.blankBefore && around.item) = False):
    HangLaysAll kinds
      (word.leading around key)
      indent
      (place hang => place = entry ∧ hang = At state ∧ Seated indent before state entry)
      (LineAt indent (leadColumn indent entry) (At state)) :=
  let pre: Place → Hang → Prop := place hang => place = entry ∧ hang = At state ∧ Seated indent before state entry
  let column := leadColumn indent entry
  let lined := LineAt indent column (At state)
  let broken := BrokenAt indent column (At state)
  let front :=
    hangsCons kinds BreakParent
      ([LineStart] ++ notesAbove around.item [note, ..rest])
      indent
      pre
      pre
      broken
      (hangsBreakParent kinds indent pre)
      (startNotesHang kinds around.item indent before state entry note rest comments quiet)
  rewrite hoisted, noted, closer then
    match blank: word.comments.blankBefore with
      | True =>
        hangsAppend kinds
          ([BreakParent, LineStart] ++ notesAbove around.item [note, ..rest])
          [Blank]
          indent
          pre
          broken
          lined
          front
          (hangsLast kinds Blank indent broken lined (blankHangs kinds indent column (At state)))
      | False =>
        hangsAppend kinds
          ([BreakParent, LineStart] ++ notesAbove around.item [note, ..rest])
          []
          indent
          pre
          broken
          lined
          front
          (hangsNil kinds indent broken lined (brokenLine indent column (At state)))
