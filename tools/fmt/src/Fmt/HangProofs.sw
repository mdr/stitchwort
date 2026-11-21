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
import Syntax (Comments, Expr, Leaf, Note, Tok, Word)
import Fmt (..)
import Syntax.SharedFacts (solidSpaces)

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
--| leaves a place and fold that satisfy `post`. The folds are named (`hang`, `left`) and tied to their traces by
--| equations, rather than written `hangOf kinds trace`, so that `pre` and `post` are applied to bound variables only
--| and lemmas can take them implicitly; `hangsBy`, `allHangsBy`, `laysBy` and `hangsAfter` go between this and the plain reading.
def HangLays (kinds: Text → Tok) (doc: Doc) (indent: Nat) (pre post: Place → Hang → Prop): Prop :=
  ∀ (place: Place) (hang: Hang) (trace: List Event) (next: Place → List Event → Prop) => hangOf kinds trace = hang
    → pre place hang
    → (∀ (after: Place) (left: Hang) (later: List Event) => hangOf kinds later = left
      → post after left
      → next after later)
    → Lays doc indent place trace next

def HangLaysAll (kinds: Text → Tok) (docs: List Doc) (indent: Nat) (pre post: Place → Hang → Prop): Prop :=
  ∀ (place: Place) (hang: Hang) (trace: List Event) (next: Place → List Event → Prop) => hangOf kinds trace = hang
    → pre place hang
    → (∀ (after: Place) (left: Hang) (later: List Event) => hangOf kinds later = left
      → post after left
      → next after later)
    → LaysAll docs indent place trace next

theorem hangsBy ∀ [kinds: Text → Tok] [doc: Doc] [indent: Nat] [pre post: Place → Hang → Prop]
    (lays: ∀ (place: Place) (trace: List Event) (next: Place → List Event → Prop) => pre place (hangOf kinds trace)
      → (∀ (after: Place) (later: List Event) => post after (hangOf kinds later) → next after later)
      → Lays doc indent place trace next):
    HangLays kinds doc indent pre post :=
  place hang trace next same holds after =>
    lays place trace next (rewrite same then holds) (left later reached =>
      after left (hangOf kinds later) later byComputing reached)

theorem laysBy ∀ [kinds: Text → Tok] [doc: Doc] [indent: Nat] [pre post: Place → Hang → Prop]
    (hangs: HangLays kinds doc indent pre post)
    (place: Place) (trace: List Event) (next: Place → List Event → Prop) (holds: pre place (hangOf kinds trace))
    (after: ∀ (left: Place) (later: List Event) => post left (hangOf kinds later) → next left later):
    Lays doc indent place trace next :=
  hangs place (hangOf kinds trace) trace next byComputing holds (left hang later same reached =>
    after left later (rewrite same then reached))

theorem allHangsBy ∀ [kinds: Text → Tok] [docs: List Doc] [indent: Nat] [pre post: Place → Hang → Prop]
    (lays: ∀ (place: Place) (trace: List Event) (next: Place → List Event → Prop) => pre place (hangOf kinds trace)
      → (∀ (after: Place) (later: List Event) => post after (hangOf kinds later) → next after later)
      → LaysAll docs indent place trace next):
    HangLaysAll kinds docs indent pre post :=
  place hang trace next same holds after =>
    lays place trace next (rewrite same then holds) (left later reached =>
      after left (hangOf kinds later) later byComputing reached)

--| The plain reading of a triple's continuation, as the triple takes it.
theorem hangsAfter ∀ [kinds: Text → Tok] [post: Place → Hang → Prop] [next: Place → List Event → Prop]
    (after: ∀ (left: Place) (later: List Event) => post left (hangOf kinds later) → next left later) (left: Place)
    (hang: Hang) (later: List Event)
    (same: hangOf kinds later = hang) (reached: post left hang):
    next left later :=
  after left later (rewrite same then reached)

--| A declaration's document that lays from the start of the output with the fold never broken prints words that
--| keep the line rule: the printed trace, comments put after the closers on their line, folds alike.
theorem hangsPrinted ∀ [kinds: Text → Tok] [doc: Doc] (width: Nat)
    (lays: HangLays kinds doc 0 (place hang => place = AtStart 0 Carry.none ∧ hang = Opening) (place hang =>
      hang ≠ Broke)):
    hangOf kinds (eventsOf (printedPieces doc width).reverse) ≠ Broke :=
  let spec: Place → List Event → Prop := place laid => hangOf kinds laid ≠ Broke
  let laid: Lays doc 0 (AtStart 0 Carry.none) [] spec :=
    laysBy lays (AtStart 0 Carry.none) [] spec (byComputing, byComputing) (after later holds => holds)
  match printLays spec doc width laid with
    | (place, laid, holds, tucks) =>
      rewrite (tucksHang kinds laid (eventsOf (printedPieces doc width).reverse) tucks).flipped then holds

theorem hangsPre ∀ [kinds: Text → Tok] [doc: Doc] [indent: Nat] [pre weaker post: Place → Hang → Prop]
    (lays: HangLays kinds doc indent pre post)
    (implies: ∀ (place: Place) (hang: Hang) => weaker place hang → pre place hang):
    HangLays kinds doc indent weaker post :=
  place hang trace next same holds after => lays place hang trace next same (implies place hang holds) after

theorem hangsPost ∀ [kinds: Text → Tok] [doc: Doc] [indent: Nat] [pre post weaker: Place → Hang → Prop]
    (lays: HangLays kinds doc indent pre post)
    (implies: ∀ (place: Place) (hang: Hang) => post place hang → weaker place hang):
    HangLays kinds doc indent pre weaker :=
  place hang trace next same holds after =>
    lays place hang trace next same holds (left fold later folds reached =>
      after left fold later folds (implies left fold reached))

theorem allHangsPre ∀ [kinds: Text → Tok] [docs: List Doc] [indent: Nat] [pre weaker post: Place → Hang → Prop]
    (lays: HangLaysAll kinds docs indent pre post)
    (implies: ∀ (place: Place) (hang: Hang) => weaker place hang → pre place hang):
    HangLaysAll kinds docs indent weaker post :=
  place hang trace next same holds after => lays place hang trace next same (implies place hang holds) after

theorem allHangsPost ∀ [kinds: Text → Tok] [docs: List Doc] [indent: Nat] [pre post weaker: Place → Hang → Prop]
    (lays: HangLaysAll kinds docs indent pre post)
    (implies: ∀ (place: Place) (hang: Hang) => post place hang → weaker place hang):
    HangLaysAll kinds docs indent pre weaker :=
  place hang trace next same holds after =>
    lays place hang trace next same holds (left fold later folds reached =>
      after left fold later folds (implies left fold reached))

theorem hangsNil ∀ (kinds: Text → Tok) (indent: Nat)
    (pre post: Place → Hang → Prop) (implies: ∀ (place: Place) (hang: Hang) => pre place hang → post place hang):
    HangLaysAll kinds [] indent pre post :=
  place hang trace next same holds after => after place hang trace same (implies place hang holds)

theorem hangsCons ∀ [kinds: Text → Tok] [doc: Doc] (docs: List Doc) [indent: Nat] [pre middle post: Place → Hang → Prop]
    (first: HangLays kinds doc indent pre middle)
    (rest: HangLaysAll kinds docs indent middle post):
    HangLaysAll kinds [doc, ..docs] indent pre post :=
  place hang trace next same holds after =>
    first place hang trace
      (between later => LaysAll docs indent between later next)
      same
      holds
      (between fold later folds reached => rest between fold later next folds reached after)

theorem hangsLast ∀ [kinds: Text → Tok] [doc: Doc] [indent: Nat] [pre post: Place → Hang → Prop]
    (only: HangLays kinds doc indent pre post):
    HangLaysAll kinds [doc] indent pre post :=
  hangsCons [] only (hangsNil kinds indent post post (place hang holds => holds))

theorem hangsTwo ∀ [kinds: Text → Tok] [first second: Doc] [indent: Nat] [pre middle post: Place → Hang → Prop]
    (one: HangLays kinds first indent pre middle)
    (other: HangLays kinds second indent middle post):
    HangLaysAll kinds [first, second] indent pre post :=
  hangsCons [second] one (hangsLast other)

--| Documents one after another, then more: the first lot, then the second from where the first leaves off.
theorem laysAllAppend ∀ [front: List Doc] (back: List Doc) (indent: Nat) (place: Place)
    (trace: List Event) (next: Place → List Event → Prop)
    (lays: LaysAll front indent place trace (between later => LaysAll back indent between later next)):
    LaysAll (front ++ back) indent place trace next :=
  match front, lays with
    | [], lays => lays
    | [doc, ..rest], lays =>
      laysWeaker doc indent place trace
        (between later => LaysAll rest indent between later (after more => LaysAll back indent after more next))
        (between later => LaysAll (rest ++ back) indent between later next)
        (between later reached => laysAllAppend back indent between later next reached)
        lays

theorem hangsAppend ∀ [kinds: Text → Tok] [front back: List Doc] [indent: Nat] [pre middle post: Place → Hang → Prop]
    (first: HangLaysAll kinds front indent pre middle)
    (second: HangLaysAll kinds back indent middle post):
    HangLaysAll kinds (front ++ back) indent pre post :=
  place hang trace next same holds after =>
    laysAllAppend back indent place trace next
      (first place hang trace
        (between later => LaysAll back indent between later next)
        same
        holds
        (between fold later folds reached => second between fold later next folds reached after))

theorem emptyLays ∀ [doc: Doc] (indent: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop)
    (empty: doc.isEmpty = True)
    (lays: Lays doc indent place trace next):
    next place trace :=
  match doc, empty, lays with | Doc.Nothing, _, lays => lays

theorem filterLays ∀ [docs: List Doc] (indent: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop)
    (lays: LaysAll docs indent place trace next):
    LaysAll (docs.filter (doc => not doc.isEmpty)) indent place trace next :=
  match docs, lays with
    | [], lays => lays
    | [doc, ..rest], lays =>
      match empty: doc.isEmpty with
        | True =>
          filterLays indent place trace next
            (emptyLays indent place trace (after later => LaysAll rest indent after later next) empty lays)
        | False =>
          laysWeaker doc indent place trace
            (after later => LaysAll rest indent after later next)
            (after later => LaysAll (rest.filter (doc => not doc.isEmpty)) indent after later next)
            (after later others => filterLays indent after later next others)
            lays

--| `Doc.concat` lays as the documents one after another.
theorem concatLays ∀ [docs: List Doc] (indent: Nat) (place: Place) (trace: List Event) (next: Place → List Event → Prop)
    (lays: LaysAll docs indent place trace next):
    Lays (Doc.concat docs) indent place trace next :=
  let kept := filterLays indent place trace next lays
  match found: docs.filter (doc => not doc.isEmpty) with
    | [] => kept
    | [only] =>
      laysWeaker only indent place trace
        (after later => LaysAll [] indent after later next)
        next
        (after later reached => reached)
        kept
    | [first, second, ..rest] => kept

theorem hangsConcat ∀ [kinds: Text → Tok] [docs: List Doc] [indent: Nat] [pre post: Place → Hang → Prop]
    (each: HangLaysAll kinds docs indent pre post):
    HangLays kinds (Doc.concat docs) indent pre post :=
  place hang trace next same holds after =>
    concatLays indent place trace next (each place hang trace next same holds after)

-- The document's constructors that put down no word.

theorem hangsNothing ∀ (kinds: Text → Tok) (indent: Nat) (pre: Place → Hang → Prop):
    HangLays kinds Doc.Nothing indent pre pre :=
  place hang trace next same holds after => after place hang trace same holds

theorem hangsBreakParent ∀ (kinds: Text → Tok) (indent: Nat) (pre: Place → Hang → Prop):
    HangLays kinds BreakParent indent pre pre :=
  place hang trace next same holds after => after place hang trace same holds

theorem hangsMark ∀ (kinds: Text → Tok) (key indent: Nat) (pre post: Place → Hang → Prop)
    (keeps: ∀ (place: Place) (hang: Hang) => pre place hang
      → post (place.withCarry (place.carry.mark key place.indent)) hang):
    HangLays kinds (Mark key) indent pre post :=
  hangsBy (place trace next holds after => after _ trace (keeps place (hangOf kinds trace) holds))

theorem hangsNest ∀ [kinds: Text → Tok] [more indent: Nat] [inner: Doc] [pre post: Place → Hang → Prop]
    (lays: HangLays kinds inner (indent + more) pre post):
    HangLays kinds (Nest more inner) indent pre post :=
  lays

theorem hangsGroup ∀ [kinds: Text → Tok] [inner: Doc] (hard: Bool) [indent: Nat] [pre post: Place → Hang → Prop]
    (lays: HangLays kinds inner indent pre post):
    HangLays kinds (Group inner hard) indent pre post :=
  lays

theorem hangsIdGroup ∀ [kinds: Text → Tok] (id: Nat) [inner: Doc] (hard: Bool)
    [indent: Nat] [pre post: Place → Hang → Prop]
    (lays: HangLays kinds inner indent pre post):
    HangLays kinds (IdGroup id inner hard) indent pre post :=
  lays

theorem hangsFlatten ∀ [kinds: Text → Tok] [inner: Doc] [indent: Nat] [pre post: Place → Hang → Prop]
    (lays: HangLays kinds inner indent pre post):
    HangLays kinds (Flatten inner) indent pre post :=
  lays

theorem hangsIfBroken ∀ [kinds: Text → Tok] (id: Nat) [broken flat: Doc] (indent: Nat) [pre post: Place → Hang → Prop]
    (brokenLays: HangLays kinds broken indent pre post)
    (flatLays: HangLays kinds flat indent pre post):
    HangLays kinds (IfBroken id broken flat) indent pre post :=
  place hang trace next same holds after =>
    (brokenLays place hang trace next same holds after, flatLays place hang trace next same holds after)

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
    | [last], (lays, _) => laysBy lays place trace next holds after
    | [option, second, ..others], (lays, rest) => (
      laysBy lays place trace next holds after,
      optionsHang kinds [second, ..others] indent pre post rest keeps place trace next holds after
    )

--| A choice whose options all lay out, from places where doing nothing would too.
theorem hangsChoice ∀ [kinds: Text → Tok] (options: List Doc) [indent: Nat] [pre post: Place → Hang → Prop]
    (each: EachHangs kinds indent pre post options)
    (keeps: ∀ (place: Place) (hang: Hang) => pre place hang → post place hang):
    HangLays kinds (Choice options) indent pre post :=
  hangsBy (place trace next holds after =>
    optionsHang kinds options indent pre post each keeps place trace next holds after)

--| A `HardLine`, after words: to the start of a line at the indentation.
theorem hangsHard ∀ (kinds: Text → Tok) (indent: Nat) (pre post: Place → Hang → Prop)
    (moves: ∀ (place: Place) (hang: Hang) => pre place hang
      → place.midLine = True ∧ post (AtStart (floored place.carry indent) (place.carry.breakTo indent)) hang):
    HangLays kinds HardLine indent pre post :=
  hangsBy (place trace next holds after =>
    match moves place (hangOf kinds trace) holds with | (mid, started) => (mid, Inr (after _ trace started)))

--| A `HardLine` a `Blank` may follow: right after the line break.
theorem hangsHardBroken ∀ (kinds: Text → Tok) (indent: Nat) (pre post: Place → Hang → Prop)
    (moves: ∀ (place: Place) (hang: Hang) => pre place hang
      → place.midLine = True ∧ post (Broken (floored place.carry indent) (place.carry.breakTo indent)) hang):
    HangLays kinds HardLine indent pre post :=
  hangsBy (place trace next holds after =>
    match moves place (hangOf kinds trace) holds with | (mid, broken) => (mid, Inl (after _ trace broken)))

--| A `Blank`: a blank line after a line break, which the fold skips; nothing after words.
theorem hangsBlank ∀ (kinds: Text → Tok) (indent: Nat) (pre post: Place → Hang → Prop)
    (moves: ∀ (place: Place) (trace: List Event) => pre place (hangOf kinds trace)
      → BlankLays place trace (after later => post after (hangOf kinds later))):
    HangLays kinds Blank indent pre post :=
  hangsBy (place trace next holds after =>
    blankLaysWeaker place trace (left later => post left (hangOf kinds later)) next after (moves place trace holds))

--| The fold after a blank line is the fold before it.
theorem blankHang ∀ (kinds: Text → Tok) (trace: List Event):
    hangOf kinds (trace ++ [Event.blankLine]) = hangOf kinds trace :=
  rewrite hangSnoc kinds trace Event.blankLine then blankSkips kinds (hangOf kinds trace)

--| A `Line`: a space or a line break, after words.
theorem hangsLine ∀ (kinds: Text → Tok) (indent: Nat) (pre post: Place → Hang → Prop)
    (moves: ∀ (place: Place) (trace: List Event) => pre place (hangOf kinds trace)
      → SepLays indent place trace (after later => post after (hangOf kinds later))):
    HangLays kinds Line indent pre post :=
  hangsBy (place trace next holds after =>
    sepLaysWeaker indent place trace
      (left later => post left (hangOf kinds later))
      next
      after
      (moves place trace holds))

--| A `SoftLine`: nothing or a line break, after words.
theorem hangsSoft ∀ (kinds: Text → Tok) (indent: Nat) (pre post: Place → Hang → Prop)
    (moves: ∀ (place: Place) (trace: List Event) => pre place (hangOf kinds trace)
      → SoftLays indent place trace (after later => post after (hangOf kinds later))):
    HangLays kinds SoftLine indent pre post :=
  hangsBy (place trace next holds after =>
    softLaysWeaker indent place trace
      (left later => post left (hangOf kinds later))
      next
      after
      (moves place trace holds))

--| A `LineStart`: a comment break, unless a line starts here.
theorem hangsStart ∀ (kinds: Text → Tok) (indent: Nat) (pre post: Place → Hang → Prop)
    (moves: ∀ (place: Place) (trace: List Event) => pre place (hangOf kinds trace)
      → StartLays indent place trace (after later => post after (hangOf kinds later))):
    HangLays kinds LineStart indent pre post :=
  hangsBy (place trace next holds after =>
    startLaysWeaker indent place trace
      (left later => post left (hangOf kinds later))
      next
      after
      (moves place trace holds))

--| A `LineStartHere`: a line at the indentation, unless a line starts here.
theorem hangsStartHere ∀ (kinds: Text → Tok) (indent: Nat) (pre post: Place → Hang → Prop)
    (moves: ∀ (place: Place) (trace: List Event) => pre place (hangOf kinds trace)
      → HerePuts indent place trace (after later => post after (hangOf kinds later))):
    HangLays kinds LineStartHere indent pre post :=
  hangsBy (place trace next holds after =>
    herePutsWeaker indent place trace
      (left later => post left (hangOf kinds later))
      next
      after
      (moves place trace holds))

--| A `CloserLine`: the closer's line, where the open marks put it, after a line break or at the line start one
--| left (`Place.closerLine`).
theorem hangsCloserLine ∀ (kinds: Text → Tok) (key indent: Nat) (pre post: Place → Hang → Prop)
    (moves: ∀ (place: Place) (hang: Hang) => pre place hang → post (place.closerLine key indent) hang):
    HangLays kinds (CloserLine key) indent pre post :=
  hangsBy (place trace next holds after => after _ trace (moves place (hangOf kinds trace) holds))

theorem hangsDisplaced ∀ (kinds: Text → Tok) (inner: Doc) (indent: Nat)
    (pre post: Place → Hang → Prop) (seat: Nat → Place → Hang → Prop)
    (lays: ∀ (column: Nat) => HangLays kinds inner column (seat column) post)
    (moves: ∀ (place: Place) (hang: Hang) => pre place hang
      → DisplacedHolds indent place (column start => seat column start hang)):
    HangLays kinds (Displaced inner) indent pre post :=
  hangsBy (place trace next holds after =>
    match place, moves place (hangOf kinds trace) holds with
      | AtStart at carry, seated => laysBy (lays _) (AtStart at carry) trace next seated after
      | Broken at carry, seated => laysBy (lays _) (Broken at carry) trace next seated after
      | Mid at carry, seated => laysBy (lays _) (Mid at carry) trace next seated after
      | Held at carry, seated => laysBy (lays _) _ trace next seated after)

--| A `OneLineBelow`: after words, its contents start a line at 2 deeper.
theorem hangsOneLineBelow ∀ [kinds: Text → Tok] [inner: Doc] (indent: Nat)
    (pre: Place → Hang → Prop) [below post: Place → Hang → Prop]
    (lays: HangLays kinds inner (indent + 2) below post)
    (moves: ∀ (place: Place) (hang: Hang) => pre place hang
      → place.midLine = True
        ∧ below (Broken (floored place.carry (indent + 2)) (place.carry.breakTo (indent + 2))) hang):
    HangLays kinds (OneLineBelow inner) indent pre post :=
  hangsBy (place trace next holds after =>
    match moves place (hangOf kinds trace) holds with | (mid, started) => (mid, laysBy lays _ trace next started after))

-- Words.

--| Where a word written at `place` starts its line, if it does: at the line's indentation if nothing is on the
--| line, and on a new line, a comment break, after a waiting comment.
def wordStart (indent: Nat) (place: Place): Option Nat := match place with
  | AtStart at _ | Broken at _ => Some at
  | Mid _ _ => None
  | Held at carry => Some (floored carry (Nat.max indent (at + 2)))

--| Where the printer is after the word `text`.
def wordAfter (indent: Nat) (text: Text) (place: Place): Place := match place with
  | AtStart at carry | Broken at carry | Mid at carry => Mid at (floorAfter text carry)
  | Held at carry =>
    Mid (floored carry (Nat.max indent (at + 2))) (floorAfter text (carry.breakTo (Nat.max indent (at + 2))))

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
      match place, reached with | AtStart _ _ | Broken _ _ | Mid _ _ | Held _ _, reached => reached
    )

theorem hangsChunk ∀ (kinds: Text → Tok) (text: Text) (width indent: Nat) (pre post: Place → Hang → Prop)
    (solid: isLayout text = False)
    (moves: ∀ (place: Place) (trace: List Event) => pre place (hangOf kinds trace)
      → post
        (wordAfter indent text place)
        (hangStep kinds (hangOf kinds trace) { word = text, start = wordStart indent place })):
    HangLays kinds (Chunk text width) indent pre post :=
  hangsBy (place trace next holds after =>
    writeOne indent text place trace next solid
      (after _ _
        (rewrite hangSnoc kinds trace { word = text, start = wordStart indent place } then moves place trace holds)))

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
  hangsBy (place trace next holds after =>
    let reached: next (closeAfter indent text place) (trace ++ [{ word = text, start = closeStart indent place }]) :=
      after _ _
        (rewrite hangSnoc kinds trace { word = text, start = closeStart indent place } then moves place trace holds)
    match place, reached with
      | AtStart at carry, reached => writeOne indent text (AtStart at carry) trace next solid reached
      | Broken at carry, reached => writeOne indent text (Broken at carry) trace next solid reached
      | Mid at carry, reached => writeOne indent text (Mid at carry) trace next solid reached
      | Held at carry, reached => (closes, reached))

--| A trailing comment, after words on its line: the fold skips it.
theorem hangsSuffix ∀ (kinds: Text → Tok) [comment: Text] (indent: Nat) (pre post: Place → Hang → Prop)
    (isComment: IsComment comment)
    (solid: isLayout comment = False)
    (moves: ∀ (place: Place) (hang: Hang) => pre place hang
      → ∃ (at: Nat) => ∃ (carry: Carry) => place = Mid at carry ∧ post (Held at carry) hang):
    HangLays kinds (LineSuffix comment) indent pre post :=
  hangsBy (place trace next holds after =>
    match moves place (hangOf kinds trace) holds with
      | (at, carry, (isMid, reached)) =>
        let skipped: hangOf kinds (trace ++ [{ word = comment, start = None }]) = hangOf kinds trace :=
          rewrite hangSnoc kinds trace { word = comment, start = None } then
            commentSkips kinds (hangOf kinds trace) { word = comment, start = None } isComment
        (isComment, solid, rewrite isMid then after (Held at carry) _ (rewrite skipped then reached)))

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

theorem stepCloser ∀ [kinds: Text → Tok] [state: HangState] [block: Option Nat] (outer: List (Option Nat))
    [word: Text] (start: Option Nat)
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

--| Where an element may start: at the start of a line at `column` (a comment floor no deeper), mid-line, or after a
--| waiting comment only if the code before ends its line with one (`before`); mid-line no comment floor, and nothing
--| in force right of the line's indentation, so a comment break is right of it.
def Seated (column: Nat) (before: Bool) (state: HangState) (place: Place): Prop := match place with
  | AtStart at carry | Broken at carry => at = column ∧ floored carry column = column
  | Mid at carry => carry.floor = None ∧ (inForce state.blocks state.top <= at) = True
  | Held at carry => before = True ∧ carry.floor = None ∧ (inForce state.blocks state.top <= at) = True

--| Where an element ends: after words, a trailing comment waiting only if it ends with one (`trails`), no comment
--| floor, and nothing in force right of the line's indentation.
def Ended (state: HangState) (trails: Bool) (place: Place): Prop := match place with
  | AtStart _ _ | Broken _ _ => False
  | Mid at carry => carry.floor = None ∧ (inForce state.blocks state.top <= at) = True
  | Held at carry => trails = True ∧ carry.floor = None ∧ (inForce state.blocks state.top <= at) = True

--| What the fold must allow where an element laid at `indent` starts, seated at `column`: the seat no deeper than
--| the indentation, nothing in force right of the indentation (its later lines are right of it), and room for its
--| first word to start a line at `first`, if it does.
def Seat (indent column: Nat) (before: Bool) (state: HangState) (entry: Place) (first: Option Nat): Prop :=
  Seated column before state entry
    ∧ (column <= indent) = True
    ∧ (inForce state.blocks state.top <= indent) = True
    ∧ Room state first

--| At the element's entry, with the fold at `state` and a seat there.
def Entered (indent column: Nat) (before: Bool) (state: HangState) (entry: Place) (first: Option Nat):
    Place → Hang → Prop :=
  place hang => place = entry ∧ hang = At state ∧ Seat indent column before state entry first

--| `doc` is one element that folds as one plain token: laid at `indent` from a seat at `column`, its first word
--| written where `start` says, it ends after words with the fold as after that one token. The seat is left of the
--| indentation only for a call's head, which `appDocs` lays 4 deeper than where the call starts.
def ElHangs (kinds: Text → Tok) (doc: Doc) (indent column: Nat) (before trails: Bool) (start: Nat → Place → Option Nat):
    Prop :=
  ∀ (state: HangState) (entry: Place) => HangLays kinds doc indent
    (Entered indent column before state entry (start indent entry))
    (place hang =>
      Ended (openedBy state (start indent entry)) trails place ∧ hang = At (openedBy state (start indent entry)))

theorem floorAfterToken ∀ (text: Text) (carry: Carry)
    (token: text.startsWith "--" = False):
    (floorAfter text carry).floor = None :=
  rewrite token

theorem staleBlocks ∀ (column: Nat) (blocks: List (Option Nat)): startBlocks False column blocks = blocks :=
  match blocks with | [] | [_, .._] => byComputing

--| After an element that starts no line, what is in force is what was.
theorem openedNone ∀ (state: HangState):
    inForce (openedBy state None).blocks (openedBy state None).top = inForce state.blocks state.top :=
  rewrite Bool.andFalse state.start, staleBlocks 0 state.blocks

--| After an element that starts a line at `column`, nothing is in force right of it.
theorem openedSome ∀ [state: HangState] (column: Nat)
    (left: (inForce state.blocks state.top <= column) = True):
    (inForce (openedBy state (Some column)).blocks (openedBy state (Some column)).top <= column) = True :=
  match state, left with
    | { blocks, top, start = False, glue }, left => rewrite staleBlocks column blocks then left
    | { blocks = ([] | [_, .._]), top, start = True, glue }, _ => rewrite Nat.leRefl column

--| After a word written at a seat, nothing is in force right of the line's indentation.
--|
--| Proof idea: mid-line the fold doesn't move; at a line start, or on the comment break after a waiting comment,
--| the word starts the line, right of what is in force, and is the most the fold can put in force (`openedSome`).
theorem wordEnded ∀ [indent column: Nat] [before: Bool] [text: Text] [state: HangState] [place: Place]
    (token: text.startsWith "--" = False)
    (seated: Seated column before state place)
    (room: Room state (wordStart indent place)):
    Ended (openedBy state (wordStart indent place)) False (wordAfter indent text place) :=
  match place, seated, room with
    | AtStart at carry | Broken at carry, (_, _), (_, _) => (floorAfterToken text carry token, openedSome at arithmetic)
    | Mid at carry, (_, left), _ => (floorAfterToken text carry token, rewrite openedNone state then left)
    | Held at carry, (_, _, _), (_, right) => (
      floorAfterToken text (carry.breakTo (Nat.max indent (at + 2))) token,
      openedSome (floored carry (Nat.max indent (at + 2))) arithmetic
    )

--| A plain token's text, written where the place says, folds as one plain token, and leaves the printer after it.
theorem plainStep ∀ (kinds: Text → Tok) (text: Text) (indent column: Nat) (before: Bool)
    (state: HangState) (entry: Place)
    (plain: Plain (kinds text))
    (token: text.startsWith "--" = False)
    (solid: isLayout text = False):
    HangLays kinds
      (Doc.text text)
      indent
      (Entered indent column before state entry (wordStart indent entry))
      (place hang =>
        place = wordAfter indent text entry
          ∧ Ended (openedBy state (wordStart indent entry)) False place
          ∧ hang = At (openedBy state (wordStart indent entry))) :=
  hangsChunk kinds text text.length indent
    (Entered indent column before state entry (wordStart indent entry))
    (place hang =>
      place = wordAfter indent text entry
        ∧ Ended (openedBy state (wordStart indent entry)) False place
        ∧ hang = At (openedBy state (wordStart indent entry)))
    solid
    (place trace (isEntry, hang, seat) =>
      match seat with
        | (seated, _, _, room) =>
          rewrite isEntry, hang then
            (
              byComputing,
              wordEnded token seated room,
              stepPlain kinds state text
                (wordStart indent entry)
                (tokenCode text (wordStart indent entry) token solid)
                plain
                room
            ))

--| After a word the printer is mid-line.
theorem wordAfterMid ∀ (indent: Nat) (text: Text) (place: Place):
    ∃ (at: Nat) => ∃ (carry: Carry) => wordAfter indent text place = Mid at carry :=
  match place with
    | AtStart at carry | Broken at carry | Mid at carry => (at, floorAfter text carry, byComputing)
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
theorem plainLeafHangs ∀ (kinds: Text → Tok) (word: Word) (around: Around) (key indent column: Nat)
    (plain: Plain (kinds word.text))
    (token: word.text.startsWith "--" = False)
    (solid: isLayout word.text = False)
    (closer: isCloserText word.text = False)
    (comma: (word.text == ",") = False)
    (bare: word.leading around key = [])
    (trails: TrailsComment word):
    ElHangs kinds (word.leaf around key) indent column around.before word.trails wordStart :=
  state entry =>
    let step := plainStep kinds word.text indent column around.before state entry plain token solid
    let pre := Entered indent column around.before state entry (wordStart indent entry)
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
          hangsConcat (hangsLast (hangsPost [post := mid] step (place hang (_, ended, folded) => (ended, folded))))
        | Some comment, (isComment, layout) =>
          hangsConcat
            (hangsTwo step
              (hangsSuffix kinds indent mid (post True) isComment layout (place hang (isAfter, ended, folded) =>
                match mids place isAfter with
                  | (at, carry, isMid) =>
                    match carry, rewrite isMid at ended then ended with
                      | carry, (floor, left) => (at, carry, (isMid, (byComputing, floor, left), folded)))))

--| With no item, type or body starting and nothing glued, an element leaves the fold as it found it.
theorem openedQuiet ∀ [state: HangState] (start: Option Nat)
    (quiet: state.start = False)
    (unglued: state.glue = False):
    openedBy state start = state :=
  match state, quiet, unglued with | { blocks = ([] | [_, .._]), top, start = False, glue = False }, _, _ => byComputing

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
    Seat indent indent before state place (wordStart indent place) :=
  match place, ended with
    | Mid at carry, ended => (ended, Nat.leRefl indent, clear, byComputing)
    | Held at carry, (trails, floor, left) =>
      let landed: floored carry (Nat.max indent (at + 2)) = Nat.max indent (at + 2) := rewrite floor
      ((trails, floor, left), Nat.leRefl indent, clear, (unglued, rewrite landed then arithmetic))

--| The fold after an element starts nothing and glues nothing.
theorem openedQuietStart ∀ (state: HangState) (start: Option Nat): (openedBy state start).start = False := byComputing

theorem openedUnglued ∀ (state: HangState) (start: Option Nat): (openedBy state start).glue = False := byComputing

--| An element after words is a part.
theorem elPart ∀ (kinds: Text → Tok) (doc: Doc) (indent: Nat) (before trails: Bool)
    (el: ElHangs kinds doc indent indent before trails wordStart):
    PartHangs kinds doc indent before trails :=
  state entry quiet unglued =>
    let pre: Place → Hang → Prop := place hang =>
      place = entry ∧ hang = At state ∧ Ended state before entry ∧ (inForce state.blocks state.top <= indent) = True
    let opened := openedBy state (wordStart indent entry)
    hangsPost
      (hangsPre (el state entry) (place hang (isEntry, folded, ended, clear) =>
        (isEntry, folded, endedSeat indent before state entry unglued ended clear)))
      (place hang (ended, folded) =>
        let same: opened = state := openedQuiet (wordStart indent entry) quiet unglued
        (rewrite same at ended then ended, rewrite same at folded then folded))

--| An element that may start after a waiting comment may start anywhere else.
theorem elUnheld ∀ (kinds: Text → Tok) (doc: Doc) (indent column: Nat)
    (before trails: Bool) (start: Nat → Place → Option Nat)
    (el: ElHangs kinds doc indent column before trails start):
    ElHangs kinds doc indent column False trails start :=
  state entry =>
    hangsPre (el state entry) (place hang (isEntry, folded, (seated, below, clear, room)) =>
      let held: Seated column before state entry := match entry, seated with
        | AtStart _ _ | Broken _ _ | Mid _ _, seated => seated
        | Held at carry, (never, _, _) => (Bool.falseNotTrue never).impossible
      (isEntry, folded, (held, below, clear, room)))

--| Where a displaced element's contents are seated, laid at `inset`: the line's column at a line start.
def lineSeat (inset: Nat) (place: Place): Nat := match place with
  | AtStart at _ | Broken at _ => at
  | _ => inset

--| A displaced element: its contents start where it does, at the start of a line after a waiting comment, and
--| are indented from there.
--|
--| Proof idea: `DisplacedHolds` gives the contents a seat at the column their first word is written at; at a line
--| start that is the seat's column, laid at the element's indentation (`Nat.max indent at` is `indent`, the seat
--| being no deeper), after a waiting comment the comment break's, with no floor.
theorem displacedHangs ∀ (kinds: Text → Tok) (inner: Doc) (indent column: Nat) (before trails: Bool)
    (el: ∀ (inset seat: Nat) => ElHangs kinds inner inset seat False trails wordStart):
    ElHangs kinds (Displaced inner) indent column before trails wordStart :=
  state entry =>
    let post: Place → Hang → Prop := place hang =>
      Ended (openedBy state (wordStart indent entry)) trails place ∧ hang = At (openedBy state (wordStart indent entry))
    let seat: Nat → Place → Hang → Prop := inset place hang =>
      Entered inset (lineSeat inset place) False state place (wordStart inset place) place hang
        ∧ wordStart inset place = wordStart indent entry
    hangsDisplaced kinds inner indent
      (Entered indent column before state entry (wordStart indent entry))
      post
      seat
      (inset =>
        hangsBy (place trace next (entered, same) after =>
          laysBy (el inset (lineSeat inset place) state place) place trace next entered (left later (ended, folded) =>
            after left later (rewrite same at ended then ended, rewrite same at folded then folded))))
      (place hang (isEntry, folded, (seated, below, clear, room)) =>
        rewrite isEntry then
          match entry, seated, room with
            | AtStart at _ | Broken at _, (atColumn, landed), room =>
              let deep: (at <= Nat.max indent at) = True := arithmetic
              let wide: (inForce state.blocks state.top <= Nat.max indent at) = True := arithmetic
              ((byComputing, folded, (byComputing, rewrite atColumn then landed), deep, wide, room), byComputing)
            | Mid at carry, seated, room => ((byComputing, folded, seated, Nat.leRefl indent, clear, room), byComputing)
            | Held at carry, (_, floor, _), room =>
              let broken := Nat.max indent (at + 2)
              let wide: (inForce state.blocks state.top <= broken) = True := arithmetic
              let landed: floored carry broken = broken := rewrite floor
              let deep: (floored carry broken <= broken) = True := rewrite landed then Nat.leRefl broken
              ((byComputing, folded, (byComputing, rewrite landed then landed), deep, wide, room), byComputing))

--| A node that isn't displaced has no comment waiting before it.
theorem displacesUnheld ∀ (first: Word) (around: Around)
    (placed: first.displaces around = False):
    around.before = False :=
  Bool.orFalseRight _ _ (Bool.orFalseRight _ _ placed)

--| A node framed by its first token, whose own-line comments an enclosing element wrote, or that has none: the node,
--| displaced or not (`Word.displaces`).
theorem framedHangs ∀ [kinds: Text → Tok] (first: Word) [around: Around] (doc: Doc) (indent column: Nat) (trails: Bool)
    (bare: first.leading around around.at = [])
    (el: ∀ (inset seat: Nat) => ElHangs kinds doc inset seat False trails wordStart):
    ElHangs kinds (framedBy first around doc) indent column around.before trails wordStart :=
  state entry =>
    let pre := Entered indent column around.before state entry (wordStart indent entry)
    let post: Place → Hang → Prop := place hang =>
      Ended (openedBy state (wordStart indent entry)) trails place ∧ hang = At (openedBy state (wordStart indent entry))
    rewrite bare then
      match placed: first.displaces around with
        | True =>
          hangsConcat
            (hangsCons
              [Displaced doc]
              (hangsNothing kinds indent pre)
              (hangsLast (displacedHangs kinds doc indent column around.before trails el state entry)))
        | False =>
          let unheld: around.before = False := displacesUnheld first around placed
          hangsConcat
            (hangsCons
              [doc]
              (hangsNothing kinds indent pre)
              (hangsLast (rewrite unheld then el indent column state entry)))

--| Where no comment waits, an element's first word keeps what is in force at the indentation or left of it.
theorem openedBound ∀ [indent column: Nat] [state: HangState] [entry: Place]
    (seated: Seated column False state entry)
    (below: (column <= indent) = True)
    (clear: (inForce state.blocks state.top <= indent) = True)
    (room: Room state (wordStart indent entry)):
    (inForce (openedBy state (wordStart indent entry)).blocks (openedBy state (wordStart indent entry)).top <= indent)
      = True :=
  match entry, seated, room with
    | AtStart at _ | Broken at _, (atColumn, _), (_, _) =>
      let bound := openedSome at arithmetic
      let deep: (at <= indent) = True := rewrite atColumn then below
      arithmetic
    | Mid at carry, _, _ => rewrite openedNone state then clear
    | Held at carry, (never, _, _), _ => (Bool.falseNotTrue never).impossible

--| An element, then a part after it.
theorem elThen ∀ [kinds: Text → Tok] (first part: Doc) [indent column: Nat] [middle trails: Bool]
    (head: ElHangs kinds first indent column False middle wordStart)
    (rest: PartHangs kinds part indent middle trails):
    ElHangs kinds (Doc.concat [first, part]) indent column False trails wordStart :=
  state entry =>
    hangsBy (place trace next entered after =>
      let pre := Entered indent column False state entry (wordStart indent entry)
      let opened := openedBy state (wordStart indent entry)
      let mid: Place → Hang → Prop := place hang => Ended opened middle place ∧ hang = At opened
      let post: Place → Hang → Prop := place hang => Ended opened trails place ∧ hang = At opened
      match entered with
        | (_, _, (seated, below, clear, room)) =>
          let bound := openedBound seated below clear room
          laysBy
            (hangsConcat
              [pre := pre]
              [post := post]
              (hangsTwo
                (head state entry)
                (hangsBy (between later next (ended, folded) onward =>
                  laysBy
                    (rest opened between
                      (openedQuietStart state (wordStart indent entry))
                      (openedUnglued state (wordStart indent entry)))
                    between
                    later
                    next
                    (byComputing, folded, ended, bound)
                    onward))))
            place
            trace
            next
            entered
            after)

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
  hangsBy (place trace next holds after =>
    match isGap with
      | Inl isNothing => rewrite isNothing then after place trace holds
      | Inr isSpace =>
        rewrite isSpace then
          match place, holds with
            | Mid at carry, ((floor, left), folded, bound) =>
              after (Mid at (floorAfter " " carry)) trace ((byComputing, left), folded, bound)
            | Held at carry, holds => after (Held at carry) trace holds
            | AtStart at carry, (never, _, _) => (Bool.falseNotTrue never).impossible
            | Broken at carry, (never, _, _) => (Bool.falseNotTrue never).impossible)

--| An element, a gap, then a part after it.
theorem elGapThen ∀ [kinds: Text → Tok] (first gap part: Doc) [indent column: Nat] [middle trails: Bool]
    (head: ElHangs kinds first indent column False middle wordStart)
    (isGap: Gap gap)
    (rest: PartHangs kinds part indent middle trails):
    ElHangs kinds (Doc.concat [first, gap, part]) indent column False trails wordStart :=
  state entry =>
    hangsBy (place trace next entered after =>
      let pre := Entered indent column False state entry (wordStart indent entry)
      let opened := openedBy state (wordStart indent entry)
      match entered with
        | (_, _, (seated, below, clear, room)) =>
          let bound := openedBound seated below clear room
          let mid: Place → Hang → Prop := place hang =>
            Ended opened middle place ∧ hang = At opened ∧ (inForce opened.blocks opened.top <= indent) = True
          let post: Place → Hang → Prop := place hang => Ended opened trails place ∧ hang = At opened
          laysBy
            (hangsConcat
              [pre := pre]
              [post := post]
              (hangsCons
                [gap, part]
                (hangsPost (head state entry) (place hang (ended, folded) => (ended, folded, bound)))
                (hangsTwo
                  (gapKeeps kinds gap indent opened middle ((inForce opened.blocks opened.top <= indent) = True) isGap)
                  (hangsBy (between later next (ended, folded, bound) onward =>
                    laysBy
                      (rest opened between
                        (openedQuietStart state (wordStart indent entry))
                        (openedUnglued state (wordStart indent entry)))
                      between
                      later
                      next
                      (byComputing, folded, ended, bound)
                      onward)))))
            place
            trace
            next
            entered
            after)

-- Own-line comments.

--| Own-line comments the lexer reads as comments.
def NotesComment: List Note → Prop
  | [] => True
  | [note, ..rest] => IsComment note.text ∧ isLayout note.text = False ∧ NotesComment rest

--| At the start of a line at `column`, whose breaks land there (`floored`), with the fold at `hang`.
def LineAt (indent column: Nat) (hang: Hang) (place: Place) (now: Hang): Prop := match place with
  | AtStart at carry | Broken at carry => now = hang ∧ at = column ∧ floored carry indent = column
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
  hangsTwo
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
        | AtStart _ _ | Broken _ _, never => (Bool.falseNotTrue never).impossible
        | Held at carry, never => (Bool.falseNotTrue never).impossible))

theorem brokenLine ∀ (indent column: Nat) (hang: Hang) (place: Place) (now: Hang)
    (broken: BrokenAt indent column hang place now):
    LineAt indent column hang place now :=
  match place, broken with
    | Broken at carry, holds => holds
    | AtStart _ _ | Mid _ _ | Held _ _, never => (Bool.falseNotTrue never).impossible

--| A blank line kept right after a line break.
theorem blankHangs ∀ (kinds: Text → Tok) (indent column: Nat) (hang: Hang):
    HangLays kinds Blank indent (BrokenAt indent column hang) (LineAt indent column hang) :=
  hangsBlank kinds indent (BrokenAt indent column hang) (LineAt indent column hang) (place trace broken =>
    match place, broken with
      | Broken at carry, holds => rewrite blankHang kinds trace then holds
      | AtStart _ _ | Mid _ _, never => (Bool.falseNotTrue never).impossible
      | Held at carry, never => (Bool.falseNotTrue never).impossible)

--| Own-line comments after the first, each on its line, a blank line above one kept.
theorem laterNotesHang ∀ (kinds: Text → Tok) (notes: List Note) (indent column: Nat) (hang: Hang)
    (comments: NotesComment notes):
    HangLaysAll kinds (notesAbove notes) indent (BrokenAt indent column hang) (BrokenAt indent column hang) :=
  match notes, comments with
    | [], _ =>
      hangsNil kinds indent (BrokenAt indent column hang) (BrokenAt indent column hang) (place now held => held)
    | [note, ..rest], (comment, solid, others) =>
      let line := noteHangs kinds note.text indent column hang comment solid
      let more := laterNotesHang kinds rest indent column hang others
      match blank: note.blankBefore with
        | True =>
          hangsCons
            ([Doc.text note.text, HardLine] ++ notesAbove rest)
            (blankHangs kinds indent column hang)
            (hangsAppend line more)
        | False => hangsAppend (allHangsPre line (brokenLine indent column hang)) more

--| A token's own-line comments, each on its line, right after a line break, a blank line above the first kept.
theorem notesHangBroken ∀ (kinds: Text → Tok) (note: Note) (rest: List Note) (indent column: Nat) (hang: Hang)
    (comments: NotesComment [note, ..rest]):
    HangLaysAll kinds (notesAbove [note, ..rest]) indent (BrokenAt indent column hang) (BrokenAt indent column hang) :=
  laterNotesHang kinds [note, ..rest] indent column hang comments

--| Whether the place is a line start that needn't follow a line break, where a `Blank` may print nothing.
def plainStart: Place → Bool
  | AtStart _ _ => True
  | _ => False

--| Where a token with own-line comments above it starts its line: right after a line break if it is entered there,
--| else on the comment break `LineStart` makes. It is never entered at a plain line start, where a blank line kept
--| above its first comment might print nothing: there the column is 0, which leaves no room (`Room`), so no seat is
--| there (`leadFresh`).
def leadColumn (indent: Nat) (place: Place): Nat := match place with
  | AtStart _ _ => 0
  | Broken at _ => at
  | Mid at _ | Held at _ => Nat.max indent (at + 2)

def leadStart (indent: Nat) (place: Place): Option Nat := Some (leadColumn indent place)

--| An element whose first token has own-line comments above it, which it writes, has room only where it isn't at a
--| plain line start.
theorem leadFresh ∀ [indent: Nat] [state: HangState] [entry: Place]
    (room: Room state (leadStart indent entry)):
    plainStart entry = False :=
  match entry, room with
    | AtStart at carry, (_, never) =>
      let none: (0 > inForce state.blocks state.top) = False := arithmetic
      (Bool.falseNotTrue (rewrite none at never then never)).impossible
    | Broken _ _ | Mid _ _ | Held _ _, _ => byComputing

--| Where an element's first token starts its line, if it does: `leadStart` if the element writes own-line comments
--| above it (`noted`), else `wordStart`. The two agree at a line start.
def startFor (noted: Bool): Nat → Place → Option Nat := match noted with
  | True => leadStart
  | False => wordStart

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

--| A `LineStart` from a seat that isn't a plain line start, then a token's own-line comments, each on its line, a
--| blank line above one kept.
theorem startNotesHang ∀ (kinds: Text → Tok) (indent: Nat) (before: Bool) (state: HangState) (entry: Place)
    (note: Note) (rest: List Note)
    (comments: NotesComment [note, ..rest])
    (fresh: plainStart entry = False):
    HangLaysAll kinds
      [LineStart, ..notesAbove [note, ..rest]]
      indent
      (place hang => place = entry ∧ hang = At state ∧ Seated indent before state entry)
      (BrokenAt indent (leadColumn indent entry) (At state)) :=
  let pre: Place → Hang → Prop := place hang => place = entry ∧ hang = At state ∧ Seated indent before state entry
  let column := leadColumn indent entry
  hangsCons
    (notesAbove [note, ..rest])
    (startHangsBroken kinds indent before state entry fresh)
    (notesHangBroken kinds note rest indent column (At state) comments)

--| A token's own-line comments and the blank line kept above it, from a seat: to the start of the token's line.
theorem leadingHangs ∀ (kinds: Text → Tok) [word: Word] [around: Around] (key indent: Nat) (before: Bool)
    (state: HangState) [entry: Place] [note: Note] (rest: List Note)
    (hoisted: around.hoisted = False)
    (noted: word.comments.above = [note, ..rest])
    (closer: isCloserText word.text = False)
    (comments: NotesComment [note, ..rest])
    (fresh: plainStart entry = False):
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
    hangsCons
      ([LineStart] ++ notesAbove [note, ..rest])
      (hangsBreakParent kinds indent pre)
      (startNotesHang kinds indent before state entry note rest comments fresh)
  rewrite hoisted, noted, closer then
    match blank: word.comments.blankBefore with
      | True => hangsAppend front (hangsLast (blankHangs kinds indent column (At state)))
      | False => hangsAppend front (hangsNil kinds indent broken lined (brokenLine indent column (At state)))

-- Tokens with own-line comments above them.

--| A word's trailing comment, if it has one, after a word that ends an element: it waits after the word.
theorem trailingHangs ∀ (kinds: Text → Tok) [word: Word] (indent: Nat) (state: HangState)
    (trailed: TrailsComment word):
    HangLaysAll kinds word.trailing indent (place hang => Ended state False place ∧ hang = At state) (place hang =>
      Ended state word.trails place ∧ hang = At state) :=
  let pre: Place → Hang → Prop := place hang => Ended state False place ∧ hang = At state
  let post: Place → Hang → Prop := place hang => Ended state True place ∧ hang = At state
  match after: word.comments.after, trailed with
    | None, _ => hangsNil kinds indent pre pre (place hang held => held)
    | Some comment, (isComment, layout) =>
      hangsLast
        (hangsSuffix kinds indent pre post isComment layout (place hang (ended, folded) =>
          match place, ended with
            | Mid at carry, (floor, left) => (at, carry, (byComputing, (byComputing, floor, left), folded))
            | Held at carry, (never, _, _) => (Bool.falseNotTrue never).impossible
            | AtStart at carry, never => (Bool.falseNotTrue never).impossible
            | Broken at carry, never => (Bool.falseNotTrue never).impossible))

--| A plain token at the start of a line at `column`, right of what is in force: one plain token there.
theorem lineWordHangs ∀ (kinds: Text → Tok) (text: Text) (indent column: Nat) (state: HangState)
    (plain: Plain (kinds text))
    (token: text.startsWith "--" = False)
    (solid: isLayout text = False)
    (room: Room state (Some column)):
    HangLays kinds (Doc.text text) indent (LineAt indent column (At state)) (place hang =>
      Ended (openedBy state (Some column)) False place ∧ hang = At (openedBy state (Some column))) :=
  let post: Place → Hang → Prop := place hang =>
    Ended (openedBy state (Some column)) False place ∧ hang = At (openedBy state (Some column))
  let (_, right) := room
  let bound: (inForce (openedBy state (Some column)).blocks (openedBy state (Some column)).top <= column) = True :=
    openedSome column arithmetic
  let step := stepPlain kinds state text (Some column) (tokenCode text (Some column) token solid) plain room
  hangsChunk kinds text text.length indent (LineAt indent column (At state)) post solid (place trace lined =>
    match place, lined with
      | AtStart _ carry | Broken _ carry, (now, atColumn, _) =>
        rewrite now, atColumn then ((floorAfterToken text carry token, bound), step)
      | Mid at carry, never => (Bool.falseNotTrue never).impossible
      | Held at carry, never => (Bool.falseNotTrue never).impossible)

--| A token that is neither a closer nor a comma: its comments and blank line, the token's text, its trailing
--| comment.
theorem leafPiece ∀ (word: Word) (around: Around) (key: Nat)
    (closer: isCloserText word.text = False)
    (comma: (word.text == ",") = False):
    word.leaf around key = Doc.concat (word.leading around key ++ [Doc.text word.text, ..word.trailing]) :=
  rewrite closer, comma

--| A plain token with own-line comments above it, from a seat: the comments, each on its line, then the token
--| starting the line after them (`leadStart`), then its trailing comment, if any. Its seat leaves room for that
--| line, so it isn't a plain line start (`leadFresh`), where a blank line above the first comment might print nothing.
--|
--| Proof idea: `leadingHangs` takes the seat to the start of the token's line, with the fold unchanged, and
--| `lineWordHangs` writes the token there, right of what is in force by the seat's `Room`.
theorem notedLeafHangs ∀ [kinds: Text → Tok] [word: Word] [around: Around] (key indent: Nat) (state: HangState)
    (entry: Place) [note: Note] (rest: List Note)
    (plain: Plain (kinds word.text))
    (token: word.text.startsWith "--" = False)
    (solid: isLayout word.text = False)
    (closer: isCloserText word.text = False)
    (comma: (word.text == ",") = False)
    (hoisted: around.hoisted = False)
    (noted: word.comments.above = [note, ..rest])
    (comments: NotesComment [note, ..rest])
    (trailed: TrailsComment word):
    HangLays kinds
      (word.leaf around key)
      indent
      (Entered indent indent around.before state entry (leadStart indent entry))
      (place hang =>
        Ended (openedBy state (leadStart indent entry)) word.trails place
          ∧ hang = At (openedBy state (leadStart indent entry))) :=
  hangsBy (place trace next entered after =>
    match entered with
      | (_, _, (_, _, _, room)) =>
        let column := leadColumn indent entry
        let opened := openedBy state (Some column)
        let fresh := leadFresh room
        let pre := Entered indent indent around.before state entry (leadStart indent entry)
        let lined := LineAt indent column (At state)
        let written: Place → Hang → Prop := place hang => Ended opened False place ∧ hang = At opened
        let post: Place → Hang → Prop := place hang => Ended opened word.trails place ∧ hang = At opened
        let leading :=
          allHangsPre
            [weaker := pre]
            (leadingHangs kinds key indent around.before state rest hoisted noted closer comments fresh)
            (place hang (isEntry, folded, (seated, _, _, _)) => (isEntry, folded, seated))
        rewrite leafPiece word around key closer comma then
          laysBy
            (hangsConcat
              (hangsAppend leading
                (hangsCons word.trailing
                  (lineWordHangs kinds word.text indent column state plain token solid room)
                  (trailingHangs kinds indent opened trailed))))
            place
            trace
            next
            entered
            after)

--| Where an element ended no line starts, so no blank line above a comment there can print nothing.
theorem endedFresh ∀ (state: HangState) (trails: Bool) (place: Place)
    (ended: Ended state trails place):
    plainStart place = False :=
  match place, ended with
    | Mid _ _ | Held _ _, _ => byComputing
    | AtStart _ _ | Broken _ _, never => (Bool.falseNotTrue never).impossible

--| Where an element ended, a token with own-line comments may start: the comment break is right of the line.
theorem endedLead ∀ (indent: Nat) (before: Bool) (state: HangState) (place: Place)
    (unglued: state.glue = False)
    (ended: Ended state before place)
    (clear: (inForce state.blocks state.top <= indent) = True):
    Seat indent indent before state place (leadStart indent place) :=
  match place, ended with
    | Mid at carry, (floor, left) => ((floor, left), Nat.leRefl indent, clear, (unglued, arithmetic))
    | Held at carry, (trails, floor, left) => ((trails, floor, left), Nat.leRefl indent, clear, (unglued, arithmetic))

--| A plain token with own-line comments above it, as a later part of an element: its comments break the line, and
--| the fold, with no item starting, is as it was.
theorem notedPartHangs ∀ (kinds: Text → Tok) (word: Word) (around: Around) (key indent: Nat)
    (note: Note) (rest: List Note)
    (plain: Plain (kinds word.text))
    (token: word.text.startsWith "--" = False)
    (solid: isLayout word.text = False)
    (closer: isCloserText word.text = False)
    (comma: (word.text == ",") = False)
    (hoisted: around.hoisted = False)
    (noted: word.comments.above = [note, ..rest])
    (comments: NotesComment [note, ..rest])
    (trailed: TrailsComment word):
    PartHangs kinds (word.leaf around key) indent around.before word.trails :=
  state entry quiet unglued =>
    hangsBy (place trace next holds after =>
      match holds with
        | (isEntry, folded, ended, clear) =>
          let opened := openedBy state (leadStart indent entry)
          let same: opened = state := openedQuiet (leadStart indent entry) quiet unglued
          laysBy
            (hangsPost
              [weaker := place hang => Ended state word.trails place ∧ hang = At state]
              (hangsPre
                [weaker := place hang =>
                  place = entry
                    ∧ hang = At state
                    ∧ Ended state around.before entry
                    ∧ (inForce state.blocks state.top <= indent) = True]
                (notedLeafHangs key indent state entry rest plain token solid closer comma hoisted noted comments
                    trailed)
                (place hang (isEntry, folded, ended, clear) =>
                  (isEntry, folded, endedLead indent around.before state entry unglued ended clear)))
              (place hang (ended, folded) => (rewrite same at ended then ended, rewrite same at folded then folded)))
            place
            trace
            next
            holds
            after)

-- Nodes with own-line comments above their first token.

--| A token's own-line comments end at or right of the indentation.
theorem leadDeep ∀ (indent: Nat) (before: Bool) (state: HangState) (entry: Place)
    (seated: Seated indent before state entry)
    (fresh: plainStart entry = False):
    (indent <= leadColumn indent entry) = True :=
  match entry, seated, fresh with
    | AtStart at carry, _, never => (Bool.trueNotFalse never).impossible
    | Broken at carry, (atColumn, _), _ => rewrite atColumn then Nat.leRefl indent
    | Mid _ _ | Held _ _, _, _ => arithmetic

--| A line start at `column`, the comment floor no deeper than the indentation's: the floor is no deeper at `column`.
theorem flooredDeeper ∀ (carry: Carry) (indent column: Nat)
    (landed: floored carry indent = column)
    (deep: (indent <= column) = True):
    floored carry column = column :=
  match floor: carry.floor with
    | None => byComputing
    | Some least => arithmetic

--| Where the comments above a node's first token leave the printer, at the start of the line at `column`, the node
--| displaced there lays as it does with its first token's comments written elsewhere, laid at that column.
--|
--| Proof idea: at a line start, `Displaced` lays its contents at the line's column if deeper, whatever the
--| indentation: `column`, at or right of `indent`. The hoisted form, `Doc.concat [Doc.concat [], Displaced doc]`, lays
--| as `Displaced doc` does, so `framed` at `column`, entered at the line start with the seat's room, gives it.
theorem linedDisplaced ∀ (kinds: Text → Tok) (doc: Doc) (indent column: Nat) (before trails: Bool) (state: HangState)
    (deep: (indent <= column) = True)
    (room: Room state (Some column))
    (framed: ∀ (inset: Nat) => ElHangs kinds
      (Doc.concat [Doc.concat [], Displaced doc])
      inset
      inset
      before
      trails
      wordStart):
    HangLays kinds (Displaced doc) indent (LineAt indent column (At state)) (place hang =>
      Ended (openedBy state (Some column)) trails place ∧ hang = At (openedBy state (Some column))) :=
  hangsBy (place trace next lineAt after =>
    match place, lineAt with
      | AtStart at carry, (now, atColumn, landed) =>
        let wide: Nat.max indent at = at := rewrite atColumn then arithmetic
        let same: Nat.max at at = at := arithmetic
        let floorAt: floored carry at = at := rewrite atColumn then flooredDeeper carry indent column landed deep
        let laid: Lays (Doc.concat [Doc.concat [], Displaced doc]) at (AtStart at carry) trace next :=
          laysBy
            (framed at state (AtStart at carry))
            (AtStart at carry)
            trace
            next
            (
              byComputing,
              now,
              ((byComputing, floorAt), Nat.leRefl at, rewrite atColumn then arithmetic, rewrite atColumn then room)
            )
            (left later (ended, folded) =>
              after left later (rewrite atColumn at ended then ended, rewrite atColumn at folded then folded))
        let inner: Lays doc (Nat.max at at) (AtStart at carry) trace next := laid
        let target: Lays doc (Nat.max indent at) (AtStart at carry) trace next :=
          rewrite wide then (rewrite same at inner then inner)
        target
      | Broken at carry, (now, atColumn, landed) =>
        let wide: Nat.max indent at = at := rewrite atColumn then arithmetic
        let same: Nat.max at at = at := arithmetic
        let floorAt: floored carry at = at := rewrite atColumn then flooredDeeper carry indent column landed deep
        let laid: Lays (Doc.concat [Doc.concat [], Displaced doc]) at (Broken at carry) trace next :=
          laysBy
            (framed at state (Broken at carry))
            (Broken at carry)
            trace
            next
            (
              byComputing,
              now,
              ((byComputing, floorAt), Nat.leRefl at, rewrite atColumn then arithmetic, rewrite atColumn then room)
            )
            (left later (ended, folded) =>
              after left later (rewrite atColumn at ended then ended, rewrite atColumn at folded then folded))
        let inner: Lays doc (Nat.max at at) (Broken at carry) trace next := laid
        let target: Lays doc (Nat.max indent at) (Broken at carry) trace next :=
          rewrite wide then (rewrite same at inner then inner)
        target
      | Mid _ _ | Held _ _, never => (Bool.falseNotTrue never).impossible)

--| A node whose first token has own-line comments above it that the node writes: the comments from its seat, each
--| on its line, then the node displaced to the start of the line after them, its first token there (`leadStart`).
--| `framed` is the node with those comments written elsewhere (`hoisted`), which displaces it the same way.
--|
--| Proof idea: `leadingHangs` takes the seat to the start of the token's line at `leadColumn`, the fold unchanged;
--| `linedDisplaced` lays the node from there, with room by the seat's `Room`.
theorem notedFramedHangs ∀ (kinds: Text → Tok) (first: Word) (around: Around) (doc: Doc) (indent: Nat) (trails: Bool)
    (note: Note) (rest: List Note)
    (hoisted: around.hoisted = False)
    (noted: first.comments.above = [note, ..rest])
    (closer: isCloserText first.text = False)
    (comments: NotesComment [note, ..rest])
    (framed: ∀ (inset: Nat) => ElHangs kinds
      (Doc.concat [Doc.concat [], Displaced doc])
      inset
      inset
      around.before
      trails
      wordStart):
    ElHangs kinds (framedBy first around doc) indent indent around.before trails leadStart :=
  state entry =>
    hangsBy (place trace next entered after =>
      match entered with
        | (_, _, (seated, _, _, room)) =>
          let column := leadColumn indent entry
          let opened := openedBy state (Some column)
          let pre := Entered indent indent around.before state entry (leadStart indent entry)
          let lined := LineAt indent column (At state)
          let post: Place → Hang → Prop := place hang => Ended opened trails place ∧ hang = At opened
          let leadingDocs := first.leading around around.at
          let leading :=
            hangsConcat
              (allHangsPre
                [weaker := pre]
                (leadingHangs kinds around.at indent around.before state rest hoisted noted closer comments
                  (leadFresh room))
                (place hang (isEntry, folded, (seated, _, _, _)) => (isEntry, folded, seated)))
          let displaced :=
            linedDisplaced kinds doc indent column around.before trails state
              (leadDeep indent around.before state entry seated (leadFresh room))
              room
              framed
          let isNoted: first.noted = True := rewrite noted
          let unframed: framedBy first around doc = Doc.concat [Doc.concat leadingDocs, Displaced doc] :=
            rewrite isNoted
          rewrite unframed then laysBy (hangsConcat (hangsTwo leading displaced)) place trace next entered after)

-- Closers.

--| A line break's lowering finds the mark it found before, its least indentation lowered to the line.
theorem findLower ∀ (line key: Nat) (marks: List OpenMark):
    (lowerMarks line marks).find (mark => mark.key == key)
      = (marks.find (mark => mark.key == key)).map (mark => { mark | least = Some (lowest mark.least line) }) :=
  match marks with
    | [] => byComputing
    | [mark, ..rest] =>
      match same: mark.key == key with
        | True => byComputing
        | False => findLower line key rest

--| A `CloserLine` lands at the construct's indentation or left of it.
theorem closerAtMost ∀ (carry: Carry) (key indent: Nat): (carry.closerAt key indent <= indent) = True :=
  match found: carry.marks.find (mark => mark.key == key) with
    | None => Nat.leRefl indent
    | Some { key = marked_key, marked, least = None } => Nat.leRefl indent
    | Some { key = marked_key, marked, least = Some least } =>
      match low: least <= indent with
        | True => arithmetic
        | False => Nat.leRefl indent

--| A line deeper than the construct leaves where its `CloserLine` lands as it was: whether a line since the mark is
--| at or left of the indentation doesn't change.
theorem closerAtLower ∀ (carry: Carry) (key indent line: Nat)
    (deep: indent < line):
    { carry | marks = lowerMarks line carry.marks }.closerAt key indent = carry.closerAt key indent :=
  rewrite findLower line key carry.marks then
    match found: carry.marks.find (mark => mark.key == key) with
      | None => byComputing
      | Some { key = marked_key, marked, least = None } =>
        let high: (line <= indent) = False := (Nat.leqReadsFalse line indent).backward arithmetic
        rewrite high
      | Some { key = marked_key, marked, least = Some least } =>
        match low: least <= indent with
          | True =>
            let lower: (Nat.min least line <= indent) = True := arithmetic
            rewrite lower
          | False =>
            let lower: (Nat.min least line <= indent) = False :=
              (Nat.leqReadsFalse (Nat.min least line) indent).backward arithmetic
            rewrite lower

--| A line break 2 deeper than the construct, with no comment floor, leaves where its `CloserLine` lands.
theorem breakKeepsCloser ∀ (carry: Carry) (key indent: Nat)
    (floor: carry.floor = None):
    (carry.breakTo (indent + 2)).closerAt key indent = carry.closerAt key indent :=
  let landed: floored carry (indent + 2) = indent + 2 := rewrite floor
  rewrite landed then closerAtLower carry key indent (indent + 2) arithmetic

--| At the start of a line of a closer's own-line comments, 2 deeper than the construct: the fold at `hang`, no
--| comment floor, and the closer's own line still landing at `column`.
def NoteStart (indent key column: Nat) (hang: Hang) (place: Place) (now: Hang): Prop := match place with
  | AtStart at carry | Broken at carry =>
    now = hang ∧ at = indent + 2 ∧ carry.floor = None ∧ carry.closerAt key indent = column
  | _ => False = True

--| As `NoteStart`, right after a line break, where a blank line may follow.
def NoteBroken (indent key column: Nat) (hang: Hang) (place: Place) (now: Hang): Prop := match place with
  | Broken at carry => now = hang ∧ at = indent + 2 ∧ carry.floor = None ∧ carry.closerAt key indent = column
  | _ => False = True

--| After one of a closer's own-line comments, on its line.
def NoteWritten (indent key column: Nat) (hang: Hang) (place: Place) (now: Hang): Prop := match place with
  | Mid at carry => now = hang ∧ at = indent + 2 ∧ carry.floor = None ∧ carry.closerAt key indent = column
  | _ => False = True

theorem noteBrokenStart ∀ (indent key column: Nat) (hang: Hang) (place: Place) (now: Hang)
    (broken: NoteBroken indent key column hang place now):
    NoteStart indent key column hang place now :=
  match place, broken with
    | Broken at carry, holds => holds
    | AtStart _ _ | Mid _ _ | Held _ _, never => (Bool.falseNotTrue never).impossible

--| A closer's own-line comment, at the start of its line: the fold skips it.
theorem noteTextHangs ∀ (kinds: Text → Tok) (text: Text) (indent key column: Nat) (hang: Hang)
    (comment: IsComment text)
    (solid: isLayout text = False):
    HangLays kinds
      (Doc.text text)
      (indent + 2)
      (NoteStart indent key column hang)
      (NoteWritten indent key column hang) :=
  let skips := (state: Hang) (start: Option Nat) => commentSkips kinds state { word = text, start } comment
  hangsChunk kinds text text.length
    (indent + 2)
    (NoteStart indent key column hang)
    (NoteWritten indent key column hang)
    solid
    (place trace started =>
      match place, started with
        | AtStart at carry | Broken at carry, (now, atNotes, floor, lands) =>
          rewrite commentKeepsFloor text carry (commentStarts text comment), skips (hangOf kinds trace) (Some at) then
            (now, atNotes, floor, lands)
        | Mid at carry, never => (Bool.falseNotTrue never).impossible
        | Held at carry, never => (Bool.falseNotTrue never).impossible)

--| A line break after one of a closer's own-line comments: to the next one's line, the closer's line unmoved.
theorem noteBreakHangs ∀ (kinds: Text → Tok) (indent key column: Nat) (hang: Hang):
    HangLays kinds HardLine (indent + 2) (NoteWritten indent key column hang) (NoteBroken indent key column hang) :=
  hangsHardBroken kinds
    (indent + 2)
    (NoteWritten indent key column hang)
    (NoteBroken indent key column hang)
    (place now written =>
      match place, written with
        | Mid at carry, (same, _, floor, lands) =>
          let landed: floored carry (indent + 2) = indent + 2 := rewrite floor
          (byComputing, (same, landed, floor, rewrite breakKeepsCloser carry key indent floor then lands))
        | AtStart _ _ | Broken _ _, never => (Bool.falseNotTrue never).impossible
        | Held at carry, never => (Bool.falseNotTrue never).impossible)

--| A blank line kept between a closer's own-line comments.
theorem noteBlankHangs ∀ (kinds: Text → Tok) (indent key column: Nat) (hang: Hang):
    HangLays kinds Blank (indent + 2) (NoteBroken indent key column hang) (NoteStart indent key column hang) :=
  hangsBlank kinds
    (indent + 2)
    (NoteBroken indent key column hang)
    (NoteStart indent key column hang)
    (place trace broken =>
      match place, broken with
        | Broken at carry, holds => rewrite blankHang kinds trace then holds
        | AtStart _ _ | Mid _ _, never => (Bool.falseNotTrue never).impossible
        | Held at carry, never => (Bool.falseNotTrue never).impossible)

--| A closer's own-line comments after the first, each on its line, a blank line above one kept.
theorem laterCloserNotesHang ∀ (kinds: Text → Tok) (notes: List Note) (indent key column: Nat) (hang: Hang)
    (comments: NotesComment notes):
    HangLaysAll kinds
      (laterCloserNotes notes)
      (indent + 2)
      (NoteWritten indent key column hang)
      (NoteWritten indent key column hang) :=
  match notes, comments with
    | [], _ =>
      hangsNil kinds
        (indent + 2)
        (NoteWritten indent key column hang)
        (NoteWritten indent key column hang)
        (place now held => held)
    | [note, ..rest], (comment, solid, others) =>
      let text := noteTextHangs kinds note.text indent key column hang comment solid
      let more := laterCloserNotesHang kinds rest indent key column hang others
      let line := noteBreakHangs kinds indent key column hang
      match blank: note.blankBefore with
        | True =>
          hangsCons
            ([Blank, Doc.text note.text] ++ laterCloserNotes rest)
            line
            (hangsCons
              ([Doc.text note.text] ++ laterCloserNotes rest)
              (noteBlankHangs kinds indent key column hang)
              (hangsCons (laterCloserNotes rest) text more))
        | False =>
          hangsCons
            ([Doc.text note.text] ++ laterCloserNotes rest)
            line
            (hangsCons (laterCloserNotes rest) (hangsPre text (noteBrokenStart indent key column hang)) more)

--| Where a bracket's closer may be written, the fold at `state`: after its contents ended (a comment waiting only if
--| `before`), or right after the line break before it: at the indentation with no comment floor, left of the
--| bracket's block (the innermost), or anywhere if the closer takes a line of its own after a trailing comment
--| (`lone`), as that line break's line then moves to it.
def CloserSeat (indent: Nat) (before lone: Bool) (state: HangState) (place: Place): Prop := match place with
  | AtStart _ _ => False
  | Broken at carry =>
    lone = True ∨ (at = indent ∧ carry.floor = None ∧ leftOf indent (state.blocks.headOr None) = True)
  | Mid at carry => carry.floor = None ∧ (inForce state.blocks state.top <= at) = True
  | Held at carry => before = True ∧ carry.floor = None ∧ (inForce state.blocks state.top <= at) = True

--| Where a closer's line of its own lands, the fold allows it: left of the line its bracket's current item started,
--| if it started one, and not left of what is in force outside the bracket (`outside`).
def CloserFits (key indent: Nat) (block: Option Nat) (outside: Nat) (carry: Carry): Prop :=
  leftOf (carry.closerAt key indent) block = True ∧ (outside <= carry.closerAt key indent) = True

--| A closer with no own-line comments takes a line of its own after code that ends its line with a comment, when it
--| has a trailing comment of its own (`Word.leaf`'s `ownLine`).
def Word.lone (word: Word) (around: Around): Bool := !word.noted && around.before && word.trails

--| Right after a closer's line break, at `column`, with no comment floor.
def LandsAt (column: Nat) (hang: Hang) (place: Place) (now: Hang): Prop := match place with
  | Broken at carry => now = hang ∧ at = column ∧ carry.floor = None
  | _ => False = True

--| An element ended with a comment waiting only if `flag` has, where one waiting only if `wider` is allowed too.
theorem endedWider ∀ (state: HangState) (flag wider: Bool) (place: Place)
    (ended: Ended state flag place)
    (more: flag = True → wider = True):
    Ended state wider place :=
  match place, ended with
    | Mid at carry, ended => ended
    | Held at carry, (waits, floor, left) => (more waits, floor, left)
    | AtStart _ _ | Broken _ _, never => (Bool.falseNotTrue never).impossible

--| A closer written where its contents ended or after the line break before it: its bracket's block is gone.
theorem closingHangs ∀ (kinds: Text → Tok) (text: Text) (indent: Nat) (before: Bool) (state: HangState)
    (block: Option Nat) (outer: List (Option Nat))
    (closer: (kinds text).isCloser = True)
    (closes: closesText text = True)
    (token: text.startsWith "--" = False)
    (solid: isLayout text = False)
    (open: state.blocks = [block, ..outer])
    (unglued: state.glue = False)
    (nested: (inForce outer state.top <= inForce state.blocks state.top) = True)
    (clear: (inForce outer state.top <= indent) = True):
    HangLays kinds
      (Closing text)
      indent
      (place hang => hang = At state ∧ CloserSeat indent before False state place)
      (place hang => Ended (closedFrom state outer) before place ∧ hang = At (closedFrom state outer)) :=
  let closed := closedFrom state outer
  hangsClosing kinds text indent
    (place hang => hang = At state ∧ CloserSeat indent before False state place)
    (place hang => Ended closed before place ∧ hang = At closed)
    solid
    closes
    (place trace (folded, seat) =>
      rewrite folded then
        match place, seat with
          | Mid at carry, (floor, left) => (
            (floorAfterToken text carry token, arithmetic),
            stepCloser outer None (tokenCode text None token solid) closer open byComputing
          )
          | Held at carry, (waits, floor, left) => (
            (waits, floorAfterToken text carry token, arithmetic),
            stepCloser outer None (tokenCode text None token solid) closer open byComputing
          )
          | Broken at carry, Inl never => (Bool.falseNotTrue never).impossible
          | Broken at carry, Inr (atIndent, floor, inner) =>
            let shallow: leftOf indent block = True := rewrite open at inner then inner
            rewrite atIndent then
              (
                (floorAfterToken text carry token, clear),
                stepCloser outer (Some indent) (tokenCode text (Some indent) token solid) closer open (unglued, shallow)
              )
          | AtStart at carry, never => (Bool.falseNotTrue never).impossible)

--| A closer at the start of its own line, where the fold allows it: its bracket's block is gone.
theorem closingAtHangs ∀ (kinds: Text → Tok) (text: Text) (indent column: Nat) (state: HangState)
    (block: Option Nat) (outer: List (Option Nat))
    (closer: (kinds text).isCloser = True)
    (closes: closesText text = True)
    (token: text.startsWith "--" = False)
    (solid: isLayout text = False)
    (open: state.blocks = [block, ..outer])
    (unglued: state.glue = False)
    (left: leftOf column block = True)
    (right: (inForce outer state.top <= column) = True):
    HangLays kinds (Closing text) indent (LandsAt column (At state)) (place hang =>
      Ended (closedFrom state outer) False place ∧ hang = At (closedFrom state outer)) :=
  let closed := closedFrom state outer
  hangsClosing kinds text indent
    (LandsAt column (At state))
    (place hang => Ended closed False place ∧ hang = At closed)
    solid
    closes
    (place trace landed =>
      match place, landed with
        | Broken at carry, (folded, atColumn, floor) =>
          rewrite folded, atColumn then
            (
              (floorAfterToken text carry token, right),
              stepCloser outer (Some column) (tokenCode text (Some column) token solid) closer open (unglued, left)
            )
        | AtStart _ _ | Mid _ _, never => (Bool.falseNotTrue never).impossible
        | Held at carry, never => (Bool.falseNotTrue never).impossible)

--| A closer's line of its own, after words or the line break before it: where the open marks put it.
theorem closerLineHangs ∀ (kinds: Text → Tok) (key indent: Nat) (before: Bool) (state: HangState) (entry: Place):
    HangLays kinds
      (CloserLine key)
      indent
      (place hang => place = entry ∧ hang = At state ∧ CloserSeat indent before True state entry)
      (LandsAt (entry.carry.closerAt key indent) (At state)) :=
  hangsCloserLine kinds key indent
    (place hang => place = entry ∧ hang = At state ∧ CloserSeat indent before True state entry)
    (LandsAt (entry.carry.closerAt key indent) (At state))
    (place hang (isEntry, folded, seat) =>
      rewrite isEntry then
        match entry, seat with
          | Mid _ _ | Held _ _, _ => (folded, byComputing, byComputing)
          | Broken at carry, _ => (folded, byComputing, byComputing))

--| A closer with own-line comments: the comments at 2 deeper, each on its line, then the closer's line of its own,
--| where the open marks put it at the closer's seat (the comments' lines are deeper than the construct, so they don't
--| move it).
--|
--| Proof idea: `LineStartHere` starts the first comment's line at 2 deeper, lowering the marks to it at most;
--| `closerAtLower` keeps where the closer lands through that and each later line; `CloserLine` then breaks there.
theorem closerLeadingHangs ∀ (kinds: Text → Tok) (word: Word) (around: Around) (key indent: Nat) (state: HangState)
    (entry: Place) (note: Note) (rest: List Note)
    (hoisted: around.hoisted = False)
    (noted: word.comments.above = [note, ..rest])
    (closer: isCloserText word.text = True)
    (comments: NotesComment [note, ..rest]):
    HangLaysAll kinds
      (word.leading around key)
      indent
      (place hang => place = entry ∧ hang = At state ∧ CloserSeat indent around.before False state entry)
      (LandsAt (entry.carry.closerAt key indent) (At state)) :=
  let column := entry.carry.closerAt key indent
  let hang := At state
  let pre: Place → Hang → Prop := place now =>
    place = entry ∧ now = hang ∧ CloserSeat indent around.before False state entry
  let (comment, solid, others) := comments
  let text := noteTextHangs kinds note.text indent key column hang comment solid
  let more := laterCloserNotesHang kinds rest indent key column hang others
  let notes: HangLaysAll kinds
    (closerNotes [note, ..rest])
    (indent + 2)
    (NoteBroken indent key column hang)
    (NoteWritten indent key column hang) :=
    match blank: note.blankBefore with
      | True =>
        hangsCons
          ([Doc.text note.text] ++ laterCloserNotes rest)
          (noteBlankHangs kinds indent key column hang)
          (hangsCons (laterCloserNotes rest) text more)
      | False => hangsCons (laterCloserNotes rest) (hangsPre text (noteBrokenStart indent key column hang)) more
  let here: HangLays kinds LineStartHere (indent + 2) pre (NoteBroken indent key column hang) :=
    hangsStartHere kinds (indent + 2) pre (NoteBroken indent key column hang) (place trace (isEntry, folded, seat) =>
      rewrite isEntry then
        match entry, seat with
          | Mid at carry, (floor, _) =>
            let landed: floored carry (indent + 2) = indent + 2 := rewrite floor
            (folded, landed, floor, breakKeepsCloser carry key indent floor)
          | Held at carry, (_, floor, _) =>
            let landed: floored carry (indent + 2) = indent + 2 := rewrite floor
            (folded, landed, floor, breakKeepsCloser carry key indent floor)
          | Broken at carry, Inl never => (Bool.falseNotTrue never).impossible
          | Broken at carry, Inr (_, floor, _) => (folded, byComputing, floor, byComputing))
  let inner: HangLays kinds
    (Doc.concat [LineStartHere, ..closerNotes [note, ..rest]])
    (indent + 2)
    pre
    (NoteWritten indent key column hang) :=
    hangsConcat (hangsCons (closerNotes [note, ..rest]) here notes)
  let line: HangLays kinds (CloserLine key) indent (NoteWritten indent key column hang) (LandsAt column hang) :=
    hangsCloserLine kinds key indent (NoteWritten indent key column hang) (LandsAt column hang) (place now written =>
      match place, written with
        | Mid at carry, (same, _, _, lands) => (same, lands, byComputing)
        | AtStart _ _ | Broken _ _, never => (Bool.falseNotTrue never).impossible
        | Held at carry, never => (Bool.falseNotTrue never).impossible)
  rewrite hoisted, noted, closer then
    hangsCons
      [Nest 2 (Doc.concat [LineStartHere, ..closerNotes [note, ..rest]]), CloserLine key]
      (hangsBreakParent kinds indent pre)
      (hangsTwo (hangsNest inner) line)

--| A proof by cases on a list of own-line comments that leaves the goal as it is written.
theorem notesCases ∀ (goal: Prop) (notes: List Note)
    (none: notes = [] → goal) (some: ∀ (note: Note) (rest: List Note) => notes = [note, ..rest] → goal):
    goal :=
  match notes with
    | [] => none byComputing
    | [note, ..rest] => some note rest byComputing

--| A closer on its own: its own-line comments and its line of its own if any, the closer, its trailing comment.
theorem closerLeafIs ∀ (word: Word) (around: Around) (key: Nat)
    (closer: isCloserText word.text = True):
    word.leaf around key
      = Doc.concat
        (word.leading around key
          ++ (if word.lone around then [CloserLine key] else [])
          ++ [Closing word.text]
          ++ word.trailing) :=
  rewrite closer

--| `closerLeafIs`' hypothesis holds of a closer.
theorem closerLeafIsExample ∀ (comments: Comments) (around: Around) (key: Nat):
    { text = ")", comments }.leaf around key
      = Doc.concat
        ({ text = ")", comments }.leading around key
          ++ (if { text = ")", comments }.lone around then [CloserLine key] else [])
          ++ [Closing ")"]
          ++ { text = ")", comments }.trailing) :=
  closerLeafIs { text = ")", comments } around key byComputing

theorem noTrailing ∀ (word: Word) (quiet: word.trails = False): word.trailing = [] :=
  match after: word.comments.after, quiet with
    | None, _ => byComputing
    | Some comment, never => (Bool.trueNotFalse never).impossible

--| A closer's trailing comment, if it has one, where no comment waits: after a waiting comment it has none.
theorem trailingAfterClose ∀ (kinds: Text → Tok) (word: Word) (indent: Nat) (state: HangState) (before: Bool)
    (trailed: TrailsComment word)
    (quiet: (before && word.trails) = False):
    HangLaysAll kinds word.trailing indent (place hang => Ended state before place ∧ hang = At state) (place hang =>
      Ended state (word.trails || before) place ∧ hang = At state) :=
  match isBefore: before, quiet with
    | False, _ => allHangsPost (trailingHangs kinds indent state trailed) (place hang (ended, folded) =>
      (endedWider state word.trails (word.trails || False) place ended (trails => rewrite trails), folded))
    | True, quiet =>
      rewrite noTrailing word quiet, quiet then
        hangsNil kinds indent
          (place hang => Ended state True place ∧ hang = At state)
          (place hang => Ended state True place ∧ hang = At state)
          (place hang held => held)

--| The fold facts a bracket's closer needs: its block innermost, nothing glued, and what is in force outside the
--| bracket not right of the block nor of the construct's indentation.
def CloserFold (indent: Nat) (state: HangState) (block: Option Nat) (outer: List (Option Nat)): Prop :=
  state.blocks = [block, ..outer]
    ∧ state.glue = False
    ∧ (inForce outer state.top <= inForce state.blocks state.top) = True
    ∧ (inForce outer state.top <= indent) = True

--| The closer's token: a closer the lexer reads as one, not a comment or layout.
def CloserToken (kinds: Text → Tok) (text: Text): Prop :=
  (kinds text).isCloser = True
    ∧ closesText text = True
    ∧ isCloserText text = True
    ∧ text.startsWith "--" = False
    ∧ isLayout text = False

--| Where a closer may start, and where its line of its own, if it takes one, may land.
def CloserEntry (kinds: Text → Tok) (word: Word) (around: Around) (key indent: Nat) (state: HangState)
    (block: Option Nat) (outer: List (Option Nat)):
    Place → Hang → Prop :=
  place hang =>
    hang = At state
      ∧ CloserSeat indent around.before (word.lone around) state place
      ∧ ((word.noted || word.lone around) = True → CloserFits key indent block (inForce outer state.top) place.carry)

--| After a closer: the bracket's block gone, a comment waiting only if the closer or the code before it trails one.
def CloserExit (word: Word) (around: Around) (state: HangState) (outer: List (Option Nat)): Place → Hang → Prop :=
  place hang => Ended (closedFrom state outer) (word.trails || around.before) place ∧ hang = At (closedFrom state outer)

--| A closer at the start of its own line, then its trailing comment.
theorem closerAtLineHangs ∀ (kinds: Text → Tok) (word: Word) (around: Around) (indent column: Nat) (state: HangState)
    (block: Option Nat) (outer: List (Option Nat))
    (token: CloserToken kinds word.text)
    (fold: CloserFold indent state block outer)
    (trailed: TrailsComment word)
    (left: leftOf column block = True)
    (right: (inForce outer state.top <= column) = True):
    HangLaysAll kinds
      [Closing word.text, ..word.trailing]
      indent
      (LandsAt column (At state))
      (CloserExit word around state outer) :=
  let closed := closedFrom state outer
  let (closer, closes, _, notComment, solid) := token
  let (open, unglued, _, _) := fold
  hangsCons word.trailing
    (closingAtHangs kinds word.text indent column state block outer closer closes notComment solid open unglued left
        right)
    (allHangsPost (trailingHangs kinds indent closed trailed) (place hang (ended, folded) =>
      (endedWider closed word.trails (word.trails || around.before) place ended (trails => rewrite trails), folded)))

--| A closer with own-line comments.
theorem notedCloserHangs ∀ (kinds: Text → Tok) (word: Word) (around: Around) (key indent: Nat) (state: HangState)
    (block: Option Nat) (outer: List (Option Nat)) (note: Note) (rest: List Note)
    (token: CloserToken kinds word.text)
    (fold: CloserFold indent state block outer)
    (hoisted: around.hoisted = False)
    (noted: word.comments.above = [note, ..rest])
    (comments: NotesComment [note, ..rest])
    (trailed: TrailsComment word):
    HangLays kinds
      (word.leaf around key)
      indent
      (CloserEntry kinds word around key indent state block outer)
      (CloserExit word around state outer) :=
  hangsBy (place trace next (folded, seat, fits) after =>
    let (_, _, text, _, _) := token
    let lone: word.lone around = False := rewrite noted
    let (left, right) := fits (rewrite noted)
    let unlone: CloserSeat indent around.before False state place := rewrite lone at seat then seat
    let column := place.carry.closerAt key indent
    let pre: Place → Hang → Prop := entry hang =>
      entry = place ∧ hang = At state ∧ CloserSeat indent around.before False state place
    rewrite closerLeafIs word around key text, lone then
      laysBy
        (hangsConcat
          (hangsAppend
            (closerLeadingHangs kinds word around key indent state place note rest hoisted noted text comments)
            (closerAtLineHangs kinds word around indent column state block outer token fold trailed left right)))
        place
        trace
        next
        (byComputing, folded, unlone)
        after)

theorem bareCloserLeading ∀ (word: Word) (around: Around) (key: Nat)
    (hoisted: around.hoisted = False)
    (bare: word.comments.above = [])
    (single: around.item = False):
    word.leading around key = [] :=
  rewrite hoisted, bare, single

--| A closer with no own-line comments on a line of its own, after code that ends its line with a comment.
theorem loneCloserHangs ∀ (kinds: Text → Tok) (word: Word) (around: Around) (key indent: Nat) (state: HangState)
    (block: Option Nat) (outer: List (Option Nat))
    (token: CloserToken kinds word.text)
    (fold: CloserFold indent state block outer)
    (hoisted: around.hoisted = False)
    (bare: word.comments.above = [])
    (single: around.item = False)
    (lone: word.lone around = True)
    (trailed: TrailsComment word):
    HangLays kinds
      (word.leaf around key)
      indent
      (CloserEntry kinds word around key indent state block outer)
      (CloserExit word around state outer) :=
  hangsBy (place trace next (folded, seat, fits) after =>
    let (_, _, text, _, _) := token
    let alone: CloserSeat indent around.before True state place := rewrite lone at seat then seat
    let (left, right) := fits ((Bool.orReads _ _).backward (Inr lone))
    let column := place.carry.closerAt key indent
    let pre: Place → Hang → Prop := entry hang =>
      entry = place ∧ hang = At state ∧ CloserSeat indent around.before True state place
    rewrite closerLeafIs word around key text, bareCloserLeading word around key hoisted bare single, lone then
      laysBy
        (hangsConcat
          (hangsCons
            [Closing word.text, ..word.trailing]
            (closerLineHangs kinds key indent around.before state place)
            (closerAtLineHangs kinds word around indent column state block outer token fold trailed left right)))
        place
        trace
        next
        (byComputing, folded, alone)
        after)

--| A closer with no own-line comments and no line of its own: where its contents ended, or after the line break
--| before it.
theorem plainCloserHangs ∀ (kinds: Text → Tok) (word: Word) (around: Around) (key indent: Nat) (state: HangState)
    (block: Option Nat) (outer: List (Option Nat))
    (token: CloserToken kinds word.text)
    (fold: CloserFold indent state block outer)
    (hoisted: around.hoisted = False)
    (bare: word.comments.above = [])
    (single: around.item = False)
    (lone: word.lone around = False)
    (trailed: TrailsComment word):
    HangLays kinds
      (word.leaf around key)
      indent
      (CloserEntry kinds word around key indent state block outer)
      (CloserExit word around state outer) :=
  let (closer, closes, text, notComment, solid) := token
  let (open, unglued, nested, clear) := fold
  let closed := closedFrom state outer
  let quiet: (around.before && word.trails) = False := rewrite bare at lone then lone
  let pre := CloserEntry kinds word around key indent state block outer
  let ended: Place → Hang → Prop := place hang => Ended closed around.before place ∧ hang = At closed
  hangsBy (place trace next holds after =>
    rewrite closerLeafIs word around key text, bareCloserLeading word around key hoisted bare single, lone then
      laysBy
        (hangsConcat
          (hangsCons word.trailing
            (hangsPre
              [weaker := pre]
              (closingHangs kinds word.text indent around.before state block outer closer closes notComment solid open
                  unglued nested clear)
              (place hang (folded, seat, _) => (folded, rewrite lone at seat then seat)))
            (trailingAfterClose kinds word indent closed around.before trailed quiet)))
        place
        trace
        next
        holds
        after)

--| A bracket's closer on its own (`Word.leaf`), from where its contents ended or the line break before it: what
--| is written before it on lines of their own leaves the fold as it was, and the closer closes its bracket.
--|
--| Proof idea: by cases on the closer's own-line comments and on whether it takes a line of its own after a waiting
--| comment (`Word.lone`); `notedCloserHangs`, `loneCloserHangs` and `plainCloserHangs` each lay one case.
theorem closerLeafHangs ∀ (kinds: Text → Tok) (word: Word) (around: Around) (key indent: Nat) (state: HangState)
    (block: Option Nat) (outer: List (Option Nat))
    (token: CloserToken kinds word.text)
    (fold: CloserFold indent state block outer)
    (hoisted: around.hoisted = False)
    (single: around.item = False)
    (comments: NotesComment word.comments.above)
    (trailed: TrailsComment word):
    HangLays kinds
      (word.leaf around key)
      indent
      (CloserEntry kinds word around key indent state block outer)
      (CloserExit word around state outer) :=
  let goal: Prop :=
    HangLays kinds
      (word.leaf around key)
      indent
      (CloserEntry kinds word around key indent state block outer)
      (CloserExit word around state outer)
  notesCases goal word.comments.above
    (bare =>
      Bool.inspect
        (word.lone around)
        (_ => goal)
        (lone =>
          loneCloserHangs kinds word around key indent state block outer token fold hoisted bare single lone trailed)
        (lone =>
          plainCloserHangs kinds word around key indent state block outer token fold hoisted bare single lone trailed))
    (note rest noted =>
      notedCloserHangs kinds word around key indent state block outer note rest token fold hoisted noted
        (rewrite noted at comments then comments)
        trailed)

-- Openers.

--| An opening bracket's token: an opener the lexer reads as one, not a comment or layout.
def OpenerToken (kinds: Text → Tok) (text: Text): Prop :=
  (kinds text).isOpener = True
    ∧ (kinds text).isCloser = False
    ∧ (kinds text == Comma) = False
    ∧ (kinds text == ColonEq) = False
    ∧ (kinds text == Colon) = False
    ∧ (kinds text == Arrow) = False
    ∧ text.startsWith "--" = False
    ∧ isLayout text = False
    ∧ isCloserText text = False
    ∧ (text == ",") = False

--| A `Mark` leaves a seat a seat, the first word starting where it would.
theorem markSeated ∀ (indent column key: Nat) (before: Bool) (state: HangState) (place: Place)
    (seated: Seated column before state place):
    Seated column before state (place.withCarry (place.carry.mark key place.indent))
      ∧ wordStart indent (place.withCarry (place.carry.mark key place.indent)) = wordStart indent place :=
  match place, seated with | AtStart _ _ | Broken _ _ | Mid _ _ | Held _ _, seated => (seated, byComputing)

--| An opener leaves in force what a plain token there would: its own block has no column yet.
theorem openingEnded ∀ (state: HangState) (start: Option Nat) (flag: Bool) (place: Place)
    (ended: Ended (openedBy state start) flag place):
    Ended (openingBy state start) flag place :=
  match place, ended with
    | Mid _ _ | Held _ _, ended => ended
    | AtStart _ _ | Broken _ _, never => (Bool.falseNotTrue never).impossible

--| An opener's text, at a seat whose first word starts at `start`: one opener there.
theorem openerStep ∀ (kinds: Text → Tok) (text: Text) (indent column: Nat) (state: HangState) (start: Option Nat)
    (token: OpenerToken kinds text):
    HangLays kinds
      (Doc.text text)
      indent
      (place hang =>
        hang = At state
          ∧ Seated column False state place
          ∧ Room state (wordStart indent place)
          ∧ wordStart indent place = start)
      (place hang => Ended (openingBy state start) False place ∧ hang = At (openingBy state start)) :=
  let (opener, closer, comma, assign, colon, arrow, notComment, solid, _, _) := token
  hangsChunk kinds text text.length indent
    (place hang =>
      hang = At state
        ∧ Seated column False state place
        ∧ Room state (wordStart indent place)
        ∧ wordStart indent place = start)
    (place hang => Ended (openingBy state start) False place ∧ hang = At (openingBy state start))
    solid
    (place trace (folded, seated, room, same) =>
      let ended := wordEnded notComment seated room
      let stepped :=
        stepOpener kinds state text
          (wordStart indent place)
          (tokenCode text (wordStart indent place) notComment solid)
          opener
          closer
          comma
          assign
          colon
          arrow
          room
      rewrite folded then (openingEnded state start False _ (rewrite same at ended then ended), rewrite stepped, same))

--| An opening bracket, its own-line comments written by its node: its mark if its closer may take a line of its own,
--| the bracket, its trailing comment; it opens a block of its own.
theorem openingHangs ∀ [kinds: Text → Tok] [word: Word] (closer: Word) [around: Around] (indent column: Nat)
    (state: HangState) (entry: Place)
    (token: OpenerToken kinds word.text)
    (hoisted: around.hoisted = True)
    (trailed: TrailsComment word):
    HangLays kinds
      (word.opening around closer)
      indent
      (Entered indent column False state entry (wordStart indent entry))
      (place hang =>
        Ended (openingBy state (wordStart indent entry)) word.trails place
          ∧ hang = At (openingBy state (wordStart indent entry))) :=
  let (_, _, _, _, _, _, _, _, notCloser, notComma) := token
  let start := wordStart indent entry
  let opened := openingBy state start
  let ready: Place → Hang → Prop := place hang =>
    hang = At state
      ∧ Seated column False state place
      ∧ Room state (wordStart indent place)
      ∧ wordStart indent place = start
  let written: Place → Hang → Prop := place hang => Ended opened False place ∧ hang = At opened
  let post: Place → Hang → Prop := place hang => Ended opened word.trails place ∧ hang = At opened
  let rest: HangLaysAll kinds [Doc.text word.text, ..word.trailing] indent ready post :=
    hangsCons word.trailing
      (openerStep kinds word.text indent column state start token)
      (trailingHangs kinds indent opened trailed)
  rewrite hoisted, notCloser, notComma then
    match marks: closer.noted || closer.trails with
      | True =>
        hangsConcat
          (hangsCons
            [Doc.text word.text, ..word.trailing]
            (hangsMark kinds around.at indent (Entered indent column False state entry start) ready (place hang (
              isEntry,
              folded,
              (seated, _, _, room)
            ) =>
              let (stays, same) := markSeated indent column around.at False state place (rewrite isEntry then seated)
              (folded, stays, rewrite same, isEntry then room, rewrite same, isEntry)))
            rest)
      | False =>
        hangsConcat
          (allHangsPre rest (place hang (isEntry, folded, (seated, _, _, room)) =>
            (folded, rewrite isEntry then seated, rewrite isEntry then room, rewrite isEntry)))
