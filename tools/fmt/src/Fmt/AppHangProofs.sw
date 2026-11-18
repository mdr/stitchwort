--| Slice 1's `hangs` clause for calls (SW-4030): a call's elements on its line, spaced, keep the fold as after
--| its function's first word.
namespace Fmt.AppHangProofs
import Std (Bool, Doc, Eq, List, Nat, Option, Text, Void)
import Std.Doc (..)
import Std.Doc.Proofs (..)
import Syntax (Expr, Tok, Word)
import Fmt (..)
import Fmt.HangProofs (..)

--| Elements after the first, each after a space: each starts where the one before ended, a comment waiting only if
--| that one's code ends with one (`before`), and the last ends with a comment waiting only if `trails`.
def SpacedParts (kinds: Text → Tok) (indent: Nat) (before trails: Bool): List Doc → Prop
  | [] => before = trails
  | [doc, ..rest] =>
    ∃ (middle: Bool) => PartHangs kinds doc indent before middle ∧ SpacedParts kinds indent middle trails rest

--| Where an element ended after words: the fold as after them, nothing in force right of the indentation.
def AfterWords (state: HangState) (indent: Nat) (trails: Bool): Place → Hang → Prop := place hang =>
  Ended state trails place ∧ hang = Hang.At state ∧ (inForce state.blocks state.top <= indent) = True

theorem partStep ∀ (kinds: Text → Tok) (doc: Doc) (indent: Nat) (state: HangState) (before trails: Bool)
    (quiet: state.start = False)
    (unglued: state.glue = False)
    (part: PartHangs kinds doc indent before trails):
    HangLays kinds doc indent (AfterWords state indent before) (AfterWords state indent trails) :=
  place trace next (ended, folded, clear) after =>
    part state place quiet unglued place trace next (byComputing, folded, ended, clear) (left later (done, landed) =>
      after left later (done, landed, clear))

--| Spaced elements after the first.
--|
--| Proof idea: by the list; each space keeps where the element before ended (`gapKeeps`), and each element starts
--| there and ends with the fold as it was (`partStep`).
theorem spacedRest ∀ (kinds: Text → Tok) (docs: List Doc) (indent: Nat) (state: HangState) (before trails: Bool)
    (quiet: state.start = False)
    (unglued: state.glue = False)
    (parts: SpacedParts kinds indent before trails docs):
    HangLaysAll kinds
      (docs.concatMap (doc => [Doc.text " ", doc]))
      indent
      (AfterWords state indent before)
      (AfterWords state indent trails) :=
  match docs, parts with
    | [], same =>
      rewrite same then
        hangsNil kinds indent (AfterWords state indent trails) (AfterWords state indent trails) (place hang holds =>
          holds)
    | [doc, ..rest], (middle, part, more) =>
      hangsCons kinds
        (Doc.text " ")
        [doc, ..rest.concatMap (doc => [Doc.text " ", doc])]
        indent
        (AfterWords state indent before)
        (AfterWords state indent before)
        (AfterWords state indent trails)
        (place trace next (ended, folded, clear) after =>
          gapKeeps kinds
            (Doc.text " ")
            indent
            state
            before
            ((inForce state.blocks state.top <= indent) = True)
            (Inr byComputing)
            place
            trace
            next
            (ended, folded, clear)
            after)
        (hangsCons kinds doc
          (rest.concatMap (doc => [Doc.text " ", doc]))
          indent
          (AfterWords state indent before)
          (AfterWords state indent middle)
          (AfterWords state indent trails)
          (partStep kinds doc indent state before middle quiet unglued part)
          (spacedRest kinds rest indent state middle trails quiet unglued more))

--| Docs joined by a separator: the first, then the separator before each other.
theorem joinedWithIs ∀ (separator first: Doc) (rest: List Doc):
    Doc.joinedWith separator [first, ..rest] = [first, ..rest.concatMap (doc => [separator, doc])] :=
  match rest with
    | [] => byComputing
    | [second, ..more] => rewrite joinedWithIs separator second more

--| Elements spaced on one line (`spaced`) as one element: the fold after them as after the first one's first word.
--|
--| Proof idea: the first element leaves the fold as after its first word, which starts nothing and glues nothing,
--| with nothing in force right of the indentation (`openedBound`); the rest keep it (`spacedRest`).
theorem spacedHangs ∀ (kinds: Text → Tok) (first: Doc) (rest: List Doc) (indent column: Nat) (middle trails: Bool)
    (head: ElHangs kinds first indent column False middle wordStart)
    (parts: SpacedParts kinds indent middle trails rest):
    ElHangs kinds (spaced [first, ..rest]) indent column False trails wordStart :=
  state entry place trace next entered after =>
    let (_, _, (seated, below, clear, room)) := entered
    let opened := openedBy state (wordStart indent entry)
    let bound: (inForce opened.blocks opened.top <= indent) = True :=
      openedBound indent column state entry seated below clear room
    let pre := Entered indent column False state entry (wordStart indent entry)
    rewrite joinedWithIs (Doc.text " ") first rest then
      hangsConcat kinds
        [first, ..rest.concatMap (doc => [Doc.text " ", doc])]
        indent
        pre
        (AfterWords opened indent trails)
        (hangsCons kinds first
          (rest.concatMap (doc => [Doc.text " ", doc]))
          indent
          pre
          (AfterWords opened indent middle)
          (AfterWords opened indent trails)
          (hangsPost kinds first indent pre
            (place hang => Ended opened middle place ∧ hang = Hang.At opened)
            (AfterWords opened indent middle)
            (head state entry)
            (place hang (ended, folded) => (ended, folded, bound)))
          (spacedRest kinds rest indent opened middle trails
            (openedQuietStart state (wordStart indent entry))
            (openedUnglued state (wordStart indent entry))
            parts))
        place
        trace
        next
        entered
        (left later (ended, folded, _) => after left later (ended, folded))

-- A call's arguments, each an element laid at `inset`, the fold as after the call's first word.

--| Where an argument laid at `inset` starts: a seat there, after a waiting comment only if `before`.
def ArgSeat (state: HangState) (inset: Nat) (before: Bool): Place → Hang → Prop := place hang =>
  hang = Hang.At state ∧ Seat inset inset before state place (wordStart inset place)

--| An argument, from its seat: the fold after it as before it, which starts nothing and glues nothing.
theorem argHangs ∀ (kinds: Text → Tok) (doc: Doc) (inset indent: Nat) (state: HangState) (before trails: Bool)
    (quiet: state.start = False)
    (unglued: state.glue = False)
    (clear: (inForce state.blocks state.top <= indent) = True)
    (el: ElHangs kinds doc inset inset before trails wordStart):
    HangLays kinds doc inset (ArgSeat state inset before) (AfterWords state indent trails) :=
  place trace next (folded, seat) after =>
    let same := openedQuiet state (wordStart inset place) quiet unglued
    el state place place trace next (byComputing, folded, seat) (left later (ended, landed) =>
      after left later (rewrite same at ended then ended, rewrite same at landed then landed, clear))

theorem brokenArgSeat ∀ (inset: Nat) (state: HangState) (before: Bool) (carry: Carry)
    (unglued: state.glue = False)
    (floor: carry.floor = None)
    (bound: (inForce state.blocks state.top < inset) = True):
    ArgSeat state inset before (Broken (floored carry inset) (carry.breakTo inset)) (Hang.At state) :=
  let landed: floored carry inset = inset := rewrite floor
  rewrite landed then (byComputing, ((byComputing, byComputing), Nat.leRefl inset, arithmetic, (unglued, arithmetic)))

theorem startArgSeat ∀ (inset: Nat) (state: HangState) (before: Bool) (carry: Carry)
    (unglued: state.glue = False)
    (floor: carry.floor = None)
    (bound: (inForce state.blocks state.top < inset) = True):
    ArgSeat state inset before (AtStart (floored carry inset) (carry.breakTo inset)) (Hang.At state) :=
  let landed: floored carry inset = inset := rewrite floor
  rewrite landed then (byComputing, ((byComputing, byComputing), Nat.leRefl inset, arithmetic, (unglued, arithmetic)))

theorem midArgSeat ∀ (inset at: Nat) (state: HangState) (before: Bool) (carry: Carry)
    (floor: carry.floor = None)
    (left: (inForce state.blocks state.top <= at) = True)
    (bound: (inForce state.blocks state.top < inset) = True):
    ArgSeat state inset before (Mid at carry) (Hang.At state) :=
  (byComputing, ((floor, left), Nat.leRefl inset, arithmetic, byComputing))

theorem heldArgSeat ∀ (inset at: Nat) (state: HangState) (carry: Carry)
    (unglued: state.glue = False)
    (floor: carry.floor = None)
    (left: (inForce state.blocks state.top <= at) = True)
    (bound: (inForce state.blocks state.top < inset) = True):
    ArgSeat state inset True (Held at carry) (Hang.At state) :=
  let landed: floored carry (Nat.max inset (at + 2)) = Nat.max inset (at + 2) := rewrite floor
  (byComputing, ((byComputing, floor, left), Nat.leRefl inset, arithmetic, (unglued, rewrite landed then arithmetic)))

--| A `Line` before an argument laid deeper than the call: a space, or a line break at `inset`.
theorem lineArg ∀ (kinds: Text → Tok) (inset indent: Nat) (state: HangState) (before: Bool)
    (unglued: state.glue = False)
    (deeper: (indent < inset) = True):
    HangLays kinds Line inset (AfterWords state indent before) (ArgSeat state inset before) :=
  hangsLine kinds inset (AfterWords state indent before) (ArgSeat state inset before) (place trace (ended, folded,
    clear) =>
    let bound: (inForce state.blocks state.top < inset) = True := arithmetic
    match place, ended with
      | Mid at carry, (floor, left) =>
        rewrite folded then
          (
            midArgSeat inset at state before { carry | floor = None } byComputing left bound,
            brokenArgSeat inset state before carry unglued floor bound
          )
      | Held at carry, (waits, floor, left) =>
        rewrite folded then
          (
            rewrite waits then heldArgSeat inset at state carry unglued floor left bound,
            brokenArgSeat inset state before carry unglued floor bound
          ))

--| A `HardLine` before an argument laid deeper than the call: the start of a line at `inset`.
theorem hardArg ∀ (kinds: Text → Tok) (inset indent: Nat) (state: HangState) (before: Bool)
    (unglued: state.glue = False)
    (deeper: (indent < inset) = True):
    HangLays kinds HardLine inset (AfterWords state indent before) (ArgSeat state inset False) :=
  hangsHard kinds inset (AfterWords state indent before) (ArgSeat state inset False) (place hang (ended, folded,
    clear) =>
    let bound: (inForce state.blocks state.top < inset) = True := arithmetic
    match place, ended with
      | Mid at carry, (floor, _) =>
        (byComputing, rewrite folded then startArgSeat inset state False carry unglued floor bound)
      | Held at carry, (_, floor, _) =>
        (byComputing, rewrite folded then startArgSeat inset state False carry unglued floor bound))

--| Arguments each on a line of its own, laid at `inset`.
def LinedArgs (kinds: Text → Tok) (inset: Nat) (before trails: Bool): List Doc → Prop
  | [] => before = trails
  | [doc, ..rest] =>
    ∃ (middle: Bool) => ElHangs kinds doc inset inset False middle wordStart ∧ LinedArgs kinds inset middle trails rest

--| Arguments each on a line of its own (a broken call's `rest`), laid deeper than the call: the fold kept.
theorem linedRest ∀ (kinds: Text → Tok) (docs: List Doc) (inset indent: Nat) (state: HangState) (before trails: Bool)
    (quiet: state.start = False)
    (unglued: state.glue = False)
    (clear: (inForce state.blocks state.top <= indent) = True)
    (deeper: (indent < inset) = True)
    (args: LinedArgs kinds inset before trails docs):
    HangLaysAll kinds
      (docs.concatMap (doc => [HardLine, doc]))
      inset
      (AfterWords state indent before)
      (AfterWords state indent trails) :=
  match docs, args with
    | [], same =>
      rewrite same then
        hangsNil kinds inset (AfterWords state indent trails) (AfterWords state indent trails) (place hang holds =>
          holds)
    | [doc, ..rest], (middle, el, more) =>
      hangsCons kinds HardLine
        [doc, ..rest.concatMap (doc => [HardLine, doc])]
        inset
        (AfterWords state indent before)
        (ArgSeat state inset False)
        (AfterWords state indent trails)
        (hardArg kinds inset indent state before unglued deeper)
        (hangsCons kinds doc
          (rest.concatMap (doc => [HardLine, doc]))
          inset
          (ArgSeat state inset False)
          (AfterWords state indent middle)
          (AfterWords state indent trails)
          (argHangs kinds doc inset indent state False middle quiet unglued clear el)
          (linedRest kinds rest inset indent state middle trails quiet unglued clear deeper more))

--| Arguments filling lines, laid at `inset`: each after a separator, after a waiting comment only if the one before
--| ended with one.
def FilledArgs (kinds: Text → Tok) (inset: Nat) (before trails: Bool): List Doc → Prop
  | [] => before = trails
  | [doc, ..rest] =>
    ∃ (middle: Bool) => ElHangs kinds doc inset inset before middle wordStart
      ∧ FilledArgs kinds inset middle trails rest

theorem sepsArgs ∀ (kinds: Text → Tok) (docs: List Doc) (inset indent: Nat) (state: HangState) (before trails: Bool)
    (quiet: state.start = False)
    (unglued: state.glue = False)
    (clear: (inForce state.blocks state.top <= indent) = True)
    (deeper: (indent < inset) = True)
    (args: FilledArgs kinds inset before trails docs)
    (place: Place) (trace: List Event) (next: Place → List Event → Prop)
    (holds: AfterWords state indent before place (hangOf kinds trace))
    (after: ∀ (left: Place) (later: List Event) => AfterWords state indent trails left (hangOf kinds later)
      → next left later):
    SepsLay docs inset place trace next :=
  match docs, args with
    | [], same => after place trace (rewrite same at holds then holds)
    | [doc, ..rest], (middle, el, more) =>
      lineArg kinds inset indent state before unglued deeper place trace
        (seat between => Lays doc inset seat between (left later => SepsLay rest inset left later next))
        holds
        (seat between ready =>
          argHangs kinds doc inset indent state before middle quiet unglued clear el seat between
            (left later => SepsLay rest inset left later next)
            ready
            (left later done =>
              sepsArgs kinds rest inset indent state middle trails quiet unglued clear deeper more left later next done
                  after))

--| Where an element laid at `indent` may start, one laid deeper from the same seat may: its first word starts the
--| same line, if any.
theorem enteredDeeper ∀ (indent inset column: Nat) (state: HangState) (entry place: Place) (hang: Hang)
    (deeper: (indent <= inset) = True)
    (entered: Entered indent column False state entry (wordStart indent entry) place hang):
    Entered inset column False state entry (wordStart inset entry) place hang
      ∧ wordStart inset entry = wordStart indent entry :=
  match entry, entered with
    | AtStart at carry, (isEntry, folded, (seated, below, clear, room)) =>
      ((isEntry, folded, (seated, arithmetic, arithmetic, room)), byComputing)
    | Broken at carry, (isEntry, folded, (seated, below, clear, room)) =>
      ((isEntry, folded, (seated, arithmetic, arithmetic, room)), byComputing)
    | Mid at carry, (isEntry, folded, (seated, below, clear, room)) =>
      ((isEntry, folded, (seated, arithmetic, arithmetic, room)), byComputing)
    | Held at carry, (_, _, ((never, _, _), _, _, _)) => (Bool.falseNotTrue never).impossible

--| A call's elements filling lines laid at `inset`, deeper than the call (`Nest 4 (Fill …)`): the function at the
--| call's seat, the arguments after it.
--|
--| Proof idea: the function, laid deeper from the call's seat (`enteredDeeper`), leaves the fold as after its first
--| word, which starts nothing and glues nothing, with nothing in force right of the call's indentation
--| (`openedBound`); each argument then starts after a separator and keeps it (`sepsArgs`).
theorem filledHangs ∀ (kinds: Text → Tok) (head: Doc) (args: List Doc) (more indent column: Nat) (middle trails: Bool)
    (positive: (0 < more) = True)
    (headHangs: ElHangs kinds head (indent + more) column False middle wordStart)
    (filled: FilledArgs kinds (indent + more) middle trails args):
    ElHangs kinds (Nest more (Fill [head, ..args])) indent column False trails wordStart :=
  state entry place trace next entered after =>
    let inset := indent + more
    let (_, _, (seated, below, clear, room)) := entered
    let opened := openedBy state (wordStart indent entry)
    let bound: (inForce opened.blocks opened.top <= indent) = True :=
      openedBound indent column state entry seated below clear room
    let (deep, same) := enteredDeeper indent inset column state entry place (hangOf kinds trace) arithmetic entered
    headHangs state entry place trace (left later => SepsLay args inset left later next) deep (left later (ended,
      folded) =>
      sepsArgs kinds args inset indent opened middle trails
        (openedQuietStart state (wordStart indent entry))
        (openedUnglued state (wordStart indent entry))
        bound
        arithmetic
        filled
        left
        later
        next
        (rewrite same at ended then ended, rewrite same at folded then folded, bound)
        (left later (done, landed, _) => after left later (done, landed)))

--| A broken call's arguments each on a line of its own, laid deeper than the call, as a part after its function.
theorem linedPart ∀ (kinds: Text → Tok) (docs: List Doc) (more indent: Nat) (before trails: Bool)
    (positive: (0 < more) = True)
    (args: LinedArgs kinds (indent + more) before trails docs):
    PartHangs kinds (Nest more (Doc.concat (docs.concatMap (doc => [HardLine, doc])))) indent before trails :=
  state entry quiet unglued place trace next (isEntry, folded, ended, clear) after =>
    hangsConcat kinds
      (docs.concatMap (doc => [HardLine, doc]))
      (indent + more)
      (AfterWords state indent before)
      (AfterWords state indent trails)
      (linedRest kinds docs (indent + more) indent state before trails quiet unglued clear arithmetic args)
      place
      trace
      next
      (rewrite isEntry then ended, folded, clear)
      (left later (done, landed, _) => after left later (done, landed))
