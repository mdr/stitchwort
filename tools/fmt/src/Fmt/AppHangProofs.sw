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
