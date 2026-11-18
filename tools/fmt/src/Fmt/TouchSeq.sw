--| Documents one after another, a space or a line break between each two, in the triples of `Fmt.TouchSteps`
--| (SW-4093): fills, `spaced`, and a call's layouts (`appFrom`), each spacing the documents' code words as a list of
--| `Spacing`s per document says.

namespace Fmt.TouchSeq
import Std (Bool, Doc, Eq, List, Nat, Option, Text, Void)
import Std.Doc (..)
import Std.Doc.Proofs (Seam, SepsTouch, Touch)
import Fmt (..)
import Fmt.GlueProofs (codeTouching, codeTouchingAppend)
import Fmt.OutputStatements (..)
import Fmt.TouchSteps (..)

-- Fills.

--| The steps of a fill's cells after the first, each after a separator.
def SepsSteps (docs: List Doc) (pre: Seam → Prop) (spacing: List Spacing) (post: Seam → Prop): Prop :=
  ∀ (seam: Seam) (trace: List Touch) (next: Seam → List Touch → Prop) => pre seam
    → (∀ (after: Seam) (added: List Touch) => post after
      → admitsGlue spacing (codeTouching added) = True
      → next after (trace ++ added))
    → SepsTouch docs seam trace next

theorem sepsNil ∀ (pre post: Seam → Prop) (implies: ∀ (seam: Seam) => pre seam → post seam): SepsSteps [] pre [] post :=
  seam trace next holds after => stay post [] seam trace next byComputing after (implies seam holds)

--| A cell after a separator, which touches as a `Line` does, then the cells after it.
theorem sepsCons ∀ (doc: Doc) (docs: List Doc) (pre middle post: Seam → Prop) (front back: List Spacing)
    (first: StepsAll [Line, doc] pre front middle)
    (rest: SepsSteps docs middle back post):
    SepsSteps [doc, ..docs] pre (front ++ back) post :=
  seam trace next holds after =>
    first seam trace (between later => SepsTouch docs between later next) holds (between added reached admits =>
      rest between (trace ++ added) next reached (left more ended admitsMore =>
        rewrite List.appendAssoc trace added more then
          after left
            (added ++ more)
            ended
            (rewrite codeTouchingAppend added more then
              admitsAppend front back (codeTouching added) (codeTouching more) admits admitsMore)))

--| A fill: its first cell, then the others each after a separator.
theorem stepsFill ∀ (doc: Doc) (docs: List Doc) (pre middle post: Seam → Prop) (front back: List Spacing)
    (first: Steps doc pre front middle)
    (rest: SepsSteps docs middle back post):
    Steps (Fill [doc, ..docs]) pre (front ++ back) post :=
  seam trace next holds after =>
    first seam trace (between later => SepsTouch docs between later next) holds (between added reached admits =>
      rest between (trace ++ added) next reached (left more ended admitsMore =>
        rewrite List.appendAssoc trace added more then
          after left
            (added ++ more)
            ended
            (rewrite codeTouchingAppend added more then
              admitsAppend front back (codeTouching added) (codeTouching more) admits admitsMore)))

-- Sequences.

--| Each document's spacing, one after another.
def joinSpacing: List (List Spacing) → List Spacing
  | [] => []
  | [spacing, ..rest] => spacing ++ joinSpacing rest

theorem joinAppend ∀ (front back: List (List Spacing)):
    joinSpacing (front ++ back) = joinSpacing front ++ joinSpacing back :=
  match front with
    | [] => byComputing
    | [spacing, ..rest] => rewrite joinAppend rest back, List.appendAssoc spacing (joinSpacing rest) (joinSpacing back)

theorem joinOne ∀ (spacing: List Spacing): joinSpacing [spacing] = spacing := List.appendNil spacing

theorem joinTakeDrop ∀ (spacings: List (List Spacing)) (count: Nat):
    joinSpacing (spacings.take count) ++ joinSpacing (spacings.drop count) = joinSpacing spacings :=
  rewrite <- joinAppend (spacings.take count) (spacings.drop count), List.appendTakeDrop spacings count

--| Documents one after another, a space or a line break between each two, each spaced as its entry in `spacings`
--| (the two lists alike in length): the first from `pre`, each later one from after a gap; each but the last ends
--| where a comment may wait before the gap, the last at `post`.
def SeqSteps (pre post: Seam → Prop): List Doc → List (List Spacing) → Prop
  | [], [] => ∀ (seam: Seam) => pre seam → post seam
  | [doc, ..rest], [spacing, ..later] => SeqFrom pre post doc spacing rest later
  | _, _ => Void

def SeqFrom (pre post: Seam → Prop) (doc: Doc) (spacing: List Spacing): List Doc → List (List Spacing) → Prop
  | [], [] => Steps doc pre spacing post
  | [next, ..more], [nextSpacing, ..later] =>
    Steps doc pre spacing (Ends True) ∧ SeqFrom (Gapped True) post next nextSpacing more later
  | _, _ => Void

--| The documents with a space between each two.
theorem joinedSteps ∀ (docs: List Doc) (spacings: List (List Spacing)) (pre post: Seam → Prop)
    (seq: SeqSteps pre post docs spacings):
    StepsAll (Doc.joinedWith (Doc.text " ") docs) pre (joinSpacing spacings) post :=
  match docs, spacings, seq with
    | [], [], keeps => stepsNil pre post keeps
    | [only], [spacing], steps =>
      stepsCons only [] pre post post spacing [] steps (stepsNil post post (seam holds => holds))
    | [doc, next, ..more], [spacing, nextSpacing, ..later], (first, rest) =>
      stepsCons doc _ pre
        (Ends True)
        post
        spacing
        (joinSpacing [nextSpacing, ..later])
        first
        (stepsCons
          (Doc.text " ") _
          (Ends True)
          (Gapped True)
          post
          []
          (joinSpacing [nextSpacing, ..later])
          (stepsSpace True)
          (joinedSteps [next, ..more] [nextSpacing, ..later] (Gapped True) post rest))
    | _, _, never => cases then never.impossible

--| `spaced`: the documents on one line, a space between each two.
theorem spacedSteps ∀ (docs: List Doc) (spacings: List (List Spacing)) (pre post: Seam → Prop)
    (seq: SeqSteps pre post docs spacings):
    Steps (spaced docs) pre (joinSpacing spacings) post :=
  stepsConcat _ pre _ post (joinedSteps docs spacings pre post seq)

theorem sepsSeq ∀ (doc: Doc) (more: List Doc) (spacing: List Spacing) (later: List (List Spacing)) (post: Seam → Prop)
    (seq: SeqFrom (Gapped True) post doc spacing more later):
    SepsSteps [doc, ..more] (Ends True) (joinSpacing [spacing, ..later]) post :=
  match more, later, seq with
    | [], [], steps =>
      sepsCons doc []
        (Ends True)
        post
        post
        spacing
        []
        (stepsTwo Line doc (Ends True) (Gapped True) post [] spacing (stepsLine True) steps)
        (sepsNil post post (seam holds => holds))
    | [next, ..others], [nextSpacing, ..rest], (first, seqRest) =>
      sepsCons doc
        [next, ..others]
        (Ends True)
        (Ends True)
        post
        spacing
        (joinSpacing [nextSpacing, ..rest])
        (stepsTwo Line doc (Ends True) (Gapped True) (Ends True) [] spacing (stepsLine True) first)
        (sepsSeq next others nextSpacing rest post seqRest)
    | _, _, never => cases then never.impossible

--| A fill of the documents: the first from `pre`, each later one after a space or a line break.
theorem fillSteps ∀ (docs: List Doc) (spacings: List (List Spacing)) (pre post: Seam → Prop)
    (seq: SeqSteps pre post docs spacings):
    Steps (Fill docs) pre (joinSpacing spacings) post :=
  match docs, spacings, seq with
    | [], [], keeps => seam trace next holds after => stay post [] seam trace next byComputing after (keeps seam holds)
    | [only], [spacing], steps =>
      stepsFill only [] pre post post spacing [] steps (sepsNil post post (seam holds => holds))
    | [doc, next, ..more], [spacing, nextSpacing, ..later], (first, rest) =>
      stepsFill doc
        [next, ..more]
        pre
        (Ends True)
        post
        spacing
        (joinSpacing [nextSpacing, ..later])
        first
        (sepsSeq next more nextSpacing later post rest)
    | _, _, never => cases then never.impossible

--| Documents each on a line of their own.
theorem hardSteps ∀ (docs: List Doc) (spacings: List (List Spacing))
    (pre post: Seam → Prop) (quiet: ∀ (seam: Seam) => pre seam → Quiet seam)
    (filled: docs ≠ [])
    (seq: SeqSteps (Gapped True) post docs spacings):
    StepsAll (docs.concatMap (doc => [HardLine, doc])) pre (joinSpacing spacings) post :=
  match docs, spacings, seq with
    | [], _, _ => (filled byComputing).impossible
    | [only], [spacing], steps =>
      stepsCons HardLine
        [only]
        pre
        (Gapped True)
        post
        []
        (spacing ++ [])
        (stepsHard pre (Gapped True) quiet byComputing)
        (stepsCons only [] (Gapped True) post post spacing [] steps (stepsNil post post (seam holds => holds)))
    | [doc, next, ..more], [spacing, nextSpacing, ..later], (first, rest) =>
      stepsCons HardLine _ pre
        (Gapped True)
        post
        []
        (joinSpacing [spacing, nextSpacing, ..later])
        (stepsHard pre (Gapped True) quiet byComputing)
        (stepsCons doc _
          (Gapped True)
          (Ends True)
          post
          spacing
          (joinSpacing [nextSpacing, ..later])
          first
          (hardSteps
            [next, ..more]
            [nextSpacing, ..later]
            (Ends True)
            post
            (seam ended => endsQuiet True seam ended)
            (List.consNotNil next more)
            rest))
    | _, _, never => cases then never.impossible

--| A sequence split after `keep` documents: those end where a comment may wait, and the rest, never empty, start
--| after a gap.
theorem seqSplit ∀ (docs: List Doc) (spacings: List (List Spacing)) (keep: Nat) (pre post: Seam → Prop)
    (positive: keep ≠ 0)
    (short: keep ≤ docs.length)
    (differs: (keep == docs.length) = False)
    (seq: SeqSteps pre post docs spacings):
    SeqSteps pre (Ends True) (docs.take keep) (spacings.take keep)
      ∧ SeqSteps (Gapped True) post (docs.drop keep) (spacings.drop keep)
      ∧ docs.drop keep ≠ [] :=
  match keep, docs, spacings, seq with
    | Zero, _, _, _ => (positive byComputing).impossible
    | Succ Zero, [doc, next, ..more], [spacing, nextSpacing, ..later], (first, rest) =>
      (first, rest, List.consNotNil next more)
    | Succ (Succ count), [doc, next, ..more], [spacing, nextSpacing, ..later], (first, rest) =>
      let (kept, dropped, filled) :=
        seqSplit
          [next, ..more]
          [nextSpacing, ..later]
          (Succ count)
          (Gapped True)
          post
          (never => cases)
          (arithmetic [short])
          differs
          rest
      ((first, kept), dropped, filled)
    | Succ _, [doc, next, ..more], [], never => never.impossible
    | Succ _, [doc, next, ..more], [spacing], never => never.impossible

-- A call's layouts.

--| A call's last argument opened steps, if it opens.
def HugSteps (hug: Option Doc) (pre: Seam → Prop) (spacing: List Spacing) (post: Seam → Prop): Prop := match hug with
  | None => True
  | Some open => Steps open pre spacing post

theorem hugSpacing ∀ (headSpacing lastSpacing: List Spacing) (spacings: List (List Spacing)):
    joinSpacing [headSpacing, ..spacings] ++ ([] ++ lastSpacing)
      = joinSpacing ([headSpacing, ..spacings] ++ [lastSpacing]) :=
  rewrite joinAppend [headSpacing, ..spacings] [lastSpacing], joinOne lastSpacing

--| A call's layouts (`appFrom`): on one line, filled, hugging its last argument, or the function and the arguments
--| it keeps on its line, then each other argument on a line of its own. In each the documents come in order with a
--| space or a line break between each two, so each spaces its words as the sequence does.
--|
--| Proof idea: as `Fmt.JoinProofs.appFromPasses`: the sequence spaced (`spacedSteps`), filled (`fillSteps`), or
--| split where the kept documents end (`seqSplit`), the rest each after a `HardLine` (`hardSteps`); the hug is the
--| sequence without its last document (`front`), a space, and the last opened.
theorem appFromSteps ∀ (id keep: Nat) (between betweenFront: Bool) (headDoc lastDoc: Doc) (front: List Doc)
    (hug: Option Doc) (headSpacing lastSpacing: List Spacing) (spacings: List (List Spacing)) (pre post: Seam → Prop)
    (seq: SeqFrom pre post headDoc headSpacing (front ++ [lastDoc]) (spacings ++ [lastSpacing]))
    (frontSeq: SeqFrom pre (Ends True) headDoc headSpacing front spacings)
    (hugSteps: HugSteps hug (Gapped True) lastSpacing post)
    (positive: keep ≠ 0)
    (short: keep ≤ ([headDoc, ..front] ++ [lastDoc]).length):
    Steps
      (appFrom id keep between betweenFront headDoc front lastDoc hug).doc
      pre
      (joinSpacing ([headSpacing, ..spacings] ++ [lastSpacing]))
      post :=
  let docs := [headDoc, ..front] ++ [lastDoc]
  let all := [headSpacing, ..spacings] ++ [lastSpacing]
  let whole: SeqSteps pre post docs all := seq
  match full: keep == docs.length with
    | True =>
      match between with
        | True => spacedSteps docs all pre post whole
        | False => stepsNest 4 (Fill docs) pre _ post (fillSteps docs all pre post whole)
    | False =>
      let (keptSeq, droppedSeq, filled) := seqSplit docs all keep pre post positive short full whole
      let rest := Doc.concat (docs.drop keep |> .concatMap (doc => [HardLine, doc]))
      let restSteps: Steps rest (Ends True) (joinSpacing (all.drop keep)) post :=
        stepsConcat _
          (Ends True) _
          post
          (hardSteps
            (docs.drop keep)
            (all.drop keep)
            (Ends True)
            post
            (seam ended => endsQuiet True seam ended)
            filled
            droppedSeq)
      let fillFront := keep > 2 && !betweenFront
      let frontDoc := if fillFront then IdGroup id (Nest 4 (Fill (docs.take keep))) False else spaced (docs.take keep)
      let restDoc := if fillFront then IfBroken id (Nest 4 rest) (Nest 2 rest) else Nest 2 rest
      let frontSteps: Steps frontDoc pre (joinSpacing (all.take keep)) (Ends True) := match fillFront with
        | True =>
          stepsIdGroup id _ False pre _
            (Ends True)
            (stepsNest 4 _ pre _ (Ends True) (fillSteps (docs.take keep) (all.take keep) pre (Ends True) keptSeq))
        | False => spacedSteps (docs.take keep) (all.take keep) pre (Ends True) keptSeq
      let restDocSteps: Steps restDoc (Ends True) (joinSpacing (all.drop keep)) post := match fillFront with
        | True =>
          stepsIfBroken id
            (Nest 4 rest)
            (Nest 2 rest)
            (Ends True) _
            post
            (stepsNest 4 rest (Ends True) _ post restSteps)
            (stepsNest 2 rest (Ends True) _ post restSteps)
        | False => stepsNest 2 rest (Ends True) _ post restSteps
      let broken: Steps (Doc.concat [frontDoc, restDoc]) pre (joinSpacing all) post :=
        stepsSpacing _ pre _ _ post
          (joinTakeDrop all keep)
          (stepsConcat _ pre _ post (stepsTwo frontDoc restDoc pre (Ends True) post _ _ frontSteps restDocSteps))
      let flat: Steps (Flatten (spaced docs)) pre (joinSpacing all) post :=
        stepsFlatten _ pre _ post (spacedSteps docs all pre post whole)
      match hug, hugSteps with
        | None, _ => stepsChoice (Flatten (spaced docs)) [Doc.concat [frontDoc, restDoc]] pre (joinSpacing all) post (
          flat,
          broken,
          byComputing
        )
        | Some open, opens =>
          let hugged: Steps
            (Doc.concat [Flatten (spaced [headDoc, ..front]), Doc.text " ", open])
            pre
            (joinSpacing all)
            post :=
            stepsSpacing _ pre _ _ post
              (hugSpacing headSpacing lastSpacing spacings)
              (stepsConcat _ pre _ post
                (stepsCons
                  (Flatten (spaced [headDoc, ..front])) _
                  pre
                  (Ends True)
                  post
                  (joinSpacing [headSpacing, ..spacings])
                  ([] ++ lastSpacing)
                  (stepsFlatten _ pre _
                    (Ends True)
                    (spacedSteps [headDoc, ..front] [headSpacing, ..spacings] pre (Ends True) frontSeq))
                  (stepsTwo (Doc.text " ") open (Ends True) (Gapped True) post [] lastSpacing (stepsSpace True) opens)))
          stepsChoice
            (Flatten (spaced docs))
            [Doc.concat [Flatten (spaced [headDoc, ..front]), Doc.text " ", open], Doc.concat [frontDoc, restDoc]]
            pre
            (joinSpacing all)
            post
            (flat, hugged, broken, byComputing)

theorem hugTo ∀ (hug: Option Doc) (pre: Seam → Prop) (spacing: List Spacing) (post later: Seam → Prop)
    (steps: HugSteps hug pre spacing post) (implies: ∀ (seam: Seam) => post seam → later seam):
    HugSteps hug pre spacing later :=
  match hug, steps with
    | None, _ => byComputing
    | Some open, opens => stepsTo open pre spacing post later opens implies
