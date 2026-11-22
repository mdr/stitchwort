--| What a property of documents needs of the printer's combinators for the facts about a call's layouts (`appFrom`) to
--| be proved once, for any such property (SW-4562, after `DocHolds` for `bodyAfter`).
--|
--| Unlike `DocHolds`, the reading changes along the way: the documents of a call's line and of the lines below it
--| each read part of what the whole call reads. So a property here has two sides: `r doc reading` for one document,
--| and `rs docs readings` for a list of them, whose readings (a `b`) turn into one reading by `flat`, and are built
--| one document at a time by `cons` (one before the rest) and `snoc` (one after).

namespace Fmt.AppHolds
import Std (Bool, Doc, Eq, List, Nat, Option)
import Std.Doc (..)
import Fmt (..)

--| A property of documents, `r`, and of lists of them, `rs`, that the combinators `appFrom` uses keep.
type AppHolds (a b: Type) (r: Doc → List a → Prop) (rs: List Doc → b → Prop) (flat: b → List a) (cons: List a
  → b
  → b) (snoc: b → List a → b) = {
  nest: ∀ (indent: Nat) (doc: Doc) (reading: List a) => r doc reading → r (Nest indent doc) reading,
  flatten: ∀ (doc: Doc) (reading: List a) => r doc reading → r (Flatten doc) reading,
  idGroup: ∀ (id: Nat) (hard: Bool) (doc: Doc) (reading: List a) => r doc reading → r (IdGroup id doc hard) reading,
  ifBroken: ∀ (id: Nat) (broken plain: Doc) (reading: List a) => r broken reading
    → r plain reading
    → r (IfBroken id broken plain) reading,
  choice: ∀ (first: Doc) (more: List Doc) (reading: List a) => List.All (doc => r doc reading) [first, ..more]
    → r (Choice [first, ..more]) reading,
  fillOf: ∀ (docs: List Doc) (readings: b) => rs docs readings → r (Fill docs) (flat readings),
  spacedOf: ∀ (docs: List Doc) (readings: b) => rs docs readings → r (spaced docs) (flat readings),
  hugged: ∀ (docs: List Doc) (open: Doc) (readings: b) (last: List a) => rs docs readings
    → r open last
    → r (Doc.concat [Flatten (spaced docs), Doc.text " ", open]) (flat readings ++ last),
  frontRest: ∀ (id keep: Nat) (fillFront: Bool) (docs: List Doc) (readings: b) => rs docs readings
    → r
      (Doc.concat [
        if fillFront then IdGroup id (Nest 4 (Fill (docs.take keep))) False else spaced (docs.take keep),
        if fillFront then
          IfBroken id
            (Nest 4 (Doc.concat (docs.drop keep |> .concatMap (doc => [HardLine, doc]))))
            (Nest 2 (Doc.concat (docs.drop keep |> .concatMap (doc => [HardLine, doc]))))
        else Nest 2 (Doc.concat (docs.drop keep |> .concatMap (doc => [HardLine, doc])))
      ])
      (flat readings),
  consed: ∀ (doc: Doc) (docs: List Doc) (reading: List a) (readings: b) => r doc reading
    → rs docs readings
    → rs [doc, ..docs] (cons reading readings),
  snoced: ∀ (docs: List Doc) (doc: Doc) (readings: b) (reading: List a) => rs docs readings
    → r doc reading
    → rs (docs ++ [doc]) (snoc readings reading),
  consFlat: ∀ (reading: List a) (readings: b) => flat (cons reading readings) = reading ++ flat readings,
  snocFlat: ∀ (reading: List a) (readings: b) (last: List a) => flat (snoc (cons reading readings) last)
    = reading ++ flat readings ++ last
}

--| A call's document and its hug have the property when the function's, the arguments before the last, the last and
--| the last's hug do.
--|
--| Proof idea: Cases on whether every element stays on its line; else each option of the choice (flat, hugged if the
--| last argument hugs, the front and the rest) has the property.
theorem appFromHolds ∀ [a b: Type] [r: Doc → List a → Prop] [rs: List Doc → b → Prop] [flat: b → List a]
    [cons: List a → b → b] [snoc: b → List a → b]
    (holds: AppHolds a b r rs flat cons snoc)
    (id keep: Nat) (between betweenFront: Bool) (headDoc lastDoc: Doc) (front: List Doc) (hug: Option Doc)
    (head: List a) (readings: b) (last: List a) (headR: r headDoc head) (frontR: rs front readings)
    (lastR: r lastDoc last) (hugR: ∀ (open: Doc) => hug = Some open → r open last):
    r (appFrom id keep between betweenFront headDoc front lastDoc hug).doc (head ++ flat readings ++ last)
      ∧ (∀ (open: Doc) => (appFrom id keep between betweenFront headDoc front lastDoc hug).hug = Some open
        → r open (head ++ flat readings ++ last)) :=
  let frontsR := holds.consed headDoc front head readings headR frontR
  let docsR := holds.snoced [headDoc, ..front] lastDoc (cons head readings) last frontsR lastR
  rewrite <- holds.snocFlat head readings last then
    match keep == ([headDoc, ..front] ++ [lastDoc]).length with
      | True => (
        (match between with
          | True => holds.spacedOf _ _ docsR
          | False => holds.nest 4 _ _ (holds.fillOf _ _ docsR)),
        (open none => cases)
      )
      | False =>
        let third := holds.frontRest id keep (keep > 2 && !betweenFront) _ _ docsR
        let all := holds.flatten _ _ (holds.spacedOf _ _ docsR)
        match hug with
          | None => (
            holds.choice (Flatten (spaced ([headDoc, ..front] ++ [lastDoc]))) [_] _ (all, (third, Trivial)),
            (open same => cases)
          )
          | Some opened =>
            let total: flat (cons head readings) ++ last = flat (snoc (cons head readings) last) :=
              rewrite holds.consFlat head readings, holds.snocFlat head readings last then
                List.appendAssoc head (flat readings) last
            let huggedR := rewrite total at holds.hugged _ _ _ _ frontsR (hugR opened byComputing)
            (
              holds.choice (Flatten (spaced ([headDoc, ..front] ++ [lastDoc]))) [_, _] _ (
                all,
                (huggedR, (third, Trivial))
              ),
              (open same => rewrite <- Option.someInjective same then huggedR)
            )
