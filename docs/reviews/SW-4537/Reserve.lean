/- SW-4544, stage 2 of SW-4537: the printer's first reserve, `appFromSpells` (Fmt/SpellProofs.sw:935), ported
   for the variant that sets `exprBlanks` aside by rule (b). Lean 4, core only. The counted theorem follows the
   `-- sample:` line; the rest is uncounted support. Check: nix shell nixpkgs#lean4 -c lean Reserve.lean -/

namespace AppFromSpells

axiom Text : Type

/- Cut down from std's `Doc` (Fmt/Rules.sw): the constructors `appFrom` builds; `Group`, `Line`, `Softline`
   and the rest dropped. `Doc.concat` (which drops empty documents) and `spaced` are opaque: the proof reaches
   them only through `spellsConcat` and `spellsSpaced`. -/
inductive Doc where
  | text (s : String)
  | HardLine
  | Nest (indent : Nat) (inner : Doc)
  | Fill (items : List Doc)
  | IdGroup (id : Nat) (inner : Doc) (hard : Bool)
  | IfBroken (id : Nat) (broken flat : Doc)
  | Flatten (inner : Doc)
  | Choice (options : List Doc)

axiom Doc.concat : List Doc → Doc
axiom spaced : List Doc → Doc

/- `Spells` (uniform, marked, and its words are the texts) and `SpellsAll` are reached only through their
   lemmas, so they are opaque. -/
axiom Spells : Doc → List Text → Prop
axiom SpellsAll : List Doc → List Text → Prop

def SpellsEach (texts : List Text) : List Doc → Prop
  | [] => True
  | doc :: docs => Spells doc texts ∧ SpellsEach texts docs

def optionList : Option Doc → List Doc
  | some doc => [doc]
  | none => []

noncomputable section

structure Applied where
  doc : Doc
  hug : Option Doc

/- Stitchwort's `++` groups to the right and Lean's to the left: the brackets keep Stitchwort's terms. -/
def appFrom (id keep : Nat) (between betweenFront : Bool) (headDoc : Doc) (front : List Doc)
    (lastDoc : Doc) (hug : Option Doc) : Applied :=
  let docs := (headDoc :: front) ++ [lastDoc]
  let all := spaced docs
  if keep == docs.length then { doc := if between then all else .Nest 4 (.Fill docs), hug := none }
  else
    let hugged := hug.map (fun opened => Doc.concat [.Flatten (spaced (headDoc :: front)), .text " ", opened])
    let fillFront := keep > 2 && !betweenFront
    let kept := docs.take keep
    let frontDoc := if fillFront then .IdGroup id (.Nest 4 (.Fill kept)) false else spaced kept
    let rest := Doc.concat ((docs.drop keep).flatMap (fun doc => [.HardLine, doc]))
    let restDoc := if fillFront then .IfBroken id (.Nest 4 rest) (.Nest 2 rest) else .Nest 2 rest
    let options := [Doc.Flatten all] ++ (optionList hugged ++ [Doc.concat [frontDoc, restDoc]])
    { doc := .Choice options, hug := hugged }

def AppSpells (applied : Applied) (texts : List Text) : Prop :=
  Spells applied.doc texts ∧ ∀ opened, applied.hug = some opened → Spells opened texts

/- The lemmas the Stitchwort proof names (rule 6). -/
axiom spellsNil : SpellsAll [] []
axiom spellsCons {doc : Doc} {docs : List Doc} {texts later : List Text} (first : Spells doc texts)
    (rest : SpellsAll docs later) : SpellsAll (doc :: docs) (texts ++ later)
axiom spellsLast {doc : Doc} {texts : List Text} (only : Spells doc texts) : SpellsAll [doc] texts
axiom spellsAppend {front back : List Doc} {texts later : List Text} (first : SpellsAll front texts)
    (second : SpellsAll back later) : SpellsAll (front ++ back) (texts ++ later)
axiom spellsSpace : Spells (.text " ") []
axiom spellsNest (indent : Nat) {inner : Doc} {texts : List Text} (spells : Spells inner texts) :
    Spells (.Nest indent inner) texts
axiom spellsFlatten {inner : Doc} {texts : List Text} (spells : Spells inner texts) :
    Spells (.Flatten inner) texts
axiom spellsFill {items : List Doc} {texts : List Text} (each : SpellsAll items texts) :
    Spells (.Fill items) texts
axiom spellsConcat {docs : List Doc} {texts : List Text} (each : SpellsAll docs texts) :
    Spells (Doc.concat docs) texts
axiom spellsChoice {texts : List Text} (first : Doc) (options : List Doc)
    (each : SpellsEach texts (first :: options)) : Spells (.Choice (first :: options)) texts
axiom spellsSpaced {docs : List Doc} {texts : List Text} (each : SpellsAll docs texts) :
    Spells (spaced docs) texts
axiom frontRestSpells (id keep : Nat) (fillFront : Bool) (docs : List Doc) (texts : List Text)
    (spells : SpellsAll docs texts) :
    Spells (Doc.concat [
        if fillFront then .IdGroup id (.Nest 4 (.Fill (docs.take keep))) false else spaced (docs.take keep),
        if fillFront then
          .IfBroken id (.Nest 4 (Doc.concat ((docs.drop keep).flatMap (fun doc => [.HardLine, doc]))))
            (.Nest 2 (Doc.concat ((docs.drop keep).flatMap (fun doc => [.HardLine, doc]))))
        else .Nest 2 (Doc.concat ((docs.drop keep).flatMap (fun doc => [.HardLine, doc])))])
      texts

-- sample: appFromSpells
theorem appFromSpells (id keep : Nat) (between betweenFront : Bool) (headDoc lastDoc : Doc)
    (front : List Doc) (hug : Option Doc) (headTexts frontTexts lastTexts : List Text)
    (headSpells : Spells headDoc headTexts)
    (frontSpells : SpellsAll front frontTexts)
    (lastSpells : Spells lastDoc lastTexts)
    (hugSpells : ∀ opened : Doc, hug = some opened → Spells opened lastTexts) :
    AppSpells (appFrom id keep between betweenFront headDoc front lastDoc hug)
      (headTexts ++ (frontTexts ++ lastTexts)) := by
  have docs : SpellsAll ((headDoc :: front) ++ [lastDoc])
      (headTexts ++ (frontTexts ++ lastTexts)) :=
    spellsCons headSpells (spellsAppend frontSpells (spellsLast lastSpells))
  have third := frontRestSpells id keep (keep > 2 && !betweenFront) _ _ docs
  have all := spellsFlatten (spellsSpaced docs)
  dsimp only [appFrom, AppSpells]
  split
  · refine ⟨?_, by simp⟩
    cases between
    · exact spellsNest 4 (spellsFill docs)
    · exact spellsSpaced docs
  · cases hug with
    | none =>
      refine ⟨spellsChoice _ _ ?_, by simp⟩
      exact ⟨all, third, trivial⟩
    | some opened =>
      have hugged := spellsConcat (spellsCons (spellsFlatten (spellsSpaced (spellsCons headSpells
        frontSpells))) (spellsCons spellsSpace (spellsLast (hugSpells opened rfl))))
      simp only [List.nil_append, List.append_assoc] at hugged
      refine ⟨spellsChoice _ _ ?_, by simpa using hugged⟩
      exact ⟨all, hugged, third, trivial⟩

end

end AppFromSpells
