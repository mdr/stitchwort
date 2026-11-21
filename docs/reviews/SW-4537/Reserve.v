(* SW-4544, stage 2 of SW-4537: the printer's first reserve, appFromSpells (Fmt/SpellProofs.sw:935), ported
   for the variant that sets exprBlanks aside by rule (b). Rocq 9.1 with its Stdlib only. The counted lemma
   follows the "sample:" comment; the rest is uncounted support.
   Check: rocq compile -R <stdlib>/lib/coq/9.1/user-contrib/Stdlib Stdlib Reserve.v *)
From Stdlib Require Import List Bool String Arith.
Import ListNotations.

Module AppFromSpells.

Parameter Text : Type.

(* Cut down from std's Doc (Fmt/Rules.sw): the constructors appFrom builds; Group, Line, Softline and the
   rest dropped. concat (which drops empty documents) and spaced are opaque: the proof reaches them only
   through spellsConcat and spellsSpaced. *)
Inductive Doc :=
  | DText (s : string)
  | HardLine
  | Nest (indent : nat) (inner : Doc)
  | Fill (items : list Doc)
  | IdGroup (id : nat) (inner : Doc) (hard : bool)
  | IfBroken (id : nat) (broken flat : Doc)
  | Flatten (inner : Doc)
  | Choice (options : list Doc).

Parameter concat : list Doc -> Doc.
Parameter spaced : list Doc -> Doc.

(* Spells and SpellsAll are reached only through their lemmas, so they are opaque. *)
Parameter Spells : Doc -> list Text -> Prop.
Parameter SpellsAll : list Doc -> list Text -> Prop.

Fixpoint SpellsEach (texts : list Text) (docs : list Doc) : Prop :=
  match docs with
  | [] => True
  | doc :: more => Spells doc texts /\ SpellsEach texts more
  end.

Definition optionList (o : option Doc) : list Doc :=
  match o with Some doc => [doc] | None => [] end.

Record Applied := { doc : Doc; hug : option Doc }.

Definition breakAll (docs : list Doc) : Doc := concat (flat_map (fun d => [HardLine; d]) docs).

Definition appFrom (id keep : nat) (between betweenFront : bool) (headDoc : Doc) (front : list Doc)
    (lastDoc : Doc) (hugOf : option Doc) : Applied :=
  let docs := (headDoc :: front) ++ [lastDoc] in
  let all := spaced docs in
  if keep =? List.length docs then {| doc := if between then all else Nest 4 (Fill docs); hug := None |}
  else
    let hugged := option_map (fun o => concat [Flatten (spaced (headDoc :: front)); DText " "; o]) hugOf in
    let fillFront := (2 <? keep) && negb betweenFront in
    let kept := firstn keep docs in
    let frontDoc := if fillFront then IdGroup id (Nest 4 (Fill kept)) false else spaced kept in
    let rest := breakAll (skipn keep docs) in
    let restDoc := if fillFront then IfBroken id (Nest 4 rest) (Nest 2 rest) else Nest 2 rest in
    {| doc := Choice ([Flatten all] ++ (optionList hugged ++ [concat [frontDoc; restDoc]]));
       hug := hugged |}.

Definition AppSpells (applied : Applied) (texts : list Text) : Prop :=
  Spells (doc applied) texts /\ (forall o, hug applied = Some o -> Spells o texts).

(* The lemmas the Stitchwort proof names (rule 6). *)
Axiom spellsCons : forall d ds texts later,
  Spells d texts -> SpellsAll ds later -> SpellsAll (d :: ds) (texts ++ later).
Axiom spellsLast : forall d texts, Spells d texts -> SpellsAll [d] texts.
Axiom spellsAppend : forall front back texts later,
  SpellsAll front texts -> SpellsAll back later -> SpellsAll (front ++ back) (texts ++ later).
Axiom spellsSpace : Spells (DText " ") [].
Axiom spellsNest : forall indent inner texts, Spells inner texts -> Spells (Nest indent inner) texts.
Axiom spellsFlatten : forall inner texts, Spells inner texts -> Spells (Flatten inner) texts.
Axiom spellsFill : forall items texts, SpellsAll items texts -> Spells (Fill items) texts.
Axiom spellsConcat : forall docs texts, SpellsAll docs texts -> Spells (concat docs) texts.
Axiom spellsChoice : forall texts first options,
  SpellsEach texts (first :: options) -> Spells (Choice (first :: options)) texts.
Axiom spellsSpaced : forall docs texts, SpellsAll docs texts -> Spells (spaced docs) texts.
Axiom frontRestSpells : forall id keep (fillFront : bool) docs texts, SpellsAll docs texts ->
  Spells (concat [
    if fillFront then IdGroup id (Nest 4 (Fill (firstn keep docs))) false else spaced (firstn keep docs);
    if fillFront then IfBroken id (Nest 4 (breakAll (skipn keep docs))) (Nest 2 (breakAll (skipn keep docs)))
    else Nest 2 (breakAll (skipn keep docs))]) texts.

(* sample: appFromSpells *)
Lemma appFromSpells id keep between betweenFront headDoc lastDoc front hugOf
  headTexts frontTexts lastTexts
  (headSpells : Spells headDoc headTexts) (frontSpells : SpellsAll front frontTexts)
  (lastSpells : Spells lastDoc lastTexts)
  (hugSpells : forall o, hugOf = Some o -> Spells o lastTexts) :
  AppSpells (appFrom id keep between betweenFront headDoc front lastDoc hugOf)
    (headTexts ++ frontTexts ++ lastTexts).
Proof.
  assert (docs := spellsCons _ _ _ _ headSpells (spellsAppend _ _ _ _ frontSpells
    (spellsLast _ _ lastSpells))).
  pose proof (frontRestSpells id keep ((2 <? keep) && negb betweenFront) _ _ docs) as third.
  pose proof (spellsFlatten _ _ (spellsSpaced _ _ docs)) as all.
  unfold appFrom, AppSpells; simpl.
  destruct (keep =? _).
  - split; simpl; [destruct between; auto using spellsNest, spellsFill, spellsSpaced | easy].
  - destruct hugOf as [o |]; simpl; [| split; [now apply spellsChoice | easy]].
    assert (hugged := spellsConcat _ _ (spellsCons _ _ _ _ (spellsFlatten _ _ (spellsSpaced _ _
      (spellsCons _ _ _ _ headSpells frontSpells))) (spellsCons _ _ _ _ spellsSpace
      (spellsLast _ _ (hugSpells o eq_refl))))).
    simpl in hugged; rewrite <- app_assoc in hugged.
    split; [now apply spellsChoice | now intros ? [= <-]].
Qed.

End AppFromSpells.
