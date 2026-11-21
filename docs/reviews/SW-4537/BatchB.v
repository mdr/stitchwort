(* SW-4537 batch B (the syntax side): seven drawn slice 1 theorems in Rocq 9.1 with its Stdlib only.
   Counted lemmas follow a "sample:" comment; everything else is uncounted support
   (cut-down definitions, and lemmas the Stitchwort proof names, as axioms).
   Check: rocq compile -R <stdlib>/lib/coq/9.1/user-contrib/Stdlib Stdlib BatchB.v *)
From Stdlib Require Import List Bool String Lia PeanoNat.
Import ListNotations.
Open Scope nat_scope.
Open Scope string_scope.
Open Scope nat_scope.

(** * settle 3: homeStands (Fmt/SettleOutputProofs.sw) *)
Module HomeStands.

(* Cut down from Syntax.Tok: one word kind, the comma, one closer, and | (outside slice 1). *)
Inductive Tok := Lower | Comma | RParen | Pipe.
Scheme Equality for Tok.

Definition isCloser (kind : Tok) : bool := match kind with RParen => true | _ => false end.
(* Cut down from Fmt/Slice1.sw: | is the one kind here outside slice 1. *)
Definition within1 (kind : Tok) : bool := match kind with Pipe => false | _ => true end.

(* Rocq's record fields share one namespace, so some are renamed: ctext, wtext, ttext and so on. *)
Record Comment := { ctext : string; column : nat; cblank : nat }.
Record Trivia := { leading : list Comment; tblank : nat; trailing : option Comment }.
Record Token := { kind : Tok; ttext : string; tcolumn : nat; lineStart : bool }.
Record Leaf := { token : Token; trivia : Trivia }.
Record Note := { ntext : string; nblank : bool }.
Record Comments := { above : list Note; after : option string; cblankBefore : bool }.
Record Word := { wtext : string; comments : Comments }.

Definition note_eq_dec (x y : Note) : {x = y} + {x <> y}.
Proof. decide equality; auto using bool_dec, string_dec. Defined.

Definition notes_eqb (xs ys : list Note) : bool := if list_eq_dec note_eq_dec xs ys then true else false.
Definition text_opt_eqb (x y : option string) : bool :=
  match x, y with Some a, Some b => String.eqb a b | None, None => true | _, _ => false end.

Notation lkind leaf := (kind (token leaf)).
Definition withTrailing (leaf : Leaf) (c : option Comment) : Leaf :=
  {| token := token leaf; trivia := {| leading := leading (trivia leaf); tblank := tblank (trivia leaf);
                                       trailing := c |} |}.
Definition withLeading (leaf : Leaf) (cs : list Comment) : Leaf :=
  {| token := token leaf; trivia := {| leading := cs; tblank := tblank (trivia leaf);
                                       trailing := trailing (trivia leaf) |} |}.
Definition unspaced (c : Comment) : Comment := {| ctext := ctext c; column := column c; cblank := 0 |}.

Definition word (leaf : Leaf) : Word :=
  {| wtext := ttext (token leaf);
     comments := {| above := map (fun c => {| ntext := ctext c; nblank := 0 <? cblank c |}) (leading (trivia leaf));
                    after := option_map ctext (trailing (trivia leaf));
                    cblankBefore := 0 <? tblank (trivia leaf) |} |}.

Definition trails (w : Word) : bool := if after (comments w) then true else false.
Definition noted (w : Word) : bool := negb (match above (comments w) with [] => true | _ => false end).
Definition isCloserText (text : string) : bool :=
  String.eqb text ")" || String.eqb text "]" || String.eqb text "}".
Definition isEmpty {A} (xs : list A) : bool := match xs with [] => true | _ => false end.

Fixpoint trailsBack (ws : list Word) : bool :=
  match ws with [] => false | w :: rest => trails w || (isCloserText (wtext w) && trailsBack rest) end.

Fixpoint homedBack (ws : list Word) : bool :=
  match ws with
  | [] => true
  | w :: earlier =>
    (negb (isCloserText (wtext w) && trails w) || isEmpty earlier || noted w || trailsBack earlier)
      && homedBack earlier
  end.

Definition headedAs (leaf : Leaf) (w : Word) : bool :=
  String.eqb (ttext (token leaf)) (wtext w) && notes_eqb (above (comments (word leaf))) (above (comments w))
    && Bool.eqb (cblankBefore (comments (word leaf))) (cblankBefore (comments w)).

Definition tucked (owed : option string) (leaf : Leaf) : option (option string) :=
  match owed, trailing (trivia leaf) with
  | None, None => Some None
  | None, Some _ => None
  | Some _, None => if lineStart (token leaf) then None else Some owed
  | Some text, Some c => if lineStart (token leaf) || negb (String.eqb (ctext c) text) then None else Some None
  end.

Fixpoint stands (owed : option string) (words : list Word) (leaves : list Leaf) : bool :=
  match leaves with
  | [] => isEmpty words && negb (if owed then true else false)
  | leaf :: rest =>
    if Tok_beq (lkind leaf) Comma then
      isEmpty (leading (trivia leaf)) && (tblank (trivia leaf) =? 0)
        && match tucked owed leaf with None => false | Some still => stands still words rest end
    else
      match words with
      | [] => false
      | w :: later =>
        headedAs leaf w
          && match owed, after (comments w) with
             | Some _, Some _ => false
             | Some _, None =>
               isCloser (lkind leaf)
                 && match tucked owed leaf with None => false | Some still => stands still later rest end
             | None, None => negb (if trailing (trivia leaf) then true else false) && stands None later rest
             | None, Some text =>
               (negb (isCloser (lkind leaf)) || lineStart (token leaf))
                 && match trailing (trivia leaf) with
                    | None => stands (Some text) later rest
                    | Some c => String.eqb (ctext c) text && stands None later rest
                    end
             end
      end
  end.

Definition passable (leaf : Leaf) : bool := Tok_beq (lkind leaf) Comma || isCloser (lkind leaf).

Fixpoint endsOn (leaves : list Leaf) : bool :=
  match leaves with
  | [] => false
  | leaf :: earlier =>
    if trailing (trivia leaf) then true
    else if isEmpty earlier || negb (passable leaf) then false
    else endsOn earlier
  end.

Definition stopsAt (leaf : Leaf) (older : list Leaf) : bool :=
  lineStart (token leaf) && (negb (isEmpty (leading (trivia leaf))) || endsOn older).

Fixpoint chainTo (steps : nat) (behind : list Leaf) : bool :=
  match steps, behind with
  | 1, target :: older => negb (passable target) || isEmpty older || stopsAt target older
  | S (S _ as more), leaf :: earlier => passable leaf && negb (lineStart (token leaf)) && chainTo more earlier
  | _, _ => false
  end.

Fixpoint trailingAt (behind : list Leaf) (steps : nat) (c : Comment) : list Leaf :=
  match behind, steps with
  | leaf :: earlier, 1 => withTrailing leaf (Some c) :: earlier
  | leaf :: earlier, S (S _ as more) => leaf :: trailingAt earlier more c
  | _, _ => behind
  end.

Definition tokens (leaves : list Leaf) : list Token := map token leaves.

(* Rule 1's movable, stepsBack and barBelow look at record-update bars (recordBar), which slice 1 never
   reaches; the proof uses them only through movableQuiet1, chainSteps, landedHere and barsQuiet1, so they
   are opaque here. *)
Parameter movable : Leaf -> list Leaf -> list Leaf -> bool.
Parameter stepsBack : bool -> Leaf -> list Leaf -> list Leaf -> nat -> nat.
Parameter barBelow : Leaf -> list Leaf -> list Leaf -> bool.

Fixpoint homeFrom (bareLast : bool) (behind : list Leaf) (bumped : option Comment) (rest : list Leaf)
  : list Leaf :=
  match rest with
  | [] => rev behind
  | leaf0 :: ahead =>
    let leaf := match bumped with Some c => withLeading leaf0 (c :: leading (trivia leaf0)) | None => leaf0 end in
    match trailing (trivia leaf) with
    | Some c =>
      if movable leaf behind ahead then
        match stepsBack bareLast leaf behind ahead 0 with
        | 0 =>
          if barBelow leaf behind ahead
          then homeFrom bareLast (withTrailing leaf None :: behind) (Some (unspaced c)) ahead
          else homeFrom bareLast (leaf :: behind) None ahead
        | steps => homeFrom bareLast (withTrailing leaf None :: trailingAt behind steps c) None ahead
        end
      else homeFrom bareLast (leaf :: behind) None ahead
    | None => homeFrom bareLast (leaf :: behind) None ahead
    end
  end.

Definition agrees (leaf : Leaf) : bool := Bool.eqb (isCloser (lkind leaf)) (isCloserText (ttext (token leaf))).

Definition fits (leaf : Leaf) (w : Word) : bool :=
  headedAs leaf w && text_opt_eqb (option_map ctext (trailing (trivia leaf))) (after (comments w)) && agrees leaf.

Definition bare (leaf : Leaf) : bool :=
  negb (if trailing (trivia leaf) then true else false) && isEmpty (leading (trivia leaf)).

Fixpoint matched (behind : list Leaf) (done : list Word) : bool :=
  match behind with
  | [] => isEmpty done
  | leaf :: earlier =>
    if Tok_beq (lkind leaf) Comma then negb (isEmpty done) && bare leaf && matched earlier done
    else match done with [] => false | w :: older => fits leaf w && matched earlier older end
  end.

Definition lands (leaf : Leaf) (earlier : list Leaf) : bool :=
  negb (passable leaf) || isEmpty earlier || stopsAt leaf earlier.

Fixpoint owing (text : string) (behind : list Leaf) (done : list Word) : bool :=
  match behind with
  | [] => false
  | leaf :: earlier =>
    if Tok_beq (lkind leaf) Comma then bare leaf && negb (lineStart (token leaf)) && owing text earlier done
    else
      match done with
      | [] => false
      | w :: older =>
        if text_opt_eqb (after (comments w)) (Some text) then
          negb (if trailing (trivia leaf) then true else false) && headedAs leaf w && agrees leaf
            && lands leaf earlier && matched earlier older
        else isCloser (lkind leaf) && negb (lineStart (token leaf)) && fits leaf w && owing text earlier older
      end
  end.

Definition held (owed : option string) (behind : list Leaf) (done : list Word) : bool :=
  match owed with None => matched behind done | Some text => owing text behind done end.

Definition notCommaFirst (leaves : list Leaf) : bool :=
  match leaves with [] => true | leaf :: _ => negb (Tok_beq (lkind leaf) Comma) end.

Definition kindWithin (leaf : Leaf) : bool := within1 (lkind leaf).

Axiom movableQuiet1 : forall leaf behind ahead, within1 (lkind leaf) = true ->
  movable leaf behind ahead = (Tok_beq (lkind leaf) Comma && negb (lineStart (token leaf))) || isCloser (lkind leaf).
Axiom barsQuiet1 : forall leaf behind ahead, within1 (lkind leaf) = true -> barBelow leaf behind ahead = false.
Axiom chainSteps : forall current behind ahead steps acc,
  within1 (lkind current) = true -> forallb kindWithin behind = true -> passable current = true ->
  lineStart (token current) = false -> chainTo steps behind = true ->
  stepsBack false current behind ahead acc = acc + steps.
Axiom landedHere : forall leaf older ahead steps,
  within1 (lkind leaf) = true -> forallb kindWithin older = true ->
  (negb (passable leaf) || isEmpty older || stopsAt leaf older) = true ->
  stepsBack false leaf older ahead steps = steps.
Axiom withinOfTokens : forall xs ys, tokens xs = tokens ys -> forallb kindWithin ys = true ->
  forallb kindWithin xs = true.
Axiom trailingAtTokens : forall behind steps c, tokens (trailingAt behind steps c) = tokens behind.
Axiom owingNonEmpty : forall text behind done, owing text behind done = true -> negb (isEmpty done) = true.
Axiom homedReverseOnto : forall xs ys, homedBack (rev_append xs ys) = true -> homedBack ys = true.
Axiom landing : forall leaf w behind done,
  Tok_beq (lkind leaf) Comma = false -> headedAs leaf w = true -> agrees leaf = true ->
  (if after (comments w) then true else false) = true ->
  (negb (isCloser (lkind leaf)) || lineStart (token leaf)) = true ->
  matched behind done = true -> homedBack (w :: done) = true -> lands leaf behind = true.
Axiom owingPlaced : forall text behind done c, owing text behind done = true -> ctext c = text ->
  exists steps, chainTo (S steps) behind = true /\ matched (trailingAt behind (S steps) c) done = true.

(* sample: homeStands *)
Lemma homeStands (owed : option string) (behind rest : list Leaf) (done words : list Word)
  (standing : stands owed words rest = true)
  (state : held owed behind done = true)
  (lead : (negb (isEmpty done) || notCommaFirst rest) = true)
  (homed : homedBack (rev_append words done) = true)
  (behindWithin : forallb kindWithin behind = true)
  (within : forallb kindWithin rest = true)
  (agree : forallb agrees rest = true) :
  matched (rev (homeFrom false behind None rest)) (rev_append words done) = true.
Proof.
  revert owed behind done words standing state lead homed behindWithin within agree.
  induction rest as [| leaf ahead IH];
    intros owed behind done words standing state lead homed bw within agree.
  - destruct owed, words; simpl in *; try discriminate. now rewrite rev_involutive.
  - simpl in within, agree.
    apply andb_prop in within as [W within]. apply andb_prop in agree as [A agree].
    assert (pushed : forallb kindWithin (leaf :: behind) = true)
      by exact (andb_true_intro (conj W bw)).
    (* a moved comment's target keeps its tokens, so stays within slice 1 *)
    assert (target : forall steps c,
      forallb kindWithin (withTrailing leaf None :: trailingAt behind steps c) = true).
    { intros steps c.
      exact (andb_true_intro (conj W (withinOfTokens _ _ (trailingAtTokens _ _ _) bw))). }
    simpl in standing. unfold held in state. simpl homeFrom.
    destruct (Tok_beq (lkind leaf) Comma) eqn:comma.
    + assert (filled : negb (isEmpty done) = true).
      { destruct owed as [text |]; [exact (owingNonEmpty _ _ _ state) |].
        simpl in lead. now rewrite comma, orb_false_r in lead. }
      apply andb_prop in standing as [[leading _]%andb_prop tuck]. unfold tucked in tuck.
      destruct owed as [text |], (trailing (trivia leaf)) as [c |] eqn:tr; try discriminate.
      * (* the comma holds the owed comment: it walks back to its word *)
        destruct (lineStart (token leaf)) eqn:start, (String.eqb (ctext c) text) eqn:named;
          try discriminate.
        apply String.eqb_eq in named.
        destruct (owingPlaced _ _ _ _ state named) as [steps [chain placed]].
        rewrite (movableQuiet1 _ _ _ W), comma, start,
          (chainSteps _ _ _ _ _ W bw (orb_true_intro _ _ (or_introl comma)) start chain).
        apply (IH None); auto; [| now rewrite filled].
        simpl. rewrite comma, filled, placed. unfold bare. simpl. now rewrite leading.
      * (* a comment owed, carried past the comma *)
        destruct (lineStart (token leaf)) eqn:start; try discriminate.
        apply (IH (Some text)); auto; [| now rewrite filled].
        simpl. rewrite comma. unfold bare. now rewrite tr, leading, start, state.
      * (* nothing owed, nothing held *)
        apply (IH None); auto; [| now rewrite filled].
        simpl. rewrite comma, filled. unfold bare. now rewrite tr, leading, state.
    + destruct words as [| w later]; [discriminate |].
      apply andb_prop in standing as [headed clause].
      assert (fitted : forall moved, token moved = token leaf ->
        leading (trivia moved) = leading (trivia leaf) ->
        tblank (trivia moved) = tblank (trivia leaf) ->
        text_opt_eqb (option_map ctext (trailing (trivia moved))) (after (comments w)) = true ->
        fits moved w = true).
      { intros moved tok lead' blank tr.
        assert (same : headedAs moved w = headedAs leaf w)
          by (unfold headedAs, word; now rewrite tok, lead', blank).
        unfold fits. rewrite same, headed, tr. unfold agrees in *. now rewrite tok. }
      destruct owed as [text |], (after (comments w)) as [text' |] eqn:afterIs; try discriminate.
      * (* an earlier word's comment owed: the leaf is a closer carrying it *)
        apply andb_prop in clause as [closer tuck]. unfold tucked in tuck.
        destruct (trailing (trivia leaf)) as [c |] eqn:tr, (lineStart (token leaf)) eqn:start;
          try discriminate.
        ++ destruct (String.eqb (ctext c) text) eqn:named; try discriminate.
           apply String.eqb_eq in named.
           destruct (owingPlaced _ _ _ _ state named) as [steps [chain placed]].
           rewrite (movableQuiet1 _ _ _ W), closer, orb_true_r,
             (chainSteps _ _ _ _ _ W bw (orb_true_intro _ _ (or_intror closer)) start chain).
           apply (IH None _ (w :: done) later); auto. simpl. rewrite comma, placed, andb_true_r.
           apply fitted; auto.
        ++ apply (IH (Some text) _ (w :: done) later); auto.
           simpl. rewrite comma, afterIs, closer, start, state.
           rewrite fitted; auto. now rewrite tr.
      * (* the word's own comment: on the leaf, or owed on *)
        apply andb_prop in clause as [open_ tuck].
        assert (landsHere := landing _ _ _ _ comma headed A ltac:(now rewrite afterIs) open_ state
          (homedReverseOnto later (w :: done) homed)).
        destruct (trailing (trivia leaf)) as [c |] eqn:tr.
        ++ apply andb_prop in tuck as [named tuck].
           assert (kept : matched (rev (homeFrom false (leaf :: behind) None ahead))
             (rev_append (w :: later) done) = true).
           { apply (IH None _ (w :: done) later); auto. simpl. rewrite comma, state, andb_true_r.
             apply fitted; auto. rewrite tr. exact named. }
           destruct (movable leaf behind ahead); [| exact kept].
           now rewrite landedHere, barsQuiet1.
        ++ apply (IH (Some text') _ (w :: done) later); auto. simpl. rewrite comma, afterIs. simpl.
           now rewrite String.eqb_refl, tr, headed, A, landsHere, state.
      * (* nothing owed, no comment on the word *)
        apply andb_prop in clause as [bareTrail tuck].
        destruct (trailing (trivia leaf)) as [c |] eqn:tr; try discriminate.
        apply (IH None _ (w :: done) later); auto. simpl. rewrite comma, state, andb_true_r.
        apply fitted; auto. now rewrite tr.
Qed.

End HomeStands.

(** * settle 2: settledHomed (Syntax/SettleProofs.sw) *)
Module SettledHomed.

(* The proof chains lemmas about rule N's passes, so the passes and most predicates are opaque; only what it
   computes with is defined: tokens, the empty cases of homedBehind, related and walkClean, and settled. *)
Parameter Tok : Type.
Parameter within1 : Tok -> bool.
Parameter Comment : Type.
Parameter Carried : Type.

(* Cut down from Syntax.Token: text and column dropped; from Syntax.Trivia: blankLines dropped. *)
Record Token := { kind : Tok; lineStart : bool }.
Record Trivia := { leading : list Comment; trailing : option Comment }.
Record Leaf := { token : Token; trivia : Trivia }.
Record Lexed := { leaves : list Leaf; end_ : Trivia }.

Definition kindWithin (leaf : Leaf) : bool := within1 (kind (token leaf)).
Definition tokens (ls : list Leaf) : list Token := map token ls.

Parameter homedLeaf : Leaf -> list Leaf -> bool.
Fixpoint homedBehind (ls : list Leaf) : bool :=
  match ls with [] => true | leaf :: older => homedLeaf leaf older && homedBehind older end.

Parameter relatedLeaf : Leaf -> Leaf -> bool.
Fixpoint related (befores afters : list Leaf) : bool :=
  match befores, afters with
  | [], [] => true
  | b :: bs, a :: as_ => relatedLeaf b a && related bs as_
  | _, _ => false
  end.

Parameter skipped : Leaf -> list Leaf -> list Leaf -> bool.
Parameter endsWithComment : list Leaf -> list Leaf -> bool.
Definition isEmpty {A} (xs : list A) : bool := match xs with [] => true | _ => false end.
Fixpoint walkClean (current : Leaf) (behind ahead : list Leaf) : bool :=
  match behind with
  | [] => true
  | previous :: earlier =>
    if negb (skipped current behind ahead) then true
    else if lineStart (token current)
      && (negb (isEmpty (leading (trivia current))) || endsWithComment behind (current :: ahead)) then true
    else isEmpty (leading (trivia current)) && negb (if trailing (trivia previous) then true else false)
      && walkClean previous earlier (current :: ahead)
  end.

Definition CleanFor (behind : list Leaf) (pending : bool) : Prop :=
  forall next ahead, (isEmpty (leading (trivia next)) || lineStart (token next)) = true ->
    (negb pending || lineStart (token next)) = true -> walkClean next behind ahead = true.

Parameter alphabet1 : list Leaf -> bool.
Parameter laidOut : bool -> list Leaf -> bool.
Parameter plain1 plainFrom backOk : list Token -> bool.
Parameter homeFrom : bool -> list Leaf -> option Comment -> list Leaf -> list Leaf.
Parameter commasFrom : list Leaf -> option Carried -> list Leaf -> Trivia -> Lexed.
Parameter arrows : list Leaf -> list Leaf.
Parameter letsFrom : list Leaf -> list Leaf -> list Leaf.
Parameter trimmed : Trivia -> Trivia.

Definition trim (leaf : Leaf) : Leaf := {| token := token leaf; trivia := trimmed (trivia leaf) |}.

Definition settledWith (lexed : Lexed) (bareLast : bool) : Lexed :=
  let homed := homeFrom bareLast [] None (leaves lexed) in
  let commas := commasFrom [] None homed (end_ lexed) in
  {| leaves := map trim (letsFrom [] (arrows (leaves commas))); end_ := trimmed (end_ commas) |}.
Definition settled (lexed : Lexed) : Lexed := settledWith lexed false.

Axiom alphabet1Leaves : forall ls, alphabet1 ls = true -> forallb kindWithin ls = true.
Axiom homeFromTokens : forall bareLast behind bumped rest,
  tokens (homeFrom bareLast behind bumped rest) = tokens (rev_append behind rest).
Axiom commasFromTokens : forall done carried rest e,
  tokens (leaves (commasFrom done carried rest e)) = tokens (rev_append done rest).
Axiom arrowsTokens : forall ls, tokens (arrows ls) = tokens ls.
Axiom trimmedTokens : forall ls, tokens (map trim ls) = tokens ls.
Axiom homeFromHomed : forall behind rest pending, CleanFor behind pending -> laidOut pending rest = true ->
  forallb kindWithin behind = true -> forallb kindWithin rest = true -> homedBehind behind = true ->
  homedBehind (rev_append (homeFrom false behind None rest) []) = true.
Axiom homedTransfer : forall befores afters, tokens befores = tokens afters -> related befores afters = true ->
  backOk (tokens befores) = true -> homedBehind befores = true -> homedBehind afters = true.
Axiom tokensReversed : forall xs ys, tokens xs = tokens ys -> tokens (rev_append xs []) = tokens (rev_append ys []).
Axiom relatedReverseOnto : forall befores afters befores2 afters2,
  related befores afters = true -> related befores2 afters2 = true ->
  related (rev_append befores befores2) (rev_append afters afters2) = true.
Axiom commasRelated : forall doneBefore done carried rest e, related doneBefore done = true ->
  related (rev_append doneBefore rest) (leaves (commasFrom done carried rest e)) = true.
Axiom backOkOf : forall ls original, tokens ls = original -> plain1 original = true ->
  backOk (tokens (rev_append ls [])) = true.
Axiom arrowsRelatedAll : forall ls, plainFrom (tokens ls) = true -> related ls (arrows ls) = true.
Axiom plainFromOf : forall original, plain1 original = true -> plainFrom original = true.
Axiom withinOfTokens : forall xs ys, tokens xs = tokens ys -> forallb kindWithin ys = true ->
  forallb kindWithin xs = true.
Axiom letsQuiet1 : forall behind rest, forallb kindWithin behind = true -> forallb kindWithin rest = true ->
  letsFrom behind rest = rev_append behind rest.
Axiom trimRelated : forall ls, related ls (map trim ls) = true.

(* sample: settledHomed *)
Lemma settledHomed (lexed : Lexed) (within : alphabet1 (leaves lexed) = true)
  (laid : laidOut false (leaves lexed) = true) (plain : plain1 (tokens (leaves lexed)) = true) :
  homedBehind (rev_append (leaves (settled lexed)) []) = true.
Proof.
  pose proof (alphabet1Leaves _ within) as leavesWithin.
  set (homed := homeFrom false [] None (leaves lexed)).
  set (commas := commasFrom [] None homed (end_ lexed)).
  set (arrowed := arrows (leaves commas)).
  assert (homedTokens : tokens homed = tokens (leaves lexed)) by apply homeFromTokens.
  assert (commasTokens : tokens (leaves commas) = tokens (leaves lexed))
    by (rewrite <- homedTokens; apply commasFromTokens).
  assert (arrowedTokens : tokens arrowed = tokens (leaves lexed))
    by (rewrite <- commasTokens; apply arrowsTokens).
  assert (homed1 : homedBehind (rev_append homed []) = true)
    by (apply (homeFromHomed [] _ false); auto; intros ? ? ? ?; reflexivity).
  assert (homed2 : homedBehind (rev_append (leaves commas) []) = true).
  { apply (homedTransfer (rev_append homed [])); auto.
    - apply tokensReversed. congruence.
    - apply relatedReverseOnto; auto. now apply (commasRelated []).
    - now apply (backOkOf _ (tokens (leaves lexed))). }
  assert (homed3 : homedBehind (rev_append arrowed []) = true).
  { apply (homedTransfer (rev_append (leaves commas) [])); auto.
    - apply tokensReversed. congruence.
    - apply relatedReverseOnto; auto.
      apply arrowsRelatedAll. rewrite commasTokens. now apply plainFromOf.
    - now apply (backOkOf _ (tokens (leaves lexed))). }
  unfold settled, settledWith; fold homed commas arrowed; simpl leaves.
  rewrite letsQuiet1 by (auto; now apply (withinOfTokens _ (leaves lexed))).
  change (rev_append [] arrowed) with arrowed.
  apply (homedTransfer (rev_append arrowed [])); auto.
  - apply tokensReversed. now rewrite trimmedTokens.
  - apply relatedReverseOnto; auto using trimRelated.
  - now apply (backOkOf _ (tokens (leaves lexed))).
Qed.

End SettledHomed.

(** * settle 1: endsQuietJoin (Fmt/SettleOutputProofs.sw) *)
Module EndsQuietJoin.

Parameter Word : Type.
(* Opaque: operatorTok word.text == Some Arrow, which the proof never looks into. *)
Parameter arrowText : Word -> bool.

Fixpoint endsQuiet (ws : list Word) : bool :=
  match ws with
  | [] => false
  | [w] => negb (arrowText w)
  | _ :: rest => endsQuiet rest
  end.

(* sample: endsQuietJoin *)
Lemma endsQuietJoin (xs ys : list Word) (quiet : endsQuiet ys = true) : endsQuiet (xs ++ ys) = true.
Proof.
  induction xs as [| x [| next rest] IH];
    [exact quiet | destruct ys; [discriminate | exact quiet] | exact IH].
Qed.

End EndsQuietJoin.

(** * lexer 2: headerResult1 (Fmt/SourcePlainProofs.sw) *)
Module HeaderResult1.

Parameter Comments Word Group Expr : Type.
Parameter wordText : Word -> string.
Parameter exprGrammar1 : Expr -> bool.
Parameter isName1 : string -> bool.

Inductive DefKind := DefPlain | DefTheorem | DefInstance.

Record Header := {
  exportKeyword : option Comments;
  opaqueKeyword : option Comments;
  kind : DefKind;
  keyword : Comments;
  name : Word;
  forallKeyword : option Word;
  params : list Group;
  colon : Comments;
  result : Expr;
  decreasingClause : option (Comments * Expr);
  unfoldingClause : option (Comments * list Word)
}.

Definition grammar1 (header : Header) : bool :=
  match header with
  | {| exportKeyword := None; opaqueKeyword := None; kind := DefPlain; name := n; forallKeyword := None;
       params := []; result := r; decreasingClause := None; unfoldingClause := None |} =>
    isName1 (wordText n) && exprGrammar1 r
  | _ => false
  end.

(* sample: headerResult1 *)
Lemma headerResult1 (header : Header) (grammar : grammar1 header = true) :
  exprGrammar1 (result header) = true.
Proof.
  destruct header as [[] [] [] ? ? [] [] ? ? [] []]; try discriminate.
  now apply andb_prop in grammar as [_ G].
Qed.

End HeaderResult1.

(** * lexer 3: plainOfShapes (Fmt/SourcePlainProofs.sw) *)
Module PlainOfShapes.

(* Cut down from Syntax.Tok, keeping a kind of each shape. *)
Inductive Tok := Lower | Comma | Arrow | RParen | LParen.
Scheme Equality for Tok.
Inductive PlainShape := ShapeComma | ShapeArrow | ShapeCloser | ShapeOther | ShapeNonItem.

Definition shape (kind : Tok) : PlainShape :=
  match kind with
  | Comma => ShapeComma | LParen => ShapeNonItem | Arrow => ShapeArrow | RParen => ShapeCloser | Lower => ShapeOther
  end.

Definition isCloser (kind : Tok) : bool := match kind with RParen => true | _ => false end.

(* Cut down from Syntax.Token: text and column dropped. *)
Record Token := { kind : Tok; lineStart : bool }.

Definition tokenShapes (toks : list Token) : list PlainShape := map (fun t => shape (kind t)) toks.

Definition isItem (s : PlainShape) : bool := match s with ShapeComma | ShapeNonItem => false | _ => true end.

Definition shapeStep (item : bool) (prev next : PlainShape) : bool :=
  match prev, next with
  | ShapeArrow, (ShapeComma | ShapeCloser | ShapeArrow) => false
  | ShapeComma, ShapeComma => false
  | ShapeComma, ShapeCloser => item
  | _, _ => true
  end.

Fixpoint shapesFrom (item : bool) (prev : PlainShape) (shapes : list PlainShape) : bool :=
  match shapes with
  | [] => true
  | next :: rest => shapeStep item prev next && shapesFrom (isItem prev) next rest
  end.

Definition passableKind (k : Tok) : bool := Tok_beq k Comma || isCloser k.
Definition arrowFollow (k : Tok) : bool := passableKind k || Tok_beq k Arrow.

(* Opaque: whether a token ends an item; the proof uses it only through itemOfShape. *)
Parameter itemKind : Tok -> bool.

Fixpoint sourcePlainFrom (item : bool) (toks : list Token) : bool :=
  match toks with
  | first :: (second :: _) as rest =>
    (negb (Tok_beq (kind first) Arrow) || negb (arrowFollow (kind second)))
      && (negb (Tok_beq (kind first) Comma && lineStart first) || negb (passableKind (kind second))
          || (isCloser (kind second) && item))
      && sourcePlainFrom (itemKind (kind first)) rest
  | _ => true
  end.

Axiom itemOfShape : forall k, isItem (shape k) = itemKind k.
Axiom clauseArrow : forall flag first second, shapeStep flag (shape (kind first)) (shape (kind second)) = true ->
  (negb (Tok_beq (kind first) Arrow) || negb (arrowFollow (kind second))) = true.
Axiom clauseComma : forall flag first second, shapeStep flag (shape (kind first)) (shape (kind second)) = true ->
  (negb (Tok_beq (kind first) Comma && lineStart first) || negb (passableKind (kind second))
    || (isCloser (kind second) && flag)) = true.

(* sample: plainOfShapes *)
Lemma plainOfShapes (flag : bool) (first : Token) (rest : list Token)
  (runs : shapesFrom flag (shape (kind first)) (tokenShapes rest) = true) :
  sourcePlainFrom flag (first :: rest) = true.
Proof.
  revert flag first runs.
  induction rest as [| second more IH]; intros flag first runs; [reflexivity |].
  simpl in runs. apply andb_prop in runs as [ok runs].
  change (sourcePlainFrom flag (first :: second :: more)) with
    ((negb (Tok_beq (kind first) Arrow) || negb (arrowFollow (kind second)))
      && (negb (Tok_beq (kind first) Comma && lineStart first) || negb (passableKind (kind second))
          || (isCloser (kind second) && flag))
      && sourcePlainFrom (itemKind (kind first)) (second :: more)).
  now rewrite (clauseArrow _ _ _ ok), (clauseComma _ _ _ ok), <- itemOfShape, IH.
Qed.

End PlainOfShapes.

(** * tree 1: argumentMinusDeaf (Syntax/DeafProofs.sw) *)
Module ArgumentMinusDeaf.

(* Cut down from Syntax.Tok. *)
Inductive Tok := Lower | Minus | Bang.
Scheme Equality for Tok.
Parameter Comment : Type.

(* Cut down from Syntax.Token (text, column and lineStart dropped), Syntax.Trivia (blankLines dropped) and
   Syntax.Item (afterDot, index, depth and lineIndent dropped). *)
Record Token := { kind : Tok }.
Record Trivia := { leading : list Comment; trailing : option Comment }.
Definition emptyTrivia : Trivia := {| leading := []; trailing := None |}.
Record Leaf := { token : Token; trivia : Trivia }.
Record Item := { leaf : Leaf; glued : bool; afterOperand : bool }.

Definition itemKind (item : Item) : Tok := kind (token (leaf item)).
Definition strippedLeaf (l : Leaf) : Leaf := {| token := token l; trivia := emptyTrivia |}.
Definition stripped (item : Item) : Item :=
  {| leaf := strippedLeaf (leaf item); glued := glued item; afterOperand := afterOperand item |}.

(* Opaque: the proof uses it only through argumentPrefixDeaf. *)
Parameter argumentPrefix : list Item -> bool.

Definition argumentMinus (items : list Item) : bool :=
  match items with sign :: _ => Tok_beq (itemKind sign) Minus && argumentPrefix items | [] => false end.

Axiom argumentPrefixDeaf : forall items, argumentPrefix items = argumentPrefix (map stripped items).

(* sample: argumentMinusDeaf *)
Lemma argumentMinusDeaf (items : list Item) :
  argumentMinus items = argumentMinus (map stripped items).
Proof.
  destruct items as [| a more]; [reflexivity |].
  simpl. now rewrite (argumentPrefixDeaf (a :: more)).
Qed.

End ArgumentMinusDeaf.

(** * tree 2: walkAttributesAlike (Syntax/FollowsDecl.sw) *)
Module WalkAttributesAlike.

Parameter Attributes : Type.
Parameter blankAttributes : Attributes -> Attributes.

(* Cut down from Fmt.Pure: the walk's other six functions dropped. *)
Record Pure := { attributes : Attributes -> Attributes }.
Definition blankPure : Pure := {| attributes := blankAttributes |}.

Fixpoint walkAttributes (on : Pure) (input : list Attributes) : list Attributes :=
  match input with [] => [] | first :: rest => attributes on first :: walkAttributes on rest end.

Definition AttributeGroupAlike (a twin : Attributes) : Prop := blankAttributes a = blankAttributes twin.

(* sample: walkAttributesAlike *)
Lemma walkAttributesAlike (items twins : list Attributes)
  (alike : Forall2 AttributeGroupAlike items twins) :
  walkAttributes blankPure items = walkAttributes blankPure twins.
Proof. induction alike as [| x y xs ys head _ IH]; simpl; congruence. Qed.

End WalkAttributesAlike.
