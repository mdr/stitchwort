(* SW-4222: a cut-down sample of the formatter's slice 1 theorems, in Rocq 9.1 with its Stdlib only.
   Each section names the Stitchwort theorem it ports. Checked with: rocq compile Sample.v *)
From Stdlib Require Import List Bool String Lia PeanoNat Recdef.
Import ListNotations.
Open Scope string_scope.
Open Scope nat_scope.

(** * Definitions (cut down from Syntax/Token.sw, Syntax/Expr.sw, Syntax/Parser.sw) *)

Inductive Tok :=
  | Lower | Upper | Num | Float | Str | LParen | RParen | LBracket | RBracket | Comma | Colon
  | Minus | Bang | Plus | Star | Equals | Arrow | Dot.
Scheme Equality for Tok.

Definition symbolic (k : Tok) : bool :=
  match k with Minus | Bang | Plus | Star | Equals | Arrow | Dot => true | _ => false end.

Definition isCloser (k : Tok) : bool := match k with RParen | RBracket => true | _ => false end.

Record Word := { text : string }.
Record Item := { kind : Tok; word : Word }.

Inductive Expr :=
  | Atom (k : Tok) (w : Word)
  | Paren (opener : Word) (inner : Expr) (closer : Word)
  | Tuple (opener : Word) (items : list Expr) (trailing : bool) (closer : Word)
  | App (head : Expr) (arguments : list Expr)
  | Pref (operator : Word) (operand : Expr).

(* Recursion through [forallb] is accepted as it stands: no mutual [allWithin] is needed. *)
Fixpoint within (e : Expr) : bool :=
  match e with
  | Atom k _ => Tok_beq k Lower || Tok_beq k Num
  | Paren _ inner _ => within inner
  | Tuple _ items _ _ => forallb within items
  | App head arguments => within head && forallb within arguments
  | Pref _ operand => within operand
  end.

Definition atomic (e : Expr) : bool :=
  match e with Atom _ _ | Paren _ _ _ | Tuple _ _ _ _ => true | _ => false end.

Definition level (e : Expr) : nat := match e with App _ _ => 19 | Pref _ _ => 18 | _ => 20 end.

Fixpoint shaped (e : Expr) : bool :=
  match e with
  | Atom _ _ => true
  | Paren _ inner _ => shaped inner
  | Tuple _ items _ _ => (2 <=? List.length items) && forallb shaped items
  | App head arguments =>
    atomic head && shaped head && negb (match arguments with [] => true | _ => false end) && forallb shaped arguments
  | Pref _ operand => shaped operand && (18 <=? level operand)
  end.

Fixpoint lexical (e : Expr) : bool :=
  match e with
  | Atom _ _ => true
  | Paren o inner c => String.eqb (text o) "(" && (String.eqb (text c) ")" && lexical inner)
  | Tuple o items _ c => String.eqb (text o) "(" && (String.eqb (text c) ")" && forallb lexical items)
  | App head arguments => lexical head && forallb lexical arguments
  | Pref _ operand => lexical operand
  end.

Definition Parsed (floor : nat) (e : Expr) : Prop :=
  within e = true -> shaped e = true /\ lexical e = true /\ floor <= level e.

Definition AtomParsed (e : Expr) : Prop :=
  within e = true -> shaped e = true /\ lexical e = true /\ atomic e = true.

Definition lead (e : Expr) : option Word :=
  match e with Atom _ w => Some w | Paren o _ _ => Some o | Tuple o _ _ _ => Some o | _ => None end.

Definition AtomFrom (opener : Word) (e : Expr) : Prop :=
  AtomParsed e /\ (within e = true -> lead e = Some opener).

(** * 1. Dispatchers: signSymbolic, closerNotComma *)

Lemma signSymbolic k : k = Minus \/ k = Bang -> symbolic k = true.
Proof. intros [-> | ->]; reflexivity. Qed.

Lemma closerNotComma k : isCloser k = true -> Tok_beq k Comma = false.
Proof. destruct k; simpl; congruence. Qed.

(** * 2. List helpers: allAppendB, itemsParsed *)

Lemma allAppendB A (xs ys : list A) (p : A -> bool) : forallb p (xs ++ ys) = forallb p xs && forallb p ys.
Proof. apply forallb_app. Qed.

Lemma itemsParsed floor items :
  Forall (Parsed floor) items -> forallb within items = true ->
  forallb shaped items = true /\ forallb lexical items = true.
Proof.
  induction 1 as [| e rest He _ IH]; simpl; [auto |].
  intros W. apply andb_true_iff in W as [W1 W2].
  destruct (He W1) as (S & L & _), (IH W2) as (S' & L'). now rewrite S, L, S', L'.
Qed.

(** * The parser: a state-passing function over the items left, [None] for a failure *)

Definition P (A : Type) := list Item -> option (A * list Item).
Definition ret {A} (x : A) : P A := fun s => Some (x, s).
Definition bind {A B} (p : P A) (j : A -> P B) : P B :=
  fun s => match p s with Some (a, s') => j a s' | None => None end.
Definition fail {A} : P A := fun _ => None.
Notation "'do' x <- p ;; q" := (bind p (fun x => q)) (at level 200, x name, p at level 100, q at level 200).

Definition peek : P (option Tok) := fun s => Some (option_map kind (hd_error s), s).
Definition bump : P Word := fun s => match s with [] => None | item :: rest => Some (word item, rest) end.
Definition at_ (wanted : Tok) : P bool :=
  do seen <- peek ;; ret (match seen with Some k => Tok_beq k wanted | None => false end).
Definition expect (wanted : Tok) : P Word := do found <- at_ wanted ;; if found then bump else fail.
Definition tupleClose : P Word := do annotated <- at_ Colon ;; if annotated then fail else expect RParen.
Definition parenClose (opener : Word) (first : Expr) : P Expr :=
  do closer <- expect RParen ;; ret (Paren opener first closer).
Definition tupleEnd (opener : Word) (pair : list Expr * bool) : P Expr :=
  do closer <- tupleClose ;; ret (Tuple opener (fst pair) (snd pair) closer).

Definition Good (item : Item) : Prop := kind item = RParen -> text (word item) = ")".
Definition GoodItems : list Item -> Prop := Forall Good.

(** * 3. A parser walk: givesTupleClose, givesParenClose, givesTupleEnd *)

Definition Gives {A} (p : P A) (holds : A -> Prop) : Prop :=
  forall s v s', GoodItems s -> p s = Some (v, s') -> holds v /\ GoodItems s'.

Lemma givesRet A (x : A) (holds : A -> Prop) : holds x -> Gives (ret x) holds.
Proof. intros H s v s' G E. inversion E; subst; auto. Qed.

Lemma givesBind A B (p : P A) (j : A -> P B) (first : A -> Prop) (holds : B -> Prop) :
  Gives p first -> (forall v, first v -> Gives (j v) holds) -> Gives (bind p j) holds.
Proof.
  intros Hp Hj s v s' G E. unfold bind in E. destruct (p s) as [[a s1] |] eqn:R; [| discriminate].
  destruct (Hp _ _ _ G R) as [F G1]. eapply Hj; eauto.
Qed.

Lemma givesFail A (holds : A -> Prop) : Gives fail holds.
Proof. intros s v s' _ E; discriminate. Qed.

Lemma givesWeaken A (p : P A) (holds weaker : A -> Prop) :
  Gives p holds -> (forall v, holds v -> weaker v) -> Gives p weaker.
Proof. intros Hp Imp s v s' G E. destruct (Hp _ _ _ G E); auto. Qed.

Lemma givesPeek : Gives peek (fun _ => True).
Proof. intros s v s' G E. inversion E; subst; auto. Qed.

Lemma givesBump : Gives bump (fun _ => True).
Proof. intros [| i r] v s' G E; inversion E; subst. inversion G; auto. Qed.

Lemma givesAt k : Gives (at_ k) (fun _ => True).
Proof. eapply givesBind; [apply givesPeek | intros; now apply givesRet]. Qed.

Lemma givesExpect : Gives (expect RParen) (fun w => text w = ")").
Proof.
  intros [| i r] v s' G E; cbv [expect at_ bind peek ret bump fail] in E; simpl in E; [discriminate |].
  destruct (Tok_beq (kind i) RParen) eqn:K; [| discriminate].
  inversion E; subst. inversion G as [| ? ? Gi Gr]; subst. split; [| exact Gr].
  apply Gi. now apply internal_Tok_dec_bl.
Qed.

(* The walk: sequencing, a finished value, a failure, a branch; callees from the hint database. *)
Create HintDb gives.
#[local] Hint Resolve givesPeek givesBump givesAt givesExpect givesFail : gives.
Ltac walk :=
  repeat first
    [ solve [eauto with gives]
    | apply givesRet
    | match goal with |- Gives (if ?b then _ else _) _ => destruct b end
    | eapply givesBind; [solve [eauto with gives] | intros ] ].

Lemma givesTupleClose : Gives tupleClose (fun w => text w = ")").
Proof. unfold tupleClose. walk. Qed.
#[local] Hint Resolve givesTupleClose : gives.

Lemma parenParsed o c inner : text o = "(" -> text c = ")" -> Parsed 1 inner -> AtomParsed (Paren o inner c).
Proof. intros Ho Hc Hp W. simpl in *. destruct (Hp W) as (S & L & _). now rewrite Ho, Hc, S, L. Qed.

Lemma tupleParsed o c items trailing :
  text o = "(" -> text c = ")" -> 2 <= List.length items -> Forall (Parsed 1) items ->
  AtomParsed (Tuple o items trailing c).
Proof.
  intros Ho Hc Hl Hp W. cbn [within] in W. destruct (itemsParsed _ _ Hp W) as [S L].
  apply Nat.leb_le in Hl. cbn [shaped lexical atomic]. now rewrite Ho, Hc, S, L, Hl.
Qed.

Lemma givesParenClose o first : text o = "(" -> Parsed 1 first -> Gives (parenClose o first) (AtomFrom o).
Proof. intros Ho Hp. unfold parenClose. walk. split; [now apply parenParsed | reflexivity]. Qed.

Lemma givesTupleEnd o items trailing :
  text o = "(" -> 2 <= List.length items -> Forall (Parsed 1) items ->
  Gives (tupleEnd o (items, trailing)) (AtomFrom o).
Proof. intros Ho Hl Hp. unfold tupleEnd. walk. split; [now apply tupleParsed | reflexivity]. Qed.

(** * 4. A longer walk: givesCommaListFrom, a loop with fuel *)

Fixpoint commaListFrom {A} (ends : nat -> P bool) (next : P A) (fuel count : nat) (current : A) (found : list A) :
    P (list A * bool) :=
  match fuel with
  | 0 => ret (rev (current :: found), false)
  | S more =>
    do seen <- peek ;;
    match seen with
    | Some k =>
      if Tok_beq k Comma then
        do _ <- bump ;;
        do stop <- ends count ;;
        if stop then ret (rev (current :: found), true)
        else do value <- next ;; commaListFrom ends next more (count + 1) value (current :: found)
      else ret (rev (current :: found), false)
    | None => ret (rev (current :: found), false)
    end
  end.

Lemma givesCommaListFrom A (ends : nat -> P bool) (next : P A) (holds : A -> Prop) :
  (forall count, Gives (ends count) (fun _ => True)) -> Gives next holds ->
  forall fuel count current found, holds current -> Forall holds found ->
  Gives (commaListFrom ends next fuel count current found)
    (fun pair => Forall holds (fst pair) /\ List.length found + 1 <= List.length (fst pair)).
Proof.
  intros He Hn.
  assert (End : forall current found flag, holds current -> Forall holds found ->
    Gives (ret (rev (current :: found), flag))
      (fun pair : list A * bool => Forall holds (fst pair) /\ List.length found + 1 <= List.length (fst pair))).
  { intros c f flag Hc Hf. apply givesRet. split.
    - apply Forall_rev. now constructor.
    - cbn [fst]. rewrite length_rev. simpl. lia. }
  induction fuel as [| more IH]; intros count current found Hc Hf; cbn [commaListFrom]; [now apply End |].
  eapply givesBind; [apply givesPeek |]. intros [k |] _; [| now apply End].
  destruct (Tok_beq k Comma); [| now apply End].
  eapply givesBind; [apply givesBump |]. intros _ _.
  eapply givesBind; [apply He |]. intros [] _; [now apply End |].
  eapply givesBind; [apply Hn |]. intros value Hv.
  eapply givesWeaken; [apply IH; [exact Hv | now constructor] |].
  cbn [List.length]. intros pair [H1 H2]. split; [exact H1 | lia].
Qed.

(** * 5. Two runs: followsExpect, followsParenClose *)

Definition SameCode (a b : Item) : Prop := kind a = kind b.
Definition WordsAlike (_ _ : Word) : Prop := True.

Inductive ExprsAlike : Expr -> Expr -> Prop :=
  | AlikeAtom k w w' : ExprsAlike (Atom k w) (Atom k w')
  | AlikeParen o o' i i' c c' : ExprsAlike i i' -> ExprsAlike (Paren o i c) (Paren o' i' c')
  | AlikeTuple o o' xs ys t c c' : Forall2 ExprsAlike xs ys -> ExprsAlike (Tuple o xs t c) (Tuple o' ys t c')
  | AlikeApp h h' xs ys : ExprsAlike h h' -> Forall2 ExprsAlike xs ys -> ExprsAlike (App h xs) (App h' ys)
  | AlikePref o o' e e' : ExprsAlike e e' -> ExprsAlike (Pref o e) (Pref o' e').

Definition Follows {A B} (alike : A -> B -> Prop) (first : P A) (second : P B) : Prop :=
  forall s t v s', Forall2 SameCode s t -> first s = Some (v, s') ->
    exists w t', second t = Some (w, t') /\ Forall2 SameCode s' t' /\ alike v w.

Lemma followsRet A B (alike : A -> B -> Prop) x y : alike x y -> Follows alike (ret x) (ret y).
Proof. intros H s t v s' S E. inversion E; subst. now exists y, t. Qed.

Lemma followsBind A B C D (mid : A -> B -> Prop) (alike : C -> D -> Prop) (p : P A) (q : P B) j k :
  Follows mid p q -> (forall v w, mid v w -> Follows alike (j v) (k w)) -> Follows alike (bind p j) (bind q k).
Proof.
  intros Hp Hj s t v s' S E. unfold bind in *. destruct (p s) as [[a s1] |] eqn:R; [| discriminate].
  destruct (Hp _ _ _ _ S R) as (w & t1 & Q & S1 & M). rewrite Q. eapply Hj; eauto.
Qed.

Lemma followsFail A B (alike : A -> B -> Prop) (second : P B) : Follows alike fail second.
Proof. intros s t v s' _ E; discriminate. Qed.

Lemma followsPeek : Follows eq peek peek.
Proof.
  intros s t v s' S E. inversion E; subst. exists (option_map kind (hd_error t)), t. repeat split; [exact S |].
  destruct S as [| a b ? ? K]; simpl; [reflexivity | unfold SameCode in K; now rewrite K].
Qed.

Lemma followsBump : Follows WordsAlike bump bump.
Proof.
  intros s t v s' S E. destruct S as [| a b s1 t1 K S1]; simpl in *; [discriminate |].
  inversion E; subst. exists (word b), t1. now repeat split.
Qed.

Lemma followsExpect wanted : Follows WordsAlike (expect wanted) (expect wanted).
Proof.
  unfold expect, at_. eapply followsBind with (mid := eq).
  - eapply followsBind; [apply followsPeek |]. intros v w ->. now apply followsRet.
  - intros found ? <-. destruct found; [apply followsBump | apply followsFail].
Qed.

Lemma followsParenClose opener openerTwin first firstTwin :
  ExprsAlike first firstTwin -> Follows ExprsAlike (parenClose opener first) (parenClose openerTwin firstTwin).
Proof.
  intros F. unfold parenClose. eapply followsBind; [apply (followsExpect RParen) |].
  intros c c' _. apply followsRet. now constructor.
Qed.

(** * 6. Rule N: allTokensWithout *)

Record Token := { tkind : Tok; ttext : string; lineStart : bool }.
Record Leaf := { token : Token; comments : list string }.

Definition hasItem (behind : list Leaf) : bool :=
  match behind with [] => false | leaf :: _ => negb (Tok_beq (tkind (token leaf)) Comma) end.

Definition startingLine (t : Token) (start : bool) : Token :=
  {| tkind := tkind t; ttext := ttext t; lineStart := start |}.

Definition commaDeleted (comma closer : Leaf) (behind : list Leaf) : Leaf * list Leaf :=
  ({| token := startingLine (token closer) (lineStart (token comma) || lineStart (token closer));
      comments := comments closer |},
   match behind with
   | [] => []
   | previous :: earlier => {| token := token previous; comments := comments previous ++ comments comma |} :: earlier
   end).

(* Not structural (the second call keeps [closer]), so by a measure; [Function] also gives the induction. *)
Function withoutR (behind rest : list Leaf) {measure List.length rest} : list Leaf :=
  match rest with
  | [] => behind
  | [leaf] => leaf :: behind
  | comma :: closer :: after =>
    if Tok_beq (tkind (token comma)) Comma && isCloser (tkind (token closer)) && hasItem behind then
      withoutR (fst (commaDeleted comma closer behind) :: snd (commaDeleted comma closer behind)) after
    else withoutR (comma :: behind) (closer :: after)
  end.
Proof. all: intros; simpl; lia. Defined.

Definition tokens (leaves : list Leaf) : list Token := map token leaves.

Lemma allTokensWithout (q : Token -> bool) :
  (forall t start, q (startingLine t start) = q t) ->
  forall behind rest, forallb q (tokens behind) = true -> forallb q (tokens rest) = true ->
  forallb q (tokens (withoutR behind rest)) = true.
Proof.
  intros blind behind rest. functional induction (withoutR behind rest); simpl; intros K C.
  - exact K.
  - now rewrite K, andb_true_r in *.
  - apply andb_true_iff in C as [_ C]. apply andb_true_iff in C as [Cc Ca].
    apply IHl; [| exact Ca]. simpl. rewrite blind, Cc. destruct behind; simpl in *; auto.
  - apply andb_true_iff in C as [Cc Ca]. apply IHl; [simpl; now rewrite Cc | exact Ca].
Qed.

(** * 7. The printer: endedWeaker, joinsWeaker, passesCons, joinsAllAppend, passesAppend *)

Inductive Edge := Plain (touching : option string) | Waiting (touching : option string).

Inductive Doc :=
  | Nothing | Line | HardLine
  | Chunk (text : string)
  | Nest (indent : nat) (inner : Doc)
  | Group (inner : Doc)
  | IfBroken (broken flat : Doc)
  | Concat (docs : list Doc).

Definition PutOk (follows : string -> string -> Prop) (touching : option string) (text : string) : Prop :=
  match touching with Some w => follows w text | None => True end.

Definition WriteJoins (follows : string -> string -> Prop) (edge : Edge) (text : string) (next : Edge -> Prop) : Prop :=
  if String.eqb text "" then next edge
  else match edge with
       | Plain touching => PutOk follows touching text /\ next (Plain (Some text))
       | Waiting _ => next (Plain (Some text))
       end.

Definition SepJoins (follows : string -> string -> Prop) (edge : Edge) (next : Edge -> Prop) : Prop :=
  match edge with
  | Plain touching => PutOk follows touching " " /\ next (Plain None)
  | Waiting touching => next (Waiting touching) /\ next (Plain None)
  end.

Section Joins.
  Variable follows : string -> string -> Prop.

  (* The list case is a local [fix]: Rocq has no mutual recursion between a nested type and its lists. *)
  Fixpoint Joins (doc : Doc) : Edge -> (Edge -> Prop) -> Prop :=
    match doc with
    | Nothing => fun edge next => next edge
    | Chunk text => fun edge next => WriteJoins follows edge text next
    | Line => fun edge next => SepJoins follows edge next
    | HardLine => fun _ next => next (Plain None)
    | Nest _ inner => Joins inner
    | Group inner => Joins inner
    | IfBroken broken flat => fun edge next => Joins broken edge next /\ Joins flat edge next
    | Concat docs =>
      (fix all (docs : list Doc) : Edge -> (Edge -> Prop) -> Prop :=
         match docs with
         | [] => fun edge next => next edge
         | doc :: rest => fun edge next => Joins doc edge (fun after => all rest after next)
         end) docs
    end.

  Fixpoint JoinsAll (docs : list Doc) : Edge -> (Edge -> Prop) -> Prop :=
    match docs with
    | [] => fun edge next => next edge
    | doc :: rest => fun edge next => Joins doc edge (fun after => JoinsAll rest after next)
    end.

  Lemma joinsConcat docs edge next : Joins (Concat docs) edge next = JoinsAll docs edge next.
  Proof. reflexivity. Qed.

  (* The generated [Doc_ind] has no hypothesis for the documents inside [Concat], so the proof is its own fixpoint
     with an inner induction over the list. *)
  Fixpoint joinsWeaker (doc : Doc) : forall edge (strong weak : Edge -> Prop),
      (forall e, strong e -> weak e) -> Joins doc edge strong -> Joins doc edge weak.
  Proof.
    destruct doc; intros edge strong weak Imp J; try (rewrite joinsConcat in *); cbn [Joins] in *.
    - auto.
    - destruct edge; unfold SepJoins in *; intuition.
    - auto.
    - unfold WriteJoins in *. destruct (text0 =? "")%string; [auto |]. destruct edge; intuition.
    - eapply joinsWeaker; eauto.
    - eapply joinsWeaker; eauto.
    - destruct J; split; eapply joinsWeaker; eauto.
    - revert edge J. induction docs as [| doc rest IH]; simpl; intros edge J; [auto |].
      eapply joinsWeaker; [| exact J]. intros e. apply IH.
  Qed.

  Lemma joinsAllWeaker docs edge (strong weak : Edge -> Prop) :
    (forall e, strong e -> weak e) -> JoinsAll docs edge strong -> JoinsAll docs edge weak.
  Proof. intros Imp J. rewrite <- joinsConcat in *. eapply joinsWeaker; eauto. Qed.

  Definition Token' (w : string) : Prop := w <> "".

  Definition Ended (trails : bool) (edge : Edge) : Prop :=
    match edge with
    | Plain None => True
    | Plain (Some w) => Token' w
    | Waiting None => trails = true
    | Waiting (Some w) => trails = true /\ Token' w
    end.

  Lemma endedWeaker trails trails' edge : (trails = true -> trails' = true) -> Ended trails edge -> Ended trails' edge.
  Proof. destruct edge as [[w |] | [w |]]; simpl; intuition. Qed.

  Definition Passes (doc : Doc) (pre post : Edge -> Prop) : Prop :=
    forall edge next, pre edge -> (forall after, post after -> next after) -> Joins doc edge next.

  Definition PassesAll (docs : list Doc) (pre post : Edge -> Prop) : Prop :=
    forall edge next, pre edge -> (forall after, post after -> next after) -> JoinsAll docs edge next.

  Lemma passesCons doc docs pre middle post :
    Passes doc pre middle -> PassesAll docs middle post -> PassesAll (doc :: docs) pre post.
  Proof. intros First Rest edge next Holds After. simpl. apply (First edge); auto. Qed.

  Lemma joinsAllAppend front back edge next :
    JoinsAll front edge (fun between => JoinsAll back between next) -> JoinsAll (front ++ back) edge next.
  Proof.
    revert edge. induction front as [| doc rest IH]; simpl; intros edge J; [exact J |].
    eapply joinsWeaker; [| exact J]. intros e. apply IH.
  Qed.

  Lemma passesAppend front back pre middle post :
    PassesAll front pre middle -> PassesAll back middle post -> PassesAll (front ++ back) pre post.
  Proof. intros First Second edge next Holds After. apply joinsAllAppend. apply (First edge); auto. Qed.
End Joins.
