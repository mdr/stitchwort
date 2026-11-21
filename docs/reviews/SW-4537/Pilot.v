(* SW-4537 pilot: three drawn slice 1 theorems in Rocq 9.1 with its Stdlib only.
   Counted lemmas follow a "sample:" comment; everything else is uncounted support
   (cut-down definitions, and lemmas the Stitchwort proof names, as axioms).
   Check: rocq compile -R <stdlib>/lib/coq/9.1/user-contrib/Stdlib Stdlib Pilot.v *)
From Stdlib Require Import List Bool String Lia PeanoNat.
Import ListNotations.
Open Scope nat_scope.

(** * walk 1: readsAtAtValue (Syntax/ParseCarriesDecl.sw) *)
Module Walk.

(* Cut down from std's Parse.Mark: left dropped. *)
Record Mark (t : Type) := { rest : list t; offset : nat }.
Arguments rest {t}. Arguments offset {t}.

(* The Parse ability as a state monad over the mark, failing with a message. *)
Definition P (t A : Type) := Mark t -> string + A * Mark t.
Definition ret {t A} (x : A) : P t A := fun s => inr (x, s).
Definition bind {t A B} (p : P t A) (j : A -> P t B) : P t B :=
  fun s => match p s with inl e => inl e | inr (x, s') => j x s' end.
Notation "'do' x <- p ;; q" := (bind p (fun x => q)) (at level 200, x name, right associativity).

(* Cut down from std's Parse.ReadsAt: the Honest bookkeeping about offsets is dropped. *)
Definition ReadsAt {t A} (start : Mark t) (p : P t A) (spec : list t -> A -> Prop) : Prop :=
  forall value after, p start = inr (value, after) -> exists read, rest start = read ++ rest after /\ spec read value.

Inductive Tok := Lower | Comma | RParen.
Scheme Equality for Tok.
Record Item := { kind : Tok }.
Record Modes := { stops : Item -> bool }.

Definition left {t} : P t (list t) := fun s => inr (rest s, s).

Fixpoint peekIn (modes : Modes) (ahead : nat) (items : list Item) : option Tok :=
  match ahead, items with
  | _, [] => None
  | 0, item :: _ => if stops modes item then None else Some (kind item)
  | S more, item :: later => if stops modes item then None else peekIn modes more later
  end.

Definition isSome (wanted : Tok) (seen : option Tok) : bool :=
  match seen with Some found => Tok_beq found wanted | None => false end.

Definition peek (modes : Modes) : P Item (option Tok) := do items <- left ;; ret (peekIn modes 0 items).
Definition at_ (modes : Modes) (wanted : Tok) : P Item bool := do seen <- peek modes ;; ret (isSome wanted seen).

(* sample: readsAtAtValue *)
Lemma readsAtAtValue (start : Mark Item) (modes : Modes) (wanted : Tok) :
  ReadsAt start (at_ modes wanted) (fun read found =>
    read = [] /\ found = isSome wanted (peekIn modes 0 (rest start))).
Proof. intros value after ran. inversion ran; subst. now exists []. Qed.

End Walk.

(** * lexer 1: itemsShapesOfKinds1 (Fmt/SourcePlainProofs.sw) *)
Module Lexer.

Inductive Tok := Lower | Comma | Arrow | RParen | Space.
Scheme Equality for Tok.
Inductive PlainShape := ShapeComma | ShapeArrow | ShapeCloser | ShapeOther | ShapeNonItem.

Definition shape (kind : Tok) : PlainShape :=
  if Tok_beq kind Comma then ShapeComma
  else if Tok_beq kind Space then ShapeNonItem
  else if Tok_beq kind Arrow then ShapeArrow
  else if Tok_beq kind RParen then ShapeCloser
  else ShapeOther.

(* Expr and its three functions are mutual with the list functions below in Stitchwort; the drawn theorem
   only uses them through shapesOfKinds1, so they are opaque here (which keeps that axiom harmless). *)
Parameter Expr : Type.
Parameter kinds : Expr -> list Tok.
Parameter shapes : Expr -> list PlainShape.
Parameter grammar1 : Expr -> bool.

Fixpoint restKinds (close : Tok) (trailing : bool) (items : list Expr) : list Tok :=
  match items with
  | [] => if trailing then [Comma; close] else [close]
  | next :: rest => Comma :: kinds next ++ restKinds close trailing rest
  end.

Definition itemsKinds (close : Tok) (trailing : bool) (items : list Expr) : list Tok :=
  match items with
  | [] => [close]
  | first :: rest => kinds first ++ restKinds close trailing rest
  end.

Fixpoint restShapes (trailing : bool) (items : list Expr) : list PlainShape :=
  match items with
  | [] => if trailing then [ShapeComma; ShapeCloser] else [ShapeCloser]
  | next :: rest => ShapeComma :: shapes next ++ restShapes trailing rest
  end.

Definition itemsShapes (trailing : bool) (items : list Expr) : list PlainShape :=
  match items with
  | [] => [ShapeCloser]
  | first :: rest => shapes first ++ restShapes trailing rest
  end.

Fixpoint allGrammar1 (items : list Expr) : bool :=
  match items with
  | [] => true
  | expr :: rest => grammar1 expr && allGrammar1 rest
  end.

Axiom shapesOfKinds1 : forall expr, grammar1 expr = true -> shapes expr = map shape (kinds expr).

Axiom restShapesOfKinds1 : forall close, shape close = ShapeCloser -> forall trailing items,
  allGrammar1 items = true -> restShapes trailing items = map shape (restKinds close trailing items).

(* sample: itemsShapesOfKinds1 *)
Lemma itemsShapesOfKinds1 (close : Tok) (closer : shape close = ShapeCloser) (trailing : bool) (items : list Expr)
  (grammar : allGrammar1 items = true) :
  itemsShapes trailing items = map shape (itemsKinds close trailing items).
Proof.
  destruct items as [| first rest]; simpl in *; [now rewrite closer |].
  apply andb_prop in grammar as [G R].
  now rewrite map_app, shapesOfKinds1, (restShapesOfKinds1 close).
Qed.

End Lexer.

(** * printer 1: closerFitsOf (Fmt/BracketHangProofs.sw) *)
Module Printer.

Record OpenMark := { key : nat; marked : nat; least : option nat }.

(* Cut down from std's Doc.Carry: floor dropped. *)
Record Carry := { marks : list OpenMark }.

Definition closerAt (carry : Carry) (k indent : nat) : nat :=
  match find (fun mark => key mark =? k) (marks carry) with
  | Some {| marked := m; least := Some l |} => if l <=? indent then Nat.min m indent else indent
  | _ => indent
  end.

Definition leftOf (column : nat) (block : option nat) : bool :=
  match block with Some b => column <? b | None => true end.

Definition CloserFits (k indent : nat) (block : option nat) (outside : nat) (carry : Carry) : Prop :=
  leftOf (closerAt carry k indent) block = true /\ outside <= closerAt carry k indent.

(* sample: closerFitsOf *)
Lemma closerFitsOf (k indent : nat) (block : option nat) (outside m : nat) (carry : Carry) (mark : OpenMark)
  (found : find (fun found => key found =? k) (marks carry) = Some mark)
  (line : marked mark = m)
  (atOpener : outside <= m)
  (clear : outside <= indent)
  (shallow : leftOf indent block = true) :
  CloserFits k indent block outside carry.
Proof.
  unfold CloserFits, closerAt. rewrite found. destruct mark as [? ? [l |]]; simpl in *; [| auto].
  destruct (l <=? indent), block; simpl in *; rewrite ?Nat.ltb_lt in *; split; auto; lia.
Qed.

End Printer.
