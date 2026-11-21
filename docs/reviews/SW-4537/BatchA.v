(* SW-4538, SW-4537 batch A: the parser strata (walk 2, two-run 1 and 2, readback 1 to 4) in Rocq 9.1
   with its Stdlib only. Counted lemmas follow a "sample:" comment; everything else is uncounted
   support: the shared parser prelude (std's Parse in Stitchwort), cut-down definitions, and lemmas
   the Stitchwort proof names, as axioms.
   Check: rocq compile -R <stdlib>/lib/coq/9.1/user-contrib/Stdlib Stdlib BatchA.v *)
From Stdlib Require Import List Bool String Lia PeanoNat.
Import ListNotations.
Open Scope nat_scope.

(** * The shared parser prelude (SW-4537 rule 9)

    Std's Parse ability as a state monad over the mark that fails with a message. Cut down from
    std: the state is the mark alone (furthest, expected and messages only shape error reports);
    the mark's left and the Honest bookkeeping are dropped, which slice 1's proofs only pass along
    (where a parser reads left, it reads the length of rest, which Honest makes equal). *)
Module Parse.

Record Mark (t : Type) := { rest : list t; offset : nat }.
Arguments rest {t}. Arguments offset {t}.

Definition P (t A : Type) := Mark t -> string + A * Mark t.
Definition ret {t A} (x : A) : P t A := fun s => inr (x, s).
Definition bind {t A B} (p : P t A) (j : A -> P t B) : P t B :=
  fun s => match p s with inl e => inl e | inr (x, s') => j x s' end.
Notation "'do' x <- p ;; q" := (bind p (fun x => q)) (at level 200, x name, right associativity).

Definition mark {t} : P t (Mark t) := fun s => inr (s, s).
Definition left {t} : P t (list t) := fun s => inr (rest s, s).
Definition fatal {t A} (message : string) : P t A := fun _ => inl message.

(* Std's Parse.Invariant: a property of the input left that reading keeps. *)
Record Invariant (t : Type) := {
  holds : list t -> Prop;
  kept : forall read rest, holds (read ++ rest) -> holds rest }.
Arguments holds {t}.

Definition ReadsAt {t A} (start : Mark t) (p : P t A) (spec : list t -> A -> Prop) : Prop :=
  forall value after, p start = inr (value, after) -> exists read, rest start = read ++ rest after /\ spec read value.

Definition ReadsIn {t A} (inv : Invariant t) (p : P t A) (spec : list t -> A -> Prop) : Prop :=
  forall start, holds inv (rest start) -> ReadsAt start p spec.

(* Std's List.All2 is Stdlib's Forall2. *)
Definition Alike {t u} (same : t -> u -> Prop) (first : Mark t) (second : Mark u) : Prop :=
  Forall2 same (rest first) (rest second) /\ offset first = offset second.

Definition Follows {t u A B} (same : t -> u -> Prop) (alike : A -> B -> Prop) (first : P t A) (second : P u B) :=
  forall start other value after, Alike same start other -> first start = inr (value, after) ->
    exists twin afterTwin, second other = inr (twin, afterTwin) /\ Alike same after afterTwin /\ alike value twin.

(* Std's Parse.RunsFrom on the cut-down state: from state on read ++ rest, p succeeds with value,
   stops with rest left, and the offset moved on by read. *)
Definition RunsFrom {t A} (state : Mark t) (p : P t A) (read rst : list t) (value : A) : Prop :=
  rest state = read ++ rst ->
    exists after, p state = inr (value, after) /\ rest after = rst /\ offset after = offset state + List.length read.

Definition Runs {t A} (p : P t A) (read rst : list t) (value : A) : Prop :=
  forall state, RunsFrom state p read rst value.

(* Std's Parse.followsDone. *)
Lemma followsPure {t u A B} (same : t -> u -> Prop) (alike : A -> B -> Prop) x y :
  alike x y -> Follows same alike (ret x) (ret y).
Proof. intros holds start other value after a ran. inversion ran; subst. now exists y, other. Qed.

(* Std's Parse.followsThen. *)
Lemma followsBind {t u A B C D} (same : t -> u -> Prop) (mid : A -> B -> Prop) (alike : C -> D -> Prop)
  (p : P t A) (q : P u B) (j : A -> P t C) (k : B -> P u D) :
  Follows same mid p q -> (forall v w, mid v w -> Follows same alike (j v) (k w)) ->
  Follows same alike (bind p j) (bind q k).
Proof.
  intros first later start other value after a ran. unfold bind in *.
  destruct (p start) as [| [v s']] eqn:run; [discriminate |].
  destruct (first _ _ _ _ a run) as (w & o' & -> & a' & m).
  exact (later _ _ m _ _ _ _ a' ran).
Qed.

(* Std's Parse.followsLeft, for any relation on items. *)
Lemma followsLeft {t u} (same : t -> u -> Prop) : Follows same (Forall2 same) left left.
Proof. intros start other value after a ran. inversion ran; subst. exists (rest other), other. exact (conj eq_refl (conj a (proj1 a))). Qed.

End Parse.
Import Parse.

(** * walk 2: readsBlockResult (Syntax/ParseCarriesLadder.sw) *)
Module Walk2.

Parameter Item Tok Word Let Attributes Header DefBody : Type.

(* Cut down from Syntax/Expr.sw: of Expr's constructors only Atom and Block are kept; the proof
   reaches no other. *)
Inductive Expr :=
  | Atom (kind : Tok) (word : Word)
  | Block (first : Statement) (rest : list Statement) (value : Expr)
with Statement :=
  | LetStatement (binding : Let)
  | LocalDef (attributes : list Attributes) (header : Header) (body : DefBody)
  | ExprStatement (value : Expr).

Parameter wordWithin1 : Tok -> bool.

(* Cut down from Expr.grammar1: a block is outside slice 1's grammar. *)
Definition grammar1 (expr : Expr) : bool :=
  match expr with Atom kind _ => wordWithin1 kind | Block _ _ _ => false end.

Definition Out (expr : Expr) : Prop := grammar1 expr = false.

Parameter GoodItems : Invariant Item.
Parameter KeptFull : list Item -> Expr -> Prop.
Axiom keptFullOut : forall read expr, Out expr -> KeptFull read expr.

Definition StatementKept (read : list Item) (statement : Statement) : Prop :=
  match statement with ExprStatement value => KeptFull read value | _ => True end.

Definition BlockRead (found : list Statement) (read : list Item) (result : list Statement) : Prop :=
  (read = [] /\ result = found)
    \/ (exists line, result = line :: found /\ StatementKept read line)
    \/ List.length found + 2 <= List.length result.

Definition blockResult (statements : list Statement) : P Item Expr :=
  match statements with
  | [ExprStatement value] => ret value
  | ExprStatement value :: last :: earlier =>
    match rev (last :: earlier) with
    | first :: rest => ret (Block first rest value)
    | [] => ret value
    end
  | LetStatement _ :: _ => fatal "a block must end with an expression, not `let`"
  | LocalDef _ _ _ :: _ => fatal "a block must end with an expression, not a local `def` or `theorem`"
  | [] => fatal "the parser read no line of a block"
  end.

(* sample: readsBlockResult *)
Lemma readsBlockResult (statements : list Statement) (read : list Item) (got : BlockRead [] read statements) :
  ReadsIn GoodItems (blockResult statements) (fun more tree => KeptFull (read ++ more) tree).
Proof.
  intros start _ value after ran.
  destruct statements as [| [| | v] [| last earlier]]; try discriminate.
  - inversion ran; subst. exists []. rewrite app_nil_r. split; [reflexivity |].
    destruct got as [[_ H] | [[line [H kept]] | H]]; [discriminate | | simpl in H; lia].
    injection H as <-. exact kept.
  - simpl in ran. destruct (rev earlier ++ [last]) as [| first rest] eqn:R.
    + now destruct (app_cons_not_nil (rev earlier) [] last).
    + inversion ran; subst. exists []. split; [reflexivity |]. now apply keptFullOut.
Qed.

End Walk2.

(** * two-run 1: followsParenAtom (Syntax/FollowsBase.sw) *)
Module TwoRun1.

Parameter Item Tok Expr Goal Modes : Type.
Parameter stripped : Item -> Item.

Definition SameCode (first second : Item) : Prop := stripped first = stripped second.

(* ExprsAlike compares the two trees with their words blanked (walk blankPure). *)
Parameter ExprsAlike : Expr -> Expr -> Prop.

Definition SelfFollows (self selfTwin : Goal -> P Item Expr) : Prop :=
  forall goal, Follows SameCode ExprsAlike (self goal) (selfTwin goal).

Parameter peekAt : Modes -> nat -> P Item (option Tok).
Parameter namedArgument : (Goal -> P Item Expr) -> Modes -> Tok -> string -> P Item Expr.
Parameter operatorSection : (Goal -> P Item Expr) -> Modes -> P Item Expr.
Parameter rightSection : (Goal -> P Item Expr) -> Modes -> nat -> P Item Expr.
Parameter parenOther : (Goal -> P Item Expr) -> Modes -> option Tok -> option Tok -> P Item Expr.
Parameter parenRest : (Goal -> P Item Expr) -> Modes -> list Item -> P Item Expr.
Parameter parenOutside : option Tok -> option Tok -> bool.

Definition parenOn self modes (second third : option Tok) : P Item Expr :=
  if parenOutside second third then parenOther self modes second third
  else do items <- left ;; parenRest self modes items.
Definition parenSecond self modes (second : option Tok) : P Item Expr :=
  do third <- peekAt modes 2 ;; parenOn self modes second third.
Definition parenAtom self modes : P Item Expr := do second <- peekAt modes 1 ;; parenSecond self modes second.

Axiom followsPeekAt : forall modes ahead, Follows SameCode eq (peekAt modes ahead) (peekAt modes ahead).

Axiom followsParenOther : forall self selfTwin modes,
  (forall closer closeText, Follows SameCode ExprsAlike
    (namedArgument self modes closer closeText) (namedArgument selfTwin modes closer closeText)) ->
  Follows SameCode ExprsAlike (operatorSection self modes) (operatorSection selfTwin modes) ->
  forall second third,
  Follows SameCode ExprsAlike (parenOther self modes second third) (parenOther selfTwin modes second third).

Axiom followsParenRest : forall self selfTwin, SelfFollows self selfTwin -> forall modes,
  (forall inside, Follows SameCode ExprsAlike (rightSection self modes inside) (rightSection selfTwin modes inside)) ->
  forall items others, Forall2 SameCode items others ->
  Follows SameCode ExprsAlike (parenRest self modes items) (parenRest selfTwin modes others).

(* sample: followsParenAtom *)
Lemma followsParenAtom self selfTwin (knot : SelfFollows self selfTwin) (modes : Modes)
  (namedArguments : forall closer closeText, Follows SameCode ExprsAlike
    (namedArgument self modes closer closeText) (namedArgument selfTwin modes closer closeText))
  (operatorSections : Follows SameCode ExprsAlike (operatorSection self modes) (operatorSection selfTwin modes))
  (rightSections : forall inside,
    Follows SameCode ExprsAlike (rightSection self modes inside) (rightSection selfTwin modes inside)) :
  Follows SameCode ExprsAlike (parenAtom self modes) (parenAtom selfTwin modes).
Proof.
  apply followsBind with (mid := eq); [apply followsPeekAt | intros second ? <-].
  apply followsBind with (mid := eq); [apply followsPeekAt | intros third ? <-].
  unfold parenOn. destruct (parenOutside second third); [now apply followsParenOther |].
  apply followsBind with (mid := Forall2 SameCode); [apply followsLeft | now apply followsParenRest].
Qed.

End TwoRun1.

(** * two-run 2: followsListPatternStep (Syntax/FollowsFormsPatterns.sw) *)
Module TwoRun2.

Parameter Item Word Pattern PatternGoal Modes : Type.
Parameter stripped : Item -> Item.

(* Cut down from Syntax/Token.sw: the one kind the proof names. *)
Inductive Tok := DotDot.

Definition SameCode (first second : Item) : Prop := stripped first = stripped second.

(* PatternsAlike and WordsAlike compare with words blanked. *)
Parameter PatternsAlike : Pattern -> Pattern -> Prop.
Parameter WordsAlike : Word -> Word -> Prop.

Definition PairAlike {A B C D} (first : A -> B -> Prop) (second : C -> D -> Prop) (x : A * C) (y : B * D) :=
  first (fst x) (fst y) /\ second (snd x) (snd y).

Definition OptionAlike {A B} (alike : A -> B -> Prop) (x : option A) (y : option B) : Prop :=
  match x, y with None, None => True | Some a, Some b => alike a b | _, _ => False end.

Definition Read := (list Pattern * (bool * option (Word * Pattern)))%type.

Definition ListRead : Read -> Read -> Prop :=
  PairAlike (Forall2 PatternsAlike) (PairAlike eq (OptionAlike (PairAlike WordsAlike PatternsAlike))).

Definition PatternSelfFollows (pself pselfTwin : PatternGoal -> P Item Pattern) : Prop :=
  forall goal, Follows SameCode PatternsAlike (pself goal) (pselfTwin goal).

Parameter at_ : Modes -> Tok -> P Item bool.
Parameter listPatternItems : nat -> (PatternGoal -> P Item Pattern) -> Modes -> list Pattern -> P Item Read.
Parameter listPatternDots : nat -> (PatternGoal -> P Item Pattern) -> Modes -> list Pattern -> bool -> P Item Read.

Definition isEmpty {A} (xs : list A) : bool := match xs with [] => true | _ => false end.

Definition listPatternStep more pself modes (found : list Pattern) (closed : bool) : P Item Read :=
  if closed then ret (rev found, (negb (isEmpty found), None))
  else do dots <- at_ modes DotDot ;; listPatternDots more pself modes found dots.

Axiom followsAt : forall modes wanted, Follows SameCode eq (at_ modes wanted) (at_ modes wanted).

Axiom followsListPatternDots : forall pself pselfTwin, PatternSelfFollows pself pselfTwin ->
  forall more modes found foundTwin, Forall2 PatternsAlike found foundTwin -> forall dots,
  (forall found foundTwin, Forall2 PatternsAlike found foundTwin ->
    Follows SameCode ListRead (listPatternItems more pself modes found)
      (listPatternItems more pselfTwin modes foundTwin)) ->
  Follows SameCode ListRead (listPatternDots more pself modes found dots)
    (listPatternDots more pselfTwin modes foundTwin dots).

Lemma forall2Rev {A B} (r : A -> B -> Prop) xs ys : Forall2 r xs ys -> Forall2 r (rev xs) (rev ys).
Proof. induction 1; simpl; auto using Forall2_app. Qed.

(* sample: followsListPatternStep *)
Lemma followsListPatternStep pself pselfTwin (pknot : PatternSelfFollows pself pselfTwin)
  (more : nat) (modes : Modes) (found foundTwin : list Pattern)
  (founds : Forall2 PatternsAlike found foundTwin) (closed : bool)
  (rest : forall found foundTwin, Forall2 PatternsAlike found foundTwin ->
    Follows SameCode ListRead (listPatternItems more pself modes found)
      (listPatternItems more pselfTwin modes foundTwin)) :
  Follows SameCode ListRead (listPatternStep more pself modes found closed)
    (listPatternStep more pselfTwin modes foundTwin closed).
Proof.
  destruct closed; simpl.
  - apply followsPure. repeat split; simpl; [now apply forall2Rev | now destruct founds].
  - apply followsBind with (mid := eq); [apply followsAt | intros dots ? <-].
    now apply followsListPatternDots.
Qed.

End TwoRun2.

(** * readback 1: runsBlockOneLine (Syntax/ReadBackProofs.sw) *)
Module ReadBack1.

Parameter Item Expr Goal Modes LineKind Let Attributes Header DefBody : Type.

Inductive Statement :=
  | LetStatement (binding : Let)
  | LocalDef (attributes : list Attributes) (header : Header) (body : DefBody)
  | ExprStatement (value : Expr).

(* Expr's Block constructor (Expr is opaque here: the proof never takes a tree apart). *)
Parameter Block : Statement -> list Statement -> Expr -> Expr.

Definition blockResult (statements : list Statement) : P Item Expr :=
  match statements with
  | [ExprStatement value] => ret value
  | ExprStatement value :: last :: earlier =>
    match rev (last :: earlier) with
    | first :: rest => ret (Block first rest value)
    | [] => ret value
    end
  | LetStatement _ :: _ => fatal "a block must end with an expression, not `let`"
  | LocalDef _ _ _ :: _ => fatal "a block must end with an expression, not a local `def` or `theorem`"
  | [] => fatal "the parser read no line of a block"
  end.

Parameter statement : (Goal -> P Item Expr) -> Modes -> P Item Statement.
Parameter blockModes : Modes -> nat -> bool -> Modes.
Parameter lineModes : Modes -> nat -> bool -> option nat -> LineKind -> Modes.
Parameter nextIndex : list Item -> option nat.
Parameter continuesAt : nat -> list Item -> bool.
Parameter blockLines : nat -> (Goal -> P Item Expr) -> Modes -> nat -> bool -> list Statement -> P Item (list Statement).

Definition block self modes column many : P Item Expr :=
  do here <- mark ;;
  do lines <- blockLines (S (List.length (rest here))) self (blockModes modes column many) column many [] ;;
  blockResult lines.

Axiom runsBlockLinesOneLine : forall more self modes column many found (state : Mark Item) read rst first,
  (forall kind (middle : Mark Item), offset middle = offset state ->
    RunsFrom middle (statement self (lineModes modes column many (nextIndex (read ++ rst)) kind)) read rst first) ->
  continuesAt column rst = false ->
  RunsFrom state (blockLines (S more) self modes column many found) read rst (first :: found).

(* sample: runsBlockOneLine *)
Lemma runsBlockOneLine self modes column many (state : Mark Item) (read rst : list Item) (value : Expr)
  (line : forall kind (middle : Mark Item), offset middle = offset state ->
    RunsFrom middle
      (statement self (lineModes (blockModes modes column many) column many (nextIndex (read ++ rst)) kind))
      read rst (ExprStatement value))
  (ends : continuesAt column rst = false) :
  RunsFrom state (block self modes column many) read rst value.
Proof.
  intros shape.
  destruct (runsBlockLinesOneLine (List.length (rest state)) self _ column many [] state read rst _ line ends shape)
    as (after & ran & R & O).
  exists after. unfold block, bind, mark. now rewrite ran.
Qed.

End ReadBack1.

(** * readback 2: openWithin (Syntax/ReadBackHungFrameLemmas.sw) *)
Module ReadBack2.

Parameter Tok Token Leaf : Type.
Parameter isOpener : Tok -> bool.
Parameter kind : Token -> Tok.
Parameter token : Leaf -> Token.

Record HangState := { blocks : list (option nat); top : option nat; start : bool; glue : bool }.

(* step and entered are opaque: the proof uses step through hangOpenStep and never looks inside
   entered. *)
Parameter step : HangState -> Leaf -> option HangState.
Parameter entered : HangState -> Leaf -> HangState.

Definition Within (state entered : HangState) : Prop :=
  exists placed, blocks state = placed :: blocks entered /\ top state = top entered.

Axiom hangOpenStep : forall state next leaf, isOpener (kind (token leaf)) = true ->
  step state leaf = Some next ->
  next = {| blocks := None :: blocks (entered state leaf); top := top (entered state leaf);
            start := true; glue := false |}.

(* sample: openWithin *)
Lemma openWithin (state next : HangState) (leaf : Leaf)
  (opener : isOpener (kind (token leaf)) = true)
  (stepped : step state leaf = Some next) :
  Within next (entered state leaf).
Proof. rewrite (hangOpenStep _ _ _ opener stepped). now exists None. Qed.

End ReadBack2.

(** * readback 3: unaryHung (Syntax/ReadBackHungApp.sw) *)
Module ReadBack3.

Parameter Word Leaf Modes HangState InfixKind : Type.
Parameter leafWord : Leaf -> Word.

(* Cut down from Syntax/Token.sw: the kinds the proof and its definitions name, and Lower for the rest. *)
Inductive Tok := Lower | Num | Float | Minus | Bang | Dot | KwMatch.
Scheme Equality for Tok.

(* Cut down from Syntax/DeafProofs.sw's Item: the fields negativeNumeral and the proof read. *)
Record Item := { kind : Tok; leaf : Leaf; glued : bool; afterOperand : bool }.

(* Cut down from Syntax/Expr.sw: Atom, App, Infix and Prefix kept; the proof meets the other
   constructors only where signed is false, a contradiction, as it is for Atom. *)
Inductive Expr :=
  | Atom (k : Tok) (word : Word)
  | App (head : Expr) (arguments : list Expr)
  | Infix (k : InfixKind) (l : Expr) (operator : Word) (r : Expr)
  | Prefix (operator : Word) (operand : Expr).

Fixpoint signed (expr : Expr) : bool :=
  match expr with Prefix _ _ => true | App head _ | Infix _ head _ _ => signed head | _ => false end.
Definition unary (expr : Expr) : bool := match expr with Infix _ _ _ _ => false | _ => true end.
Definition numeral1 (expr : Expr) : bool := match expr with Atom Num _ | Atom Float _ => true | _ => false end.
Definition primary (expr : Expr) : bool := match expr with Atom _ _ => true | _ => false end.
Definition prefix (expr : Expr) : bool := match expr with Prefix _ _ => true | _ => false end.

(* nestAll and autoPlacedAll are mutual with nest and autoPlaced; the proof computes neither. *)
Parameter nestAll : list Expr -> nat.
Parameter autoPlacedAll : bool -> list Expr -> bool.
Parameter arrowKind1 : InfixKind -> bool.

Fixpoint nest (expr : Expr) : nat :=
  match expr with
  | App head arguments => nest head + nestAll arguments + 1
  | Prefix _ operand => nest operand + 1
  | Infix _ l _ r => nest l + nest r + 1
  | _ => 0
  end.

Fixpoint autoPlaced (expr : Expr) (full : bool) : bool :=
  match expr with
  | App head arguments => autoPlaced head full && autoPlacedAll false arguments
  | Prefix _ operand => autoPlaced operand false
  | Infix k l _ r => autoPlaced l full && autoPlaced r (arrowKind1 k)
  | Atom _ _ => true
  end.

Definition negativeNumeral (items : list Item) : bool :=
  match items with
  | minus :: number :: _ =>
    Tok_beq (kind minus) Minus && (Tok_beq (kind number) Num || Tok_beq (kind number) Float) && glued number
      && negb (afterOperand minus && glued minus)
  | _ => false
  end.

Definition startKind (k : Tok) : bool := match k with Lower | Num | Float => true | _ => false end.
Definition signKind (k : Tok) : bool := match k with Minus | Bang => true | _ => false end.
Definition leadKind (k : Tok) : bool := match k with Lower | Num | Float | Minus | Bang => true | _ => false end.

Definition headFits (head : Expr) (read : list Item) : bool := primary head || (prefix head && negativeNumeral read).

Parameter wordWithin1 : Tok -> bool.
Parameter argumentFits : Expr -> list Item -> bool.
(* Std's Parse.loopReads and Parse.stepValues. *)
Parameter loopReads : list Item -> list (list Item * Expr) -> list Item.
Parameter stepValues : list (list Item * Expr) -> list Expr.
(* SpeltArgs (mutual with Spelt) and Spelt's infix clause are opaque: the proof never enters them. *)
Parameter SpeltArgs : list Expr -> list (list Item * Expr) -> Prop.
Parameter InfixSpelt : InfixKind -> Expr -> Word -> Expr -> list Item -> Prop.

(* Cut down from Syntax/ReadBackLine.sw: the clauses of the kept constructors. *)
Fixpoint Spelt (expr : Expr) (read : list Item) : Prop :=
  match expr with
  | Atom k word => exists item, read = [item] /\ kind item = k /\ leafWord (leaf item) = word /\ wordWithin1 k = true
  | App head (argument :: more) =>
    exists headRead argRead steps, read = headRead ++ (argRead ++ loopReads [] steps)
      /\ headFits head headRead = true
      /\ argumentFits argument argRead = true
      /\ Spelt head headRead
      /\ Spelt argument argRead
      /\ SpeltArgs more steps
  | App _ [] => False
  | Prefix operator operand =>
    exists sign more, read = sign :: more
      /\ signKind (kind sign) = true
      /\ leafWord (leaf sign) = operator
      /\ (negativeNumeral (sign :: more) = true -> numeral1 operand = true)
      /\ unary operand = true
      /\ Spelt operand more
  | Infix k l operator r => InfixSpelt k l operator r read
  end.

(* Cut down from Syntax/Parser.sw: the levels Layer names, and LevelInline for the rest. *)
Inductive Level := LevelFull | LevelInline | LevelUnary | LevelArgument.
Record Goal := { goalModes : Modes; level : Level }.

Definition Sub := Goal -> list Item -> list Item -> Expr -> Prop.

Parameter stops : Modes -> Item -> bool.
Parameter peekIn : Modes -> nat -> list Item -> option Tok.
Parameter matchesBarOn : Modes -> list Item -> bool.
Parameter startsAtomOn : Modes -> list Item -> bool.

Definition isSome (wanted : Tok) (seen : option Tok) : bool :=
  match seen with Some found => Tok_beq found wanted | None => false end.

Parameter AtomEnds : Modes -> bool -> Tok -> list Item -> Prop.
Parameter WordBase : Item -> list Item -> Expr -> Prop.
Parameter ParenBase TupleBase ListBase SignBase : Sub -> Modes -> Item -> list Item -> list Item -> Expr -> Prop.
Parameter EmptyListBase : Modes -> Item -> list Item -> list Item -> Expr -> Prop.
Parameter FullReads ArgumentReads : Sub -> Modes -> list Item -> list Item -> Expr -> Prop.
Parameter ArgsReads : Sub -> Modes -> list (list Item * Expr) -> list Item -> Prop.

Definition NumberBase (item : Item) (more rst : list Item) (value : Expr) : Prop :=
  exists number, more = [number]
    /\ value = Prefix (leafWord (leaf item)) (Atom (kind number) (leafWord (leaf number)))
    /\ kind item = Minus
    /\ negativeNumeral (item :: number :: rst) = true.

Definition BaseReads (sub : Sub) modes item more rst value : Prop :=
  WordBase item more value
    \/ ParenBase sub modes item more rst value
    \/ TupleBase sub modes item more rst value
    \/ EmptyListBase modes item more rst value
    \/ ListBase sub modes item more rst value
    \/ NumberBase item more rst value
    \/ SignBase sub modes item more rst value.

Definition AtomReads (sub : Sub) modes (head : bool) (read rst : list Item) value : Prop :=
  exists item more, read = item :: more
    /\ stops modes item = false
    /\ AtomEnds modes head (kind item) rst
    /\ BaseReads sub modes item more rst value.

Definition AppReads (sub : Sub) modes (read rst : list Item) value : Prop :=
  (isSome Dot (peekIn modes 0 (read ++ rst)) = false
    /\ AtomReads sub modes true read rst value
    /\ startsAtomOn modes rst = false)
    \/ (exists headRead read1 steps head first, read = headRead ++ (read1 ++ loopReads [] steps)
      /\ value = App head (first :: stepValues steps)
      /\ isSome Dot (peekIn modes 0 (read ++ rst)) = false
      /\ AtomReads sub modes true headRead ((read1 ++ loopReads [] steps) ++ rst) head
      /\ startsAtomOn modes ((read1 ++ loopReads [] steps) ++ rst) = true
      /\ ArgumentReads sub modes read1 (loopReads [] steps ++ rst) first
      /\ ArgsReads sub modes steps rst).

Definition UnaryReads (sub : Sub) modes (read rst : list Item) value : Prop :=
  (exists sign more operand, read = sign :: more
    /\ value = Prefix (leafWord (leaf sign)) operand
    /\ stops modes sign = false
    /\ (Tok_beq (kind sign) Minus || Tok_beq (kind sign) Bang) = true
    /\ matchesBarOn modes (sign :: more ++ rst) = false
    /\ (Tok_beq (kind sign) Minus && negativeNumeral (sign :: more ++ rst)) = false
    /\ sub {| goalModes := modes; level := LevelUnary |} more rst operand)
    \/ (exists item more, read = item :: more
      /\ stops modes item = false
      /\ Tok_beq (kind item) KwMatch = false
      /\ matchesBarOn modes (item :: more ++ rst) = false
      /\ ((Tok_beq (kind item) Minus || Tok_beq (kind item) Bang) = false
        \/ (Tok_beq (kind item) Minus = true /\ negativeNumeral (item :: more ++ rst) = true))
      /\ AppReads sub modes read rst value).

Definition Layer (sub : Sub) (goal : Goal) read rst value : Prop :=
  match level goal with
  | LevelFull => FullReads sub (goalModes goal) read rst value
  | LevelUnary => UnaryReads sub (goalModes goal) read rst value
  | LevelArgument => AtomReads sub (goalModes goal) false read rst value
  | _ => False
  end.

Fixpoint TreeN (depth : nat) : Sub :=
  match depth with 0 => fun _ _ _ _ => False | S below => Layer (TreeN below) end.

(* Cut down from Syntax/ReadBackLine.sw's Quiet: only passed along. *)
Parameter Quiet : Modes -> Prop.
Parameter entered : HangState -> Leaf -> HangState.
Parameter bounds : Modes -> HangState -> bool.
Parameter hangsFrom : HangState -> list Leaf -> bool.
Parameter openHead : Modes -> list Item -> bool.
(* The per-item tests of lineAll (lineKind on the kind) and deepAll (on kind and depth). *)
Parameter lineItem deepItem : Item -> bool.

Definition enters (state : HangState) (items : list Item) : HangState :=
  match items with [] => state | item :: _ => entered state (leaf item) end.
Definition leavesOf (read : list Item) : list Leaf := map leaf read.
Definition lineAll : list Item -> bool := forallb lineItem.
Definition deepAll : list Item -> bool := forallb deepItem.

Record HungAt modes state (read rst : list Item) : Prop := {
  lineRead : lineAll read = true;
  lineRest : lineAll rst = true;
  openFirst : openHead modes read = true;
  bound : bounds modes (enters state read) = true;
  hung : hangsFrom state (leavesOf (read ++ rst)) = true;
  deepItems : deepAll (read ++ rst) = true }.

Record UnaryEnds modes (rst : list Item) : Prop := {
  atom : forall head k, AtomEnds modes head k rst;
  noArgument : startsAtomOn modes rst = false }.

(* FullHungAt depth is the full level's read-back fact at depth; the proof only passes it on. *)
Parameter FullHungAt : nat -> Prop.
Definition FullHungBelow (depth : nat) : Prop := forall smaller, smaller < depth -> FullHungAt smaller.

Axiom speltPlainStarts : forall expr read, Spelt expr read -> signed expr = false ->
  exists item more, read = item :: more /\ startKind (kind item) = true.
Axiom startFacts : forall k, startKind k = true ->
  Tok_beq k Dot = false /\ Tok_beq k KwMatch = false /\ (Tok_beq k Minus || Tok_beq k Bang) = false.
Axiom openHeadStops : forall modes item later, openHead modes (item :: later) = true -> stops modes item = false.
Axiom noBarLine : forall modes item later, lineAll later = true -> matchesBarOn modes (item :: later) = false.
Axiom lineJoin : forall first rst, lineAll first = true -> lineAll rst = true -> lineAll (first ++ rst) = true.
Axiom appAnyHung : forall modes, Quiet modes -> forall expr read rst depth state,
  FullHungBelow depth -> nest expr <= depth -> Spelt expr read -> autoPlaced expr false = true ->
  HungAt modes state read rst -> UnaryEnds modes rst -> signed expr = false -> unary expr = true ->
  AppReads (TreeN depth) modes read rst expr.
Axiom appHung : forall modes, Quiet modes -> forall head argument more read rst depth state,
  FullHungBelow depth -> nest (App head (argument :: more)) <= depth -> Spelt (App head (argument :: more)) read ->
  autoPlaced (App head (argument :: more)) false = true -> HungAt modes state read rst -> UnaryEnds modes rst ->
  AppReads (TreeN depth) modes read rst (App head (argument :: more)).
Axiom pastFirst : forall modes state item rst, leadKind (kind item) = true ->
  bounds modes (entered state (leaf item)) = true -> hangsFrom state (leavesOf (item :: rst)) = true ->
  exists next, bounds modes next = true /\ hangsFrom next (leavesOf rst) = true.
Axiom signLead : forall k, signKind k = true -> leadKind k = true.
Axiom speltStarts : forall expr read, Spelt expr read ->
  exists item more, read = item :: more /\ leadKind (kind item) = true.
Axiom leadHung : forall modes state item rst, Quiet modes -> leadKind (kind item) = true ->
  bounds modes state = true -> hangsFrom state (leavesOf (item :: rst)) = true ->
  stops modes item = false /\ bounds modes (entered state (leaf item)) = true
    /\ exists next, bounds modes next = true /\ hangsFrom next (leavesOf rst) = true.
Axiom openHeadOf : forall modes item later, stops modes item = false -> openHead modes (item :: later) = true.
Axiom negativeMinus : forall sign more, negativeNumeral (sign :: more) = true -> kind sign = Minus.
Axiom peekFirst : forall modes item rst, stops modes item = false -> peekIn modes 0 (item :: rst) = Some (kind item).
Axiom signOr : forall k, signKind k = true -> (Tok_beq k Minus || Tok_beq k Bang) = true.
Axiom belowLess : forall small big, small <= big -> FullHungBelow big -> FullHungBelow small.

(* sample: unaryHung *)
Fixpoint unaryHung (modes : Modes) (quiet : Quiet modes) (expr : Expr) (read rst : list Item) (depth : nat)
  (state : HangState) (inner : FullHungBelow depth) (deep : nest expr <= depth) (spelt : Spelt expr read)
  (free : autoPlaced expr false = true) (facts : HungAt modes state read rst) (ends : UnaryEnds modes rst)
  (isUnary : unary expr = true) {struct depth} :
  UnaryReads (TreeN depth) modes read rst expr.
Proof.
  destruct (signed expr) eqn:isSigned.
  2: {
    destruct (speltPlainStarts _ _ spelt isSigned) as (item & more & -> & starts).
    destruct (startFacts _ starts) as (_ & notMatch & unsigned).
    pose proof (lineRead _ _ _ _ facts) as L. simpl in L. apply andb_prop in L as [_ L].
    right. exists item, more. repeat split.
    - exact (openHeadStops _ _ _ (openFirst _ _ _ _ facts)).
    - exact notMatch.
    - apply noBarLine, lineJoin; [exact L | apply (lineRest _ _ _ _ facts)].
    - now left.
    - exact (appAnyHung _ quiet _ _ _ _ _ inner deep spelt free facts ends isSigned isUnary). }
  destruct expr as [| head [| argument arguments] | | operator operand]; try discriminate; simpl in spelt.
  - contradiction.
  - pose proof (appHung _ quiet _ _ _ _ _ _ _ inner deep spelt free facts ends) as call.
    destruct spelt as (headRead & argRead & steps & -> & fits & _ & headSpelt & _).
    destruct head as [| | | ? operand]; try discriminate; simpl in fits.
    destruct headSpelt as (sign & more & -> & _ & _ & numeral & _ & operandSpelt).
    destruct operand; try (specialize (numeral fits); discriminate).
    destruct operandSpelt as (number & -> & _).
    pose proof (negativeMinus _ _ fits) as isMinus.
    pose proof (lineRead _ _ _ _ facts) as L. apply andb_prop in L as [_ L].
    right. exists sign, (number :: argRead ++ loopReads [] steps). repeat split.
    + exact (openHeadStops _ _ _ (openFirst _ _ _ _ facts)).
    + now rewrite isMinus.
    + apply noBarLine, (lineJoin (number :: _)); [exact L | apply (lineRest _ _ _ _ facts)].
    + right. split; [now rewrite isMinus | exact fits].
    + exact call.
  - destruct depth as [| below]; [simpl in deep; lia |].
    destruct spelt as (sign & more & -> & isSign & isWord & numeral & operandUnary & operandSpelt).
    pose proof (openHeadStops _ _ _ (openFirst _ _ _ _ facts)) as openSign.
    pose proof (lineRead _ _ _ _ facts) as L. simpl in L. apply andb_prop in L as [_ lineMore].
    pose proof (deepItems _ _ _ _ facts) as D. simpl in D. apply andb_prop in D as [_ deepMore].
    destruct (pastFirst _ _ _ _ (signLead _ isSign) (bound _ _ _ _ facts) (hung _ _ _ _ facts))
      as (s1 & s1Bound & hungMore).
    destruct (speltStarts _ _ operandSpelt) as (first & others & -> & lead).
    destruct (leadHung _ _ _ _ quiet lead s1Bound hungMore) as (openOperand & enteredOperand & _).
    pose proof (noBarLine modes sign _ (lineJoin _ _ lineMore (lineRest _ _ _ _ facts))) as noBar.
    destruct (negativeNumeral (sign :: first :: others)) eqn:negative.
    + destruct operand as [k word | | |]; try (specialize (numeral negative); discriminate).
      destruct operandSpelt as (number & isNumber & isKind & isNumberWord & _).
      injection isNumber as -> ->.
      pose proof (negativeMinus _ _ negative) as isMinus.
      right. exists sign, [number]. repeat split.
      * exact openSign.
      * now rewrite isMinus.
      * exact noBar.
      * right. split; [now rewrite isMinus | exact negative].
      * left. split; [| split; [| exact (noArgument _ _ ends)]].
        -- simpl. now rewrite (peekFirst _ _ _ openSign), isMinus.
        -- exists sign, [number]. split; [reflexivity | split; [exact openSign | split; [apply (atom _ _ ends) |]]].
           do 5 right. left. exists number. rewrite <- isWord, <- isKind, <- isNumberWord.
           repeat split; [exact isMinus | exact negative].
    + left. exists sign, (first :: others), operand. repeat split; auto using signOr.
      * now rewrite isWord.
      * assert (negativeNumeral (sign :: (first :: others) ++ rst) = false) as N by exact negative.
        now rewrite N, andb_false_r.
      * apply (unaryHung modes quiet operand (first :: others) rst below s1); auto.
        -- apply (belowLess below (S below)); auto.
        -- simpl in deep. lia.
        -- pose proof (lineRest _ _ _ _ facts). constructor; auto using openHeadOf.
Qed.

End ReadBack3.

(** * readback 4: runsWalkHere (Syntax/ReadBackRuns.sw) *)
Module ReadBack4.

Parameter Item Modes : Type.
(* walkOn modes items is isSome KwByWalking (peekIn modes 0 items); the proof only uses no. *)
Parameter walkOn : Modes -> list Item -> bool.

Definition walkHere (modes : Modes) : P Item bool := do items <- left ;; ret (walkOn modes items).

(* sample: runsWalkHere *)
Lemma runsWalkHere (modes : Modes) (items : list Item) (no : walkOn modes items = false) :
  Runs (walkHere modes) [] items false.
Proof.
  intros state shape. exists state. unfold walkHere, bind, left, ret.
  simpl in shape. now rewrite shape, no.
Qed.

End ReadBack4.
