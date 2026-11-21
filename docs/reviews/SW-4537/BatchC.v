(* SW-4540, batch C of SW-4537: the printer (printer 2 to 11) and the top (top 1 to 3), in Rocq 9.1 with its
   Stdlib only. Counted lemmas follow a "sample:" comment; everything else is uncounted support (cut-down
   definitions, and lemmas the Stitchwort proof names, as axioms).
   Check: rocq compile -R <stdlib>/lib/coq/9.1/user-contrib/Stdlib Stdlib BatchC.v *)
From Stdlib Require Import List Bool String Lia PeanoNat.
Import ListNotations.
Open Scope nat_scope.


(** * printer 5: exprBlanks (Fmt/TraverseFail.sw) *)
Module ExprBlanks.

(* The node types below Expr are mutual with it in Stitchwort; the drawn theorem reaches them only through
   their own ...Blanks theorems (rule 8), so they and their walks, blankings and traversals are opaque. *)
Parameters Word Comments Tok InfixKind BindingKind FactsKind Param Piece Scrutinee Arm Group Row : Type.
Parameters Statement Let_ HandlerClause InductArm CalcStep Rules : Type.
Parameter blankWord : Word -> Word.
Parameter noComments : Comments.

Inductive Expr :=
  | Atom (kind : Tok) (word : Word)
  | Paren (opener : Word) (inner : Expr) (close : Word)
  | Unit (opener : Word) (close : Word)
  | Universe (keyword : Word) (level : Word)
  | Include (keyword : Word) (path : Word)
  | Tuple (opener : Word) (items : list Expr) (trailingComma : bool) (close : Word)
  | ListOf (opener : Word) (items : list Expr) (trailingComma : bool) (close : Word)
  | Spread (dots : Word) (lst : Expr)
  | Record (opener : Word) (base : option (Expr * Word)) (fields : list Expr) (trailingComma : bool) (close : Word)
  | RecordField (name : Word) (equals : Word) (value : Expr)
  | CtorFields (ctor : Expr) (record : Expr)
  | App (head : Expr) (arguments : list Expr)
  | NamedArg (opener : Word) (name : Word) (colonEq : Word) (value : Expr) (close : Word)
  | FieldAccess (target : option Expr) (dot : Word) (field : Word)
  | Section (body : Expr)
  | OperatorSection (opener : Word) (lhs : option Expr) (operator : Word) (rhs : option Expr) (close : Word)
  | Infix (kind : InfixKind) (lhs : Expr) (operator : Word) (rhs : Expr)
  | Chain (first : Expr) (rest : list (Word * Expr))
  | Prefix (operator : Word) (operand : Expr)
  | Binding (kind : BindingKind) (keyword : option Word) (params : list Param) (arrow : Word) (body : Expr)
  | If (keyword : Word) (binder : option (Word * Word)) (condition : Expr) (thenKeyword : Word)
      (whenTrue : Expr) (elseKeyword : Word) (whenFalse : Expr)
  | Annotation (opener : Word) (value : Expr) (colon : Word) (annotation : Expr) (close : Word)
  | Interpolated (pieces : list Piece)
  | Match (keyword : Word) (scrutinees : list Scrutinee) (withKeyword : Word) (arms : list Arm)
  | ClauseLambda (keyword : Word) (word : option Word) (arms : list Arm)
  | Facts (kind : FactsKind) (keyword : Word) (facts : Expr)
  | FunctionType (binder : Group) (arrow : Word) (result : Expr)
  | Effect (row : Row) (result : Expr)
  | Block (first : Statement) (rest : list Statement) (result : Expr)
  | LetIn (binding : Let_) (semicolon : Comments) (body : Expr)
  | Handle (keyword : Comments) (computation : Expr) (withKeyword : Comments) (clauses : list HandlerClause)
  | Reify (keyword : Comments) (reify : Comments) (computation : Expr) (withKeyword : Comments)
      (clauses : list HandlerClause)
  | Induct (keyword : Comments) (induct : Comments) (call : Expr) (withKeyword : Comments)
      (arms : list InductArm)
  | Calc (keyword : Comments) (first : Expr) (steps : list CalcStep)
  | Rewrite (keyword : Comments) (rules : Rules) (target : option (Comments * Expr))
      (body : option (Comments * Expr))
  | Cases (keyword : Comments) (targets : list Word) (body : option (Comments * Expr))
  | Walk (keyword : Comments) (items : Expr) (body : option (Comments * Expr)).

(* Fail.toResult's result, and std's bind and map on it. *)
Definition res (A : Type) := (string + A)%type.
Definition bind {A B} (r : res A) (k : A -> res B) : res B := match r with inl e => inl e | inr x => k x end.
Definition map {A B} (f : A -> B) (r : res A) : res B := match r with inl e => inl e | inr x => inr (f x) end.
Notation "'do' x <- p ;; q" := (bind p (fun x => q)) (at level 200, x name, right associativity).

(* std's Fail.toResultAlike1Then, the shape of every arm. *)
Lemma alike1 {A B} (t t' : res A) (bl : A -> A) (k k' : A -> res B) (g : B -> B) :
  t' = map bl t -> (forall v, k' (bl v) = map g (k v)) -> bind t' k' = map g (bind t k).
Proof. intros -> step. destruct t; simpl; auto. Qed.

(* Cut down from Fmt.Walk.Pure and Syntax.Steps: only the expr step is kept. *)
Record Pure := { pureExpr : Expr -> Expr }.
Record Steps := { stepExpr : Expr -> res Expr }.

Parameter walkExprs : Pure -> list Expr -> list Expr.
Parameter walkBefore : Pure -> option (Expr * Word) -> option (Expr * Word).
Parameter walkOptional : Pure -> option Expr -> option Expr.
Parameter walkLinks : Pure -> list (Word * Expr) -> list (Word * Expr).
Parameter walkParams : Pure -> list Param -> list Param.
Parameter walkPieces : Pure -> list Piece -> list Piece.
Parameter walkScrutinees : Pure -> list Scrutinee -> list Scrutinee.
Parameter walkArms : Pure -> list Arm -> list Arm.
Parameter walkGroup : Pure -> Group -> Group.
Parameter walkRow : Pure -> Row -> Row.
Parameter walkStatement : Pure -> Statement -> Statement.
Parameter walkStatements : Pure -> list Statement -> list Statement.
Parameter walkLet : Pure -> Let_ -> Let_.
Parameter walkClauses : Pure -> list HandlerClause -> list HandlerClause.
Parameter walkInductArms : Pure -> list InductArm -> list InductArm.
Parameter walkSteps : Pure -> list CalcStep -> list CalcStep.
Parameter walkRules : Pure -> Rules -> Rules.
Parameter walkAfter : Pure -> option (Comments * Expr) -> option (Comments * Expr).

Parameter traverseExprs : Steps -> list Expr -> res (list Expr).
Parameter traverseBefore : Steps -> option (Expr * Word) -> res (option (Expr * Word)).
Parameter traverseOptional : Steps -> option Expr -> res (option Expr).
Parameter traverseLinks : Steps -> list (Word * Expr) -> res (list (Word * Expr)).
Parameter traverseParams : Steps -> list Param -> res (list Param).
Parameter traversePieces : Steps -> list Piece -> res (list Piece).
Parameter traverseScrutinees : Steps -> list Scrutinee -> res (list Scrutinee).
Parameter traverseArms : Steps -> list Arm -> res (list Arm).
Parameter traverseGroup : Steps -> Group -> res Group.
Parameter traverseRow : Steps -> Row -> res Row.
Parameter traverseStatement : Steps -> Statement -> res Statement.
Parameter traverseStatements : Steps -> list Statement -> res (list Statement).
Parameter traverseLet : Steps -> Let_ -> res Let_.
Parameter traverseClauses : Steps -> list HandlerClause -> res (list HandlerClause).
Parameter traverseInductArms : Steps -> list InductArm -> res (list InductArm).
Parameter traverseSteps : Steps -> list CalcStep -> res (list CalcStep).
Parameter traverseRules : Steps -> Rules -> res Rules.
Parameter traverseAfter : Steps -> option (Comments * Expr) -> res (option (Comments * Expr)).

Parameter blankBase : option (Expr * Word) -> option (Expr * Word).
Parameter blankLinks : list (Word * Expr) -> list (Word * Expr).
Parameter blankParams : list Param -> list Param.
Parameter blankPair : option (Word * Word) -> option (Word * Word).
Parameter blankPieces : list Piece -> list Piece.
Parameter blankScrutinees : list Scrutinee -> list Scrutinee.
Parameter blankArms : list Arm -> list Arm.
Parameter blankGroup : Group -> Group.
Parameter blankRow : Row -> Row.
Parameter blankStatement : Statement -> Statement.
Parameter blankStatements : list Statement -> list Statement.
Parameter blankLet : Let_ -> Let_.
Parameter blankClauses : list HandlerClause -> list HandlerClause.
Parameter blankInductArms : list InductArm -> list InductArm.
Parameter blankCalcSteps : list CalcStep -> list CalcStep.
Parameter blankRules : Rules -> Rules.
Parameter blankAfter : option (Comments * Expr) -> option (Comments * Expr).
Parameter blankWords : list Word -> list Word.

Definition blankExpr (expr : Expr) : Expr :=
  match expr with
  | Atom kind word => Atom kind (blankWord word)
  | Paren o inner c => Paren (blankWord o) inner (blankWord c)
  | Unit o c => Unit (blankWord o) (blankWord c)
  | Universe keyword level => Universe (blankWord keyword) (blankWord level)
  | Include keyword path => Include (blankWord keyword) (blankWord path)
  | Tuple o items comma c => Tuple (blankWord o) items comma (blankWord c)
  | ListOf o items comma c => ListOf (blankWord o) items comma (blankWord c)
  | Spread dots lst => Spread (blankWord dots) lst
  | Record o base fields comma c => Record (blankWord o) (blankBase base) fields comma (blankWord c)
  | RecordField name equals value => RecordField (blankWord name) (blankWord equals) value
  | NamedArg o name colonEq value c =>
    NamedArg (blankWord o) (blankWord name) (blankWord colonEq) value (blankWord c)
  | FieldAccess target dot field => FieldAccess target (blankWord dot) (blankWord field)
  | OperatorSection o lhs operator rhs c =>
    OperatorSection (blankWord o) lhs (blankWord operator) rhs (blankWord c)
  | Infix kind lhs operator rhs => Infix kind lhs (blankWord operator) rhs
  | Chain first rest => Chain first (blankLinks rest)
  | Prefix operator operand => Prefix (blankWord operator) operand
  | Binding kind keyword params arrow body =>
    Binding kind (option_map blankWord keyword) (blankParams params) (blankWord arrow) body
  | If keyword binder condition thenKeyword whenTrue elseKeyword whenFalse =>
    If (blankWord keyword) (blankPair binder) condition (blankWord thenKeyword) whenTrue (blankWord elseKeyword)
      whenFalse
  | Annotation o value colon annotation c => Annotation (blankWord o) value (blankWord colon) annotation (blankWord c)
  | Interpolated pieces => Interpolated (blankPieces pieces)
  | Match keyword scrutinees withKeyword arms =>
    Match (blankWord keyword) (blankScrutinees scrutinees) (blankWord withKeyword) (blankArms arms)
  | ClauseLambda keyword word arms => ClauseLambda (blankWord keyword) (option_map blankWord word) (blankArms arms)
  | Facts kind keyword facts => Facts kind (blankWord keyword) facts
  | FunctionType binder arrow result => FunctionType (blankGroup binder) (blankWord arrow) result
  | Effect row result => Effect (blankRow row) result
  | Block first rest result => Block (blankStatement first) (blankStatements rest) result
  | LetIn binding _ body => LetIn (blankLet binding) noComments body
  | Handle _ computation _ clauses => Handle noComments computation noComments (blankClauses clauses)
  | Reify _ _ computation _ clauses => Reify noComments noComments computation noComments (blankClauses clauses)
  | Induct _ _ call _ arms => Induct noComments noComments call noComments (blankInductArms arms)
  | Calc _ first steps => Calc noComments first (blankCalcSteps steps)
  | Rewrite _ rules target body => Rewrite noComments (blankRules rules) (blankAfter target) (blankAfter body)
  | Cases _ targets body => Cases noComments (blankWords targets) (blankAfter body)
  | Walk _ items body => Walk noComments items (blankAfter body)
  | other => other
  end.

Definition blankPure : Pure := {| pureExpr := blankExpr |}.

Fixpoint walk (on : Pure) (expr : Expr) : Expr :=
  match expr with
  | Atom kind word => pureExpr on (Atom kind word)
  | Paren o inner c => pureExpr on (Paren o (walk on inner) c)
  | Unit o c => pureExpr on (Unit o c)
  | Universe keyword level => pureExpr on (Universe keyword level)
  | Include keyword path => pureExpr on (Include keyword path)
  | Tuple o items comma c => pureExpr on (Tuple o (walkExprs on items) comma c)
  | ListOf o items comma c => pureExpr on (ListOf o (walkExprs on items) comma c)
  | Spread dots lst => pureExpr on (Spread dots (walk on lst))
  | Record o base fields comma c => pureExpr on (Record o (walkBefore on base) (walkExprs on fields) comma c)
  | RecordField name equals value => pureExpr on (RecordField name equals (walk on value))
  | CtorFields ctor record => pureExpr on (CtorFields (walk on ctor) (walk on record))
  | App head arguments => pureExpr on (App (walk on head) (walkExprs on arguments))
  | NamedArg o name colonEq value c => pureExpr on (NamedArg o name colonEq (walk on value) c)
  | FieldAccess target dot field => pureExpr on (FieldAccess (walkOptional on target) dot field)
  | Section body => pureExpr on (Section (walk on body))
  | OperatorSection o lhs operator rhs c =>
    pureExpr on (OperatorSection o (walkOptional on lhs) operator (walkOptional on rhs) c)
  | Infix kind lhs operator rhs => pureExpr on (Infix kind (walk on lhs) operator (walk on rhs))
  | Chain first rest => pureExpr on (Chain (walk on first) (walkLinks on rest))
  | Prefix operator operand => pureExpr on (Prefix operator (walk on operand))
  | Binding kind keyword params arrow body =>
    pureExpr on (Binding kind keyword (walkParams on params) arrow (walk on body))
  | If keyword binder condition thenKeyword whenTrue elseKeyword whenFalse =>
    pureExpr on (If keyword binder (walk on condition) thenKeyword (walk on whenTrue) elseKeyword
      (walk on whenFalse))
  | Annotation o value colon annotation c => pureExpr on (Annotation o (walk on value) colon (walk on annotation) c)
  | Interpolated pieces => pureExpr on (Interpolated (walkPieces on pieces))
  | Match keyword scrutinees withKeyword arms =>
    pureExpr on (Match keyword (walkScrutinees on scrutinees) withKeyword (walkArms on arms))
  | ClauseLambda keyword word arms => pureExpr on (ClauseLambda keyword word (walkArms on arms))
  | Facts kind keyword facts => pureExpr on (Facts kind keyword (walk on facts))
  | FunctionType binder arrow result => pureExpr on (FunctionType (walkGroup on binder) arrow (walk on result))
  | Effect row result => pureExpr on (Effect (walkRow on row) (walk on result))
  | Block first rest result =>
    pureExpr on (Block (walkStatement on first) (walkStatements on rest) (walk on result))
  | LetIn binding semicolon body => pureExpr on (LetIn (walkLet on binding) semicolon (walk on body))
  | Handle keyword computation withKeyword clauses =>
    pureExpr on (Handle keyword (walk on computation) withKeyword (walkClauses on clauses))
  | Reify keyword reify computation withKeyword clauses =>
    pureExpr on (Reify keyword reify (walk on computation) withKeyword (walkClauses on clauses))
  | Induct keyword induct call withKeyword arms =>
    pureExpr on (Induct keyword induct (walk on call) withKeyword (walkInductArms on arms))
  | Calc keyword first steps => pureExpr on (Calc keyword (walk on first) (walkSteps on steps))
  | Rewrite keyword rules target body =>
    pureExpr on (Rewrite keyword (walkRules on rules) (walkAfter on target) (walkAfter on body))
  | Cases keyword targets body => pureExpr on (Cases keyword targets (walkAfter on body))
  | Walk keyword items body => pureExpr on (Walk keyword (walk on items) (walkAfter on body))
  end.

Fixpoint traverse (on : Steps) (expr : Expr) : res Expr :=
  match expr with
  | Atom kind word => stepExpr on (Atom kind word)
  | Paren o inner c => do v <- traverse on inner ;; stepExpr on (Paren o v c)
  | Unit o c => stepExpr on (Unit o c)
  | Universe keyword level => stepExpr on (Universe keyword level)
  | Include keyword path => stepExpr on (Include keyword path)
  | Tuple o items comma c => do v <- traverseExprs on items ;; stepExpr on (Tuple o v comma c)
  | ListOf o items comma c => do v <- traverseExprs on items ;; stepExpr on (ListOf o v comma c)
  | Spread dots lst => do v <- traverse on lst ;; stepExpr on (Spread dots v)
  | Record o base fields comma c =>
    do v1 <- traverseBefore on base ;; do v2 <- traverseExprs on fields ;; stepExpr on (Record o v1 v2 comma c)
  | RecordField name equals value => do v <- traverse on value ;; stepExpr on (RecordField name equals v)
  | CtorFields ctor record =>
    do v1 <- traverse on ctor ;; do v2 <- traverse on record ;; stepExpr on (CtorFields v1 v2)
  | App head arguments =>
    do v1 <- traverse on head ;; do v2 <- traverseExprs on arguments ;; stepExpr on (App v1 v2)
  | NamedArg o name colonEq value c => do v <- traverse on value ;; stepExpr on (NamedArg o name colonEq v c)
  | FieldAccess target dot field => do v <- traverseOptional on target ;; stepExpr on (FieldAccess v dot field)
  | Section body => do v <- traverse on body ;; stepExpr on (Section v)
  | OperatorSection o lhs operator rhs c =>
    do v1 <- traverseOptional on lhs ;; do v2 <- traverseOptional on rhs ;;
    stepExpr on (OperatorSection o v1 operator v2 c)
  | Infix kind lhs operator rhs =>
    do v1 <- traverse on lhs ;; do v2 <- traverse on rhs ;; stepExpr on (Infix kind v1 operator v2)
  | Chain first rest => do v1 <- traverse on first ;; do v2 <- traverseLinks on rest ;; stepExpr on (Chain v1 v2)
  | Prefix operator operand => do v <- traverse on operand ;; stepExpr on (Prefix operator v)
  | Binding kind keyword params arrow body =>
    do v1 <- traverseParams on params ;; do v2 <- traverse on body ;; stepExpr on (Binding kind keyword v1 arrow v2)
  | If keyword binder condition thenKeyword whenTrue elseKeyword whenFalse =>
    do v1 <- traverse on condition ;; do v2 <- traverse on whenTrue ;; do v3 <- traverse on whenFalse ;;
    stepExpr on (If keyword binder v1 thenKeyword v2 elseKeyword v3)
  | Annotation o value colon annotation c =>
    do v1 <- traverse on value ;; do v2 <- traverse on annotation ;; stepExpr on (Annotation o v1 colon v2 c)
  | Interpolated pieces => do v <- traversePieces on pieces ;; stepExpr on (Interpolated v)
  | Match keyword scrutinees withKeyword arms =>
    do v1 <- traverseScrutinees on scrutinees ;; do v2 <- traverseArms on arms ;;
    stepExpr on (Match keyword v1 withKeyword v2)
  | ClauseLambda keyword word arms => do v <- traverseArms on arms ;; stepExpr on (ClauseLambda keyword word v)
  | Facts kind keyword facts => do v <- traverse on facts ;; stepExpr on (Facts kind keyword v)
  | FunctionType binder arrow result =>
    do v1 <- traverseGroup on binder ;; do v2 <- traverse on result ;; stepExpr on (FunctionType v1 arrow v2)
  | Effect row result => do v1 <- traverseRow on row ;; do v2 <- traverse on result ;; stepExpr on (Effect v1 v2)
  | Block first rest result =>
    do v1 <- traverseStatement on first ;; do v2 <- traverseStatements on rest ;; do v3 <- traverse on result ;;
    stepExpr on (Block v1 v2 v3)
  | LetIn binding semicolon body =>
    do v1 <- traverseLet on binding ;; do v2 <- traverse on body ;; stepExpr on (LetIn v1 semicolon v2)
  | Handle keyword computation withKeyword clauses =>
    do v1 <- traverse on computation ;; do v2 <- traverseClauses on clauses ;;
    stepExpr on (Handle keyword v1 withKeyword v2)
  | Reify keyword reify computation withKeyword clauses =>
    do v1 <- traverse on computation ;; do v2 <- traverseClauses on clauses ;;
    stepExpr on (Reify keyword reify v1 withKeyword v2)
  | Induct keyword induct call withKeyword arms =>
    do v1 <- traverse on call ;; do v2 <- traverseInductArms on arms ;;
    stepExpr on (Induct keyword induct v1 withKeyword v2)
  | Calc keyword first steps =>
    do v1 <- traverse on first ;; do v2 <- traverseSteps on steps ;; stepExpr on (Calc keyword v1 v2)
  | Rewrite keyword rules target body =>
    do v1 <- traverseRules on rules ;; do v2 <- traverseAfter on target ;; do v3 <- traverseAfter on body ;;
    stepExpr on (Rewrite keyword v1 v2 v3)
  | Cases keyword targets body => do v <- traverseAfter on body ;; stepExpr on (Cases keyword targets v)
  | Walk keyword items body =>
    do v1 <- traverse on items ;; do v2 <- traverseAfter on body ;; stepExpr on (Walk keyword v1 v2)
  end.

Definition runExpr (on : Steps) (input : Expr) : res Expr := traverse on input.

(* Cut down from Fmt.TraverseFail.Blanks: only the expr field, the one the proof reads. *)
Definition Blanks (on : Steps) : Prop :=
  forall z, stepExpr on (walk blankPure z) = map (walk blankPure) (stepExpr on z).

(* The other members of exprBlanks' mutual group (rule 8), on the forms their inputs take in a blanked tree. *)
Axiom exprsBlanks : forall on, Blanks on -> forall z,
  traverseExprs on (walkExprs blankPure z) = map (walkExprs blankPure) (traverseExprs on z).
Axiom beforeBlanks : forall on, Blanks on -> forall z,
  traverseBefore on (blankBase (walkBefore blankPure z)) =
    map (fun x => blankBase (walkBefore blankPure x)) (traverseBefore on z).
Axiom optionalBlanks : forall on, Blanks on -> forall z,
  traverseOptional on (walkOptional blankPure z) = map (walkOptional blankPure) (traverseOptional on z).
Axiom linksBlanks : forall on, Blanks on -> forall z,
  traverseLinks on (blankLinks (walkLinks blankPure z)) =
    map (fun x => blankLinks (walkLinks blankPure x)) (traverseLinks on z).
Axiom paramsBlanks : forall on, Blanks on -> forall z,
  traverseParams on (blankParams (walkParams blankPure z)) =
    map (fun x => blankParams (walkParams blankPure x)) (traverseParams on z).
Axiom piecesBlanks : forall on, Blanks on -> forall z,
  traversePieces on (blankPieces (walkPieces blankPure z)) =
    map (fun x => blankPieces (walkPieces blankPure x)) (traversePieces on z).
Axiom scrutineesBlanks : forall on, Blanks on -> forall z,
  traverseScrutinees on (blankScrutinees (walkScrutinees blankPure z)) =
    map (fun x => blankScrutinees (walkScrutinees blankPure x)) (traverseScrutinees on z).
Axiom armsBlanks : forall on, Blanks on -> forall z,
  traverseArms on (blankArms (walkArms blankPure z)) =
    map (fun x => blankArms (walkArms blankPure x)) (traverseArms on z).
Axiom groupBlanks : forall on, Blanks on -> forall z,
  traverseGroup on (blankGroup (walkGroup blankPure z)) =
    map (fun x => blankGroup (walkGroup blankPure x)) (traverseGroup on z).
Axiom rowBlanks : forall on, Blanks on -> forall z,
  traverseRow on (blankRow (walkRow blankPure z)) = map (fun x => blankRow (walkRow blankPure x)) (traverseRow on z).
Axiom statementBlanks : forall on, Blanks on -> forall z,
  traverseStatement on (blankStatement (walkStatement blankPure z)) =
    map (fun x => blankStatement (walkStatement blankPure x)) (traverseStatement on z).
Axiom statementsBlanks : forall on, Blanks on -> forall z,
  traverseStatements on (blankStatements (walkStatements blankPure z)) =
    map (fun x => blankStatements (walkStatements blankPure x)) (traverseStatements on z).
Axiom letBlanks : forall on, Blanks on -> forall z,
  traverseLet on (blankLet (walkLet blankPure z)) = map (fun x => blankLet (walkLet blankPure x)) (traverseLet on z).
Axiom clausesBlanks : forall on, Blanks on -> forall z,
  traverseClauses on (blankClauses (walkClauses blankPure z)) =
    map (fun x => blankClauses (walkClauses blankPure x)) (traverseClauses on z).
Axiom inductArmsBlanks : forall on, Blanks on -> forall z,
  traverseInductArms on (blankInductArms (walkInductArms blankPure z)) =
    map (fun x => blankInductArms (walkInductArms blankPure x)) (traverseInductArms on z).
Axiom calcStepsBlanks : forall on, Blanks on -> forall z,
  traverseSteps on (blankCalcSteps (walkSteps blankPure z)) =
    map (fun x => blankCalcSteps (walkSteps blankPure x)) (traverseSteps on z).
Axiom rulesBlanks : forall on, Blanks on -> forall z,
  traverseRules on (blankRules (walkRules blankPure z)) =
    map (fun x => blankRules (walkRules blankPure x)) (traverseRules on z).
Axiom afterBlanks : forall on, Blanks on -> forall z,
  traverseAfter on (blankAfter (walkAfter blankPure z)) =
    map (fun x => blankAfter (walkAfter blankPure x)) (traverseAfter on z).

(* sample: exprBlanks *)
Lemma exprBlanks (on : Steps) (deaf : Blanks on) (input : Expr) :
  runExpr on (walk blankPure input) = map (walk blankPure) (runExpr on input).
Proof.
  unfold runExpr; induction input; simpl;
    repeat (eapply alike1; [solve [eauto using exprsBlanks, beforeBlanks, optionalBlanks, linksBlanks,
      paramsBlanks, piecesBlanks, scrutineesBlanks, armsBlanks, groupBlanks, rowBlanks,
      statementBlanks, statementsBlanks, letBlanks, clausesBlanks, inductArmsBlanks,
      calcStepsBlanks, rulesBlanks, afterBlanks] | intro]);
    rewrite <- deaf; reflexivity.
Qed.

End ExprBlanks.


(** * printer 9: blankItemHangs (Fmt/ElementsBlank.sw) *)
Module BlankItem.
Local Open Scope string_scope.

Parameters Note Tok Doc Place HangState Hang : Type.
Parameter HangAt : HangState -> Hang.
Parameter concat : list Doc -> Doc.

Record Comments := { above : list Note; after : option string; blankBefore : bool }.
Record Word := { text : string; comments : Comments }.
Definition noWord : Word := {| text := ""; comments := {| above := []; after := None; blankBefore := false |} |}.
Parameter wordTrails wordSound : Word -> bool.

(* Fmt.Rules.Around; Rocq has no record update, so the one update the element makes is a definition. *)
Record Around := { before : bool; hoisted : bool; item : bool; col : nat; inArm : bool }.
Definition hoist (a : Around) : Around :=
  {| before := before a; hoisted := true; item := item a; col := col a; inArm := inArm a |}.
Definition next (a : Around) (b : bool) (skipped : nat) : Around :=
  {| before := b; hoisted := false; item := false; col := col a + skipped; inArm := inArm a |}.

(* Cut down from Syntax.InfixKind: the kinds outside slice 1 merged into InfixOther. *)
Inductive InfixKind := InfixBinary | InfixArrow | InfixOther.

(* Cut down from Syntax.Expr to slice 1's constructors: within1 is false on the rest. *)
Inductive Expr :=
  | Atom (kind : Tok) (word : Word)
  | Paren (opener : Word) (inner : Expr) (close : Word)
  | Tuple (opener : Word) (items : list Expr) (trailing : bool) (close : Word)
  | ListOf (opener : Word) (items : list Expr) (trailing : bool) (close : Word)
  | App (head : Expr) (arguments : list Expr)
  | Infix (kind : InfixKind) (lhs : Expr) (operator : Word) (rhs : Expr)
  | Prefix (operator : Word) (operand : Expr).

Parameter wordWithin1 : Tok -> bool.
Parameter textSpells1 : Tok -> string -> bool.
Parameters binaryText1 arrowText1 prefixText1 : string -> bool.
Parameters allWithin1 allSound : list Expr -> bool.

Fixpoint within1 (e : Expr) : bool :=
  match e with
  | Atom kind word => wordWithin1 kind && textSpells1 kind (text word)
  | Paren _ inner _ => within1 inner
  | Tuple _ items _ _ | ListOf _ items _ _ => allWithin1 items
  | App head arguments => within1 head && allWithin1 arguments
  | Infix InfixBinary l op r => within1 l && within1 r && binaryText1 (text op)
  | Infix InfixArrow l op r => within1 l && within1 r && arrowText1 (text op)
  | Infix InfixOther _ _ _ => false
  | Prefix op operand => within1 operand && prefixText1 (text op)
  end.

Fixpoint sound (e : Expr) : bool :=
  match e with
  | Atom _ word => wordSound word
  | Paren o inner c => wordSound o && sound inner && wordSound c
  | Tuple o items _ c | ListOf o items _ c => wordSound o && allSound items && wordSound c
  | App head arguments => sound head && allSound arguments
  | Infix _ l op r => sound l && wordSound op && sound r
  | Prefix op operand => wordSound op && sound operand
  end.

Fixpoint lead (e : Expr) : Word :=
  match e with
  | Atom _ word | Paren word _ _ | Tuple word _ _ _ | ListOf word _ _ _ => word
  | App head _ | Infix _ head _ _ => lead head
  | Prefix op _ => op
  end.

(* itemsWords is flat_map words. *)
Fixpoint words (e : Expr) : list Word :=
  match e with
  | Atom _ word => [word]
  | Paren o inner c => o :: words inner ++ [c]
  | Tuple o items _ c | ListOf o items _ c => o :: flat_map words items ++ [c]
  | App head arguments => words head ++ flat_map words arguments
  | Infix _ l op r => words l ++ op :: words r
  | Prefix op operand => op :: words operand
  end.

Definition firstWord (e : Expr) : Word := hd noWord (words e).
Parameter trails : Expr -> bool.

Parameter framedBy : Word -> Around -> Doc -> Doc.
Parameter leaf : Word -> Around -> nat -> Doc.
Parameter parenDoc : Word -> Expr -> Word -> Around -> Doc.
Parameter commaBracket : bool -> Word -> list Expr -> Word -> Around -> Doc.
(* Cut down from appDocs, whose Applied result the element reads only .doc of. *)
Parameter appDoc : Expr -> list Expr -> Around -> Doc.
Parameter chainLevel : Expr -> option nat.
Parameter chain : option nat -> Expr -> Word -> Expr -> Around -> Doc.
Parameter prefixGap : Word -> Expr -> Doc.

Definition framed (e : Expr) (a : Around) (doc : Doc) : Doc := framedBy (firstWord e) a doc.

(* Cut down from Fmt.Rules.Expr.el: the clauses outside slice 1 dropped. *)
Fixpoint el (e : Expr) (a : Around) : Doc :=
  match e with
  | Atom _ word => leaf word a (col a)
  | Paren o inner c => framed e a (parenDoc o inner c (hoist a))
  | Tuple o items _ c => framed e a (commaBracket false o items c (hoist a))
  | ListOf o items _ c => framed e a (commaBracket true o items c (hoist a))
  | App head arguments => framed e a (appDoc head arguments (hoist a))
  | Infix InfixBinary l op r | Infix InfixArrow l op r => framed e a (chain (chainLevel e) l op r (hoist a))
  | Infix InfixOther _ _ _ => concat []
  | Prefix op operand =>
    framed e a (concat [leaf op (hoist a) (col a); prefixGap op operand; el operand (next a (wordTrails op) 1)])
  end.

Parameter lexKind : string -> Tok.
Parameter Plain : Tok -> Prop.
Parameters isLayout isCloserText : string -> bool.
Parameter TrailsComment : Word -> Prop.
Parameter plainStart : Place -> bool.
Parameters wordStart leadStart : nat -> Place -> option nat.
Parameter openedBy : HangState -> option nat -> HangState.
Parameter Ended : HangState -> bool -> Place -> Prop.
Parameter Entered : nat -> nat -> bool -> HangState -> Place -> option nat -> Place -> Hang -> Prop.
Parameter HangLays : (string -> Tok) -> Doc -> nat -> (Place -> Hang -> Prop) -> (Place -> Hang -> Prop) -> Prop.
Parameter ElHangs : (string -> Tok) -> Doc -> nat -> nat -> bool -> bool -> (nat -> Place -> option nat) -> Prop.

Definition WordToken (t : string) : Prop :=
  prefix "--" t = false /\ isLayout t = false /\ isCloserText t = false /\ String.eqb t "," = false.

Definition LedAt (kinds : string -> Tok) (doc : Doc) (indent : nat) (bef trails : bool) (state : HangState)
  (entry : Place) : Prop :=
  HangLays kinds doc indent (Entered indent indent bef state entry (leadStart indent entry)) (fun place hang =>
    Ended (openedBy state (leadStart indent entry)) trails place /\ hang = HangAt (openedBy state (leadStart indent entry))).

Axiom wordFacts : forall kind t, (wordWithin1 kind && textSpells1 kind t) = true -> Plain (lexKind t) /\ WordToken t.
Axiom atomTrailsIs : forall kind word, trails (Atom kind word) = wordTrails word.
Axiom trailsOfSound : forall word, wordSound word = true -> TrailsComment word.
Axiom firstWordLead : forall e, within1 e = true -> firstWord e = lead e.

Axiom blankLeafHangs : forall {kinds word a key indent state entry},
  Plain (kinds (text word)) ->
  prefix "--" (text word) = false ->
  isLayout (text word) = false ->
  isCloserText (text word) = false ->
  String.eqb (text word) "," = false ->
  hoisted a = false ->
  item a = true ->
  above (comments word) = [] ->
  blankBefore (comments word) = true ->
  TrailsComment word ->
  plainStart entry = false ->
  HangLays kinds (leaf word a key) indent (Entered indent indent (before a) state entry (leadStart indent entry))
    (fun place hang => Ended (openedBy state (leadStart indent entry)) (wordTrails word) place
      /\ hang = HangAt (openedBy state (leadStart indent entry))).

Axiom blankNodeAt : forall {e word} (node : Around -> Doc) {a indent trails state entry},
  (forall a', el e a' = framedBy word a' (node a')) ->
  node (hoist a) = node a ->
  hoisted a = false ->
  item a = true ->
  above (comments word) = [] ->
  blankBefore (comments word) = true ->
  plainStart entry = false ->
  (forall inset, ElHangs lexKind (el e (hoist a)) inset inset (before a) trails wordStart) ->
  LedAt lexKind (el e a) indent (before a) trails state entry.

(* sample: blankItemHangs *)
Lemma blankItemHangs (e : Expr) (a : Around) (indent : nat) (state : HangState) (entry : Place)
  (within : within1 e = true)
  (snd : sound e = true)
  (hoisted : hoisted a = false)
  (item : item a = true)
  (unnoted : above (comments (lead e)) = [])
  (blank : blankBefore (comments (lead e)) = true)
  (fresh : plainStart entry = false)
  (hoistedHangs : forall inset, ElHangs lexKind (el e (hoist a)) inset inset (before a)
      (trails e) wordStart) :
  LedAt lexKind (el e a) indent (before a) (trails e) state entry.
Proof.
  destruct e as
    [kind word | o inner c | o items tr c | o items tr c | head args | kind l op r | op operand].
  - destruct (wordFacts kind (text word) within) as [plain [? [? [? ?]]]].
    rewrite atomTrailsIs. apply blankLeafHangs; auto using trailsOfSound.
  - now apply (blankNodeAt (word := o) (fun a' => parenDoc o inner c (hoist a'))).
  - now apply (blankNodeAt (word := o) (fun a' => commaBracket false o items c (hoist a'))).
  - now apply (blankNodeAt (word := o) (fun a' => commaBracket true o items c (hoist a'))).
  - apply (blankNodeAt (word := lead head) (fun a' => appDoc head args (hoist a'))); auto.
    intro. unfold el, framed. now rewrite firstWordLead.
  - apply (blankNodeAt (word := lead l) (fun a' => chain (chainLevel (Infix kind l op r)) l op r
      (hoist a'))); auto.
    intro. destruct kind; [| | discriminate]; unfold el, framed; now rewrite firstWordLead.
  - now apply (blankNodeAt (word := op)
      (fun a' => concat [leaf op (hoist a') (col a'); prefixGap op operand;
      el operand (next a' (wordTrails op) 1)])).
Qed.

End BlankItem.


(** * top 1: wordsCalmKeep (Fmt/CommentsKeptProof.sw) *)
Module WordsCalm.

Parameters Tok Comments : Type.
Parameter keptComments : Comments -> bool -> bool -> Comments.

Record Word := { text : string; comments : Comments }.

Definition kept (w : Word) (item closer : bool) : Word :=
  {| text := text w; comments := keptComments (comments w) item closer |}.

(* Cut down from Syntax.InfixKind: the kinds outside slice 1 merged into InfixOther. *)
Inductive InfixKind := InfixBinary | InfixArrow | InfixOther.

(* Cut down from Syntax.Expr to slice 1's constructors: within1 is false on the rest. *)
Inductive Expr :=
  | Atom (kind : Tok) (word : Word)
  | Paren (opener : Word) (inner : Expr) (close : Word)
  | Tuple (opener : Word) (items : list Expr) (trailing : bool) (close : Word)
  | ListOf (opener : Word) (items : list Expr) (trailing : bool) (close : Word)
  | App (head : Expr) (arguments : list Expr)
  | Infix (kind : InfixKind) (lhs : Expr) (operator : Word) (rhs : Expr)
  | Prefix (operator : Word) (operand : Expr).

Parameter wordWithin1 : Tok -> bool.
Parameter textSpells1 : Tok -> string -> bool.
Parameters binaryText1 arrowText1 prefixText1 isCloserText : string -> bool.
Parameter plainItem : Expr -> bool.
Parameter keeps : Word -> Word -> Prop.

(* allWithin1 is forallb within1, allClosed forallb closed, itemsWords flat_map words. *)
Fixpoint within1 (e : Expr) : bool :=
  match e with
  | Atom kind word => wordWithin1 kind && textSpells1 kind (text word)
  | Paren _ inner _ => within1 inner
  | Tuple _ items _ _ | ListOf _ items _ _ => forallb within1 items
  | App head arguments => within1 head && forallb within1 arguments
  | Infix InfixBinary l op r => within1 l && within1 r && binaryText1 (text op)
  | Infix InfixArrow l op r => within1 l && within1 r && arrowText1 (text op)
  | Infix InfixOther _ _ _ => false
  | Prefix op operand => within1 operand && prefixText1 (text op)
  end.

Fixpoint closed (e : Expr) : bool :=
  match e with
  | Atom _ _ => true
  | Paren _ inner c => isCloserText (text c) && closed inner
  | Tuple _ items _ c | ListOf _ items _ c => isCloserText (text c) && forallb closed items
  | App head arguments => closed head && forallb closed arguments
  | Infix _ l _ r => closed l && closed r
  | Prefix _ operand => closed operand
  end.

Fixpoint words (e : Expr) : list Word :=
  match e with
  | Atom _ word => [word]
  | Paren o inner c => (o :: words inner) ++ [c]
  | Tuple o items _ c | ListOf o items _ c => (o :: flat_map words items) ++ [c]
  | App head arguments => words head ++ flat_map words arguments
  | Infix _ l op r => words l ++ op :: words r
  | Prefix op operand => op :: words operand
  end.

(* calmAll, calmLead and pickItems are inlined into calm, so that it is structural; they are restated below. *)
Fixpoint calm (e : Expr) (item : bool) : Expr :=
  match e with
  | Atom kind word => Atom kind (kept word item false)
  | Paren o inner c => Paren (kept o item false) (calm inner false) (kept c false true)
  | Tuple o items comma c => Tuple (kept o item false) (map (fun x => calm x true) items) comma (kept c false true)
  | ListOf o items comma c =>
    ListOf (kept o item false)
      (if forallb plainItem items then
         match items with [] => [] | first :: rest => calm first false :: map (fun x => calm x true) rest end
       else map (fun x => calm x true) items)
      comma (kept c false true)
  | App head arguments => App (calm head item) (map (fun x => calm x false) arguments)
  | Infix kind l op r => Infix kind (calm l item) (kept op false false) (calm r false)
  | Prefix op operand => Prefix (kept op item false) (calm operand false)
  end.

Definition calmAll (item : bool) (items : list Expr) : list Expr := map (fun x => calm x item) items.
Definition calmLead (items : list Expr) : list Expr :=
  match items with [] => [] | first :: rest => calm first false :: calmAll true rest end.
Definition pickItems (plain : bool) (items : list Expr) : list Expr :=
  if plain then calmLead items else calmAll true items.

Fixpoint AllKeep (front back : list Word) : Prop :=
  match front, back with
  | [], [] => True
  | b :: more, a :: later => keeps b a /\ AllKeep more later
  | _, _ => False
  end.

Axiom keptKeeps : forall w item closer, (negb closer || isCloserText (text w)) = true -> keeps w (kept w item closer).
Axiom allKeepAppend : forall front later back after,
  AllKeep front later -> AllKeep back after -> AllKeep (front ++ back) (later ++ after).

(* The other members of wordsCalmKeep's mutual group (rule 8). *)
Axiom itemsKeepAll : forall items item, forallb within1 items = true -> forallb closed items = true ->
  AllKeep (flat_map words items) (flat_map words (calmAll item items)).
Axiom itemsKeepPick : forall plain items, forallb within1 items = true -> forallb closed items = true ->
  AllKeep (flat_map words items) (flat_map words (pickItems plain items)).

(* sample: wordsCalmKeep *)
Lemma wordsCalmKeep (e : Expr) (item : bool)
  (within : within1 e = true)
  (closes : closed e = true) :
  AllKeep (words e) (words (calm e item)).
Proof.
  revert item within closes.
  induction e as [| | | | | [] | ]; intros item within closes; simpl in *;
    rewrite ?andb_true_iff in *; intuition; try apply allKeepAppend; simpl; intuition;
    solve [apply keptKeeps; auto | apply itemsKeepAll; auto | apply itemsKeepPick; auto | eauto].
Qed.

End WordsCalm.


(** * printer 2: heldItemSeat (Fmt/BracketHangProofs.sw) *)
Module HeldItem.

Record OpenMark := { key : nat; marked : nat; least : option nat }.
Record Carry := { floor : option nat; marks : list OpenMark }.
Inductive Place := AtStart (c : nat) (k : Carry) | Broken (c : nat) (k : Carry) | Mid (c : nat) (k : Carry)
  | Held (c : nat) (k : Carry).
Record HangState := { blocks : list (option nat); top : option nat; start : bool; glue : bool }.
Inductive Hang := Opening | At (state : HangState) | Broke.

Definition floored (carry : Carry) (indent : nat) : nat :=
  match floor carry with None => indent | Some l => Nat.max indent l end.

Fixpoint inForce (bs : list (option nat)) (t : option nat) : nat :=
  match bs with
  | Some column :: _ => column
  | None :: rest => inForce rest t
  | [] => match t with Some x => x | None => 0 end
  end.

Definition itemState (outer : list (option nat)) (t : option nat) : HangState :=
  {| blocks := None :: outer; top := t; start := true; glue := false |}.

Definition plainStart (p : Place) : bool := match p with AtStart _ _ => true | _ => false end.

Definition wordStart (indent : nat) (p : Place) : option nat :=
  match p with
  | AtStart c _ | Broken c _ => Some c
  | Mid _ _ => None
  | Held c carry => Some (floored carry (Nat.max indent (c + 2)))
  end.

Definition Seated (column : nat) (before : bool) (state : HangState) (p : Place) : Prop :=
  match p with
  | AtStart c carry | Broken c carry => c = column /\ floored carry column = column
  | Mid c carry => floor carry = None /\ inForce (blocks state) (top state) <= c
  | Held c carry => before = true /\ floor carry = None /\ inForce (blocks state) (top state) <= c
  end.

Definition Room (state : HangState) (first : option nat) : Prop :=
  match first with
  | None => True
  | Some column => glue state = false /\ column > inForce (blocks state) (top state)
  end.

Definition Seat (indent column : nat) (before : bool) (state : HangState) (entry : Place) (first : option nat) :=
  Seated column before state entry /\ column <= indent /\ inForce (blocks state) (top state) <= indent
    /\ Room state first.

Definition ItemSeat (inset : nat) (outer : list (option nat)) (t : option nat) (before : bool) (p : Place)
  (hang : Hang) : Prop :=
  hang = At (itemState outer t) /\ plainStart p = false
    /\ Seat inset inset before (itemState outer t) p (wordStart inset p).

(* sample: heldItemSeat *)
Lemma heldItemSeat (inset c : nat) (outer : list (option nat)) (t : option nat) (carry : Carry)
  (floorNone : floor carry = None)
  (left : inForce outer t <= c)
  (bound : inForce outer t < inset) :
  ItemSeat inset outer t true (Held c carry) (At (itemState outer t)).
Proof.
  unfold ItemSeat, Seat, Seated, Room, wordStart, floored; simpl; rewrite floorNone.
  repeat split; auto; lia.
Qed.

End HeldItem.

(** * printer 3: stepsIfBroken (Fmt/TouchSteps.sw) *)
Module IfBroken.

Parameters Seam Touch Spacing : Type.
Parameter admitsGlue : list Spacing -> list Touch -> bool.
Parameter codeTouching : list Touch -> list Touch.

(* Cut down from std's Doc: one leaf kept as a stand-in for the rest, which this proof never reaches. *)
Inductive Doc := Chunk (t : string) | IfBroken (id : nat) (broken flat : Doc).

Parameter ChunkTouches : string -> Seam -> list Touch -> (Seam -> list Touch -> Prop) -> Prop.

Fixpoint Touches (doc : Doc) (seam : Seam) (trace : list Touch) (next : Seam -> list Touch -> Prop) : Prop :=
  match doc with
  | Chunk t => ChunkTouches t seam trace next
  | IfBroken _ broken flat => Touches broken seam trace next /\ Touches flat seam trace next
  end.

Definition Steps (doc : Doc) (pre : Seam -> Prop) (spacing : list Spacing) (post : Seam -> Prop) : Prop :=
  forall seam trace (next : Seam -> list Touch -> Prop), pre seam ->
    (forall after added, post after -> admitsGlue spacing (codeTouching added) = true -> next after (trace ++ added)) ->
    Touches doc seam trace next.

(* sample: stepsIfBroken *)
Lemma stepsIfBroken (id : nat) {broken flat : Doc} (pre : Seam -> Prop) {spacing : list Spacing}
  (post : Seam -> Prop)
  (brokenSteps : Steps broken pre spacing post)
  (flatSteps : Steps flat pre spacing post) :
  Steps (IfBroken id broken flat) pre spacing post.
Proof. intros seam trace next holds after; split; auto. Qed.

End IfBroken.

(** * printer 4: parenInnerKept (Fmt/CalmProofs.sw) *)
Module ParenInner.

Parameters Tok Doc Around Statement Comments : Type.
Parameter keptComments : Comments -> bool -> bool -> Comments.
Parameter concat : list Doc -> Doc.
Parameter Nest : nat -> Doc -> Doc.
Parameter Align : Doc -> Doc.
Parameter HardLine : Doc.

Record Word := { text : string; comments : Comments }.
Definition kept (w : Word) (item closer : bool) : Word :=
  {| text := text w; comments := keptComments (comments w) item closer |}.

Inductive InfixKind := InfixBinary | InfixArrow | InfixOther.

(* Cut down from Syntax.Expr: slice 1's constructors, and Block and If, which parenInner reads; the rest fall
   to parenInner's and calm's last clauses as these two do, and within1 is false on them. *)
Inductive Expr :=
  | Atom (kind : Tok) (word : Word)
  | Paren (opener : Word) (inner : Expr) (close : Word)
  | Tuple (opener : Word) (items : list Expr) (trailing : bool) (close : Word)
  | ListOf (opener : Word) (items : list Expr) (trailing : bool) (close : Word)
  | App (head : Expr) (arguments : list Expr)
  | Infix (kind : InfixKind) (lhs : Expr) (operator : Word) (rhs : Expr)
  | Prefix (operator : Word) (operand : Expr)
  | Block (first : Statement) (rest : list Statement) (result : Expr)
  | If (keyword : Word) (binder : option (Word * Word)) (condition : Expr) (thenKeyword : Word) (whenTrue : Expr)
      (elseKeyword : Word) (whenFalse : Expr).

Parameters within1 closed : Expr -> bool.
Parameter el : Expr -> Around -> Doc.
(* calmAll and calmItems are mutual with calm; the proof only needs calm to keep the constructor. *)
Parameter calmAll : bool -> list Expr -> list Expr.
Parameter calmItems : list Expr -> list Expr.
Axiom blockWithin : forall first rest result, within1 (Block first rest result) = false.
Axiom ifWithin : forall k b c t x e y, within1 (If k b c t x e y) = false.

Fixpoint calm (e : Expr) (item : bool) : Expr :=
  match e with
  | Atom kind word => Atom kind (kept word item false)
  | Paren o inner c => Paren (kept o item false) (calm inner false) (kept c false true)
  | Tuple o items comma c => Tuple (kept o item false) (calmAll true items) comma (kept c false true)
  | ListOf o items comma c => ListOf (kept o item false) (calmItems items) comma (kept c false true)
  | App head arguments => App (calm head item) (calmAll false arguments)
  | Infix kind l op r => Infix kind (calm l item) (kept op false false) (calm r false)
  | Prefix op operand => Prefix (kept op item false) (calm operand false)
  | other => other
  end.

Definition good (e : Expr) : bool := within1 e && closed e.

Definition parenInner (inner : Expr) (innerAround : Around) : Doc :=
  match inner with
  | Block _ _ _ => Nest 2 (concat [HardLine; el inner innerAround])
  | If _ _ _ _ _ _ _ => Align (el inner innerAround)
  | _ => el inner innerAround
  end.

(* sample: parenInnerKept *)
Lemma parenInnerKept (inner : Expr) (around : Around)
  (isGood : good inner = true)
  (each : el (calm inner false) around = el inner around) :
  parenInner (calm inner false) around = parenInner inner around.
Proof.
  unfold good in isGood; destruct inner; try exact each; rewrite ?blockWithin,
      ?ifWithin in isGood; discriminate.
Qed.

End ParenInner.

(** * printer 6: refinesAppend (Fmt/ToldDeclProofs.sw) *)
Module Refines.

Parameter Told : Type.
Parameter EntryRefines : Told -> Told -> Prop.

Fixpoint Refines (told shape : list Told) : Prop :=
  match told, shape with
  | [], [] => True
  | entry :: more, other :: rest => EntryRefines entry other /\ Refines more rest
  | _, _ => False
  end.

(* sample: refinesAppend *)
Lemma refinesAppend {one two three four : list Told}
  (front : Refines one three)
  (back : Refines two four) :
  Refines (one ++ two) (three ++ four).
Proof.
  revert three front; induction one; destruct three; simpl; intuition.
Qed.

End Refines.

(** * printer 7: notedCloserHangs (Fmt/HangProofs.sw) *)
Module NotedCloser.

Parameters Tok Doc Event Note : Type.
Parameter concat : list Doc -> Doc.
Parameter Closing : string -> Doc.
Parameter CloserLine : nat -> Doc.

Record OpenMark := { key : nat; marked : nat; least : option nat }.
Record Carry := { floor : option nat; marks : list OpenMark }.

Definition closerAt (carry : Carry) (k indent : nat) : nat :=
  match find (fun mark => key mark =? k) (marks carry) with
  | Some {| marked := m; least := Some l |} => if l <=? indent then Nat.min m indent else indent
  | _ => indent
  end.

Inductive Place := AtStart (c : nat) (k : Carry) | Broken (c : nat) (k : Carry) | Mid (c : nat) (k : Carry)
  | Held (c : nat) (k : Carry).
Definition carry (p : Place) : Carry := match p with AtStart _ k | Broken _ k | Mid _ k | Held _ k => k end.

Record HangState := { blocks : list (option nat); top : option nat; start : bool; glue : bool }.
Inductive Hang := Opening | At (state : HangState) | Broke.

Record Comments := { above : list Note; after : option string; blankBefore : bool }.
Record Word := { text : string; comments : Comments }.
Record Around := { before : bool; hoisted : bool; item : bool; col : nat; inArm : bool }.

Fixpoint inForce (bs : list (option nat)) (t : option nat) : nat :=
  match bs with
  | Some column :: _ => column
  | None :: rest => inForce rest t
  | [] => match t with Some x => x | None => 0 end
  end.

Definition leftOf (column : nat) (block : option nat) : bool :=
  match block with Some b => column <? b | None => true end.

Parameter wordTrails : Word -> bool.
Parameter leaf : Word -> Around -> nat -> Doc.
Parameter leading : Word -> Around -> nat -> list Doc.
Parameter trailing : Word -> list Doc.
Parameters isCloserText closesText isLayout : string -> bool.
Parameter isCloser : Tok -> bool.
Parameter NotesComment : list Note -> Prop.
Parameter TrailsComment : Word -> Prop.
Parameter hangOf : (string -> Tok) -> list Event -> Hang.
Parameter Lays : Doc -> nat -> Place -> list Event -> (Place -> list Event -> Prop) -> Prop.
Parameter HangLays : (string -> Tok) -> Doc -> nat -> (Place -> Hang -> Prop) -> (Place -> Hang -> Prop) -> Prop.
Parameter HangLaysAll :
  (string -> Tok) -> list Doc -> nat -> (Place -> Hang -> Prop) -> (Place -> Hang -> Prop) -> Prop.
Parameter LandsAt : nat -> Hang -> Place -> Hang -> Prop.
Parameter CloserExit : Word -> Around -> HangState -> list (option nat) -> Place -> Hang -> Prop.
Parameter CloserFold : nat -> HangState -> option nat -> list (option nat) -> Prop.

Definition noted (w : Word) : bool := negb (match above (comments w) with [] => true | _ => false end).
Definition lone (w : Word) (a : Around) : bool := negb (noted w) && before a && wordTrails w.

Definition CloserToken (kinds : string -> Tok) (t : string) : Prop :=
  isCloser (kinds t) = true /\ closesText t = true /\ isCloserText t = true /\ prefix "--" t = false
    /\ isLayout t = false.

Definition CloserSeat (indent : nat) (bef isLone : bool) (state : HangState) (p : Place) : Prop :=
  match p with
  | AtStart _ _ => False
  | Broken c k => isLone = true \/ (c = indent /\ floor k = None /\ leftOf indent (hd None (blocks state)) = true)
  | Mid c k => floor k = None /\ inForce (blocks state) (top state) <= c
  | Held c k => bef = true /\ floor k = None /\ inForce (blocks state) (top state) <= c
  end.

Definition CloserFits (k indent : nat) (block : option nat) (outside : nat) (cr : Carry) : Prop :=
  leftOf (closerAt cr k indent) block = true /\ outside <= closerAt cr k indent.

Definition CloserEntry (kinds : string -> Tok) (w : Word) (a : Around) (k indent : nat) (state : HangState)
  (block : option nat) (outer : list (option nat)) (p : Place) (hang : Hang) : Prop :=
  hang = At state /\ CloserSeat indent (before a) (lone w a) state p
    /\ ((noted w || lone w a) = true -> CloserFits k indent block (inForce outer (top state)) (carry p)).

Axiom hangsBy : forall {kinds doc indent} {pre post : Place -> Hang -> Prop},
  (forall p trace (next : Place -> list Event -> Prop), pre p (hangOf kinds trace) ->
    (forall after later, post after (hangOf kinds later) -> next after later) -> Lays doc indent p trace next) ->
  HangLays kinds doc indent pre post.
Axiom laysBy : forall {kinds doc indent} {pre post : Place -> Hang -> Prop},
  HangLays kinds doc indent pre post ->
  forall p trace (next : Place -> list Event -> Prop), pre p (hangOf kinds trace) ->
  (forall l later, post l (hangOf kinds later) -> next l later) -> Lays doc indent p trace next.
Axiom hangsConcat : forall {kinds docs indent pre post},
  HangLaysAll kinds docs indent pre post -> HangLays kinds (concat docs) indent pre post.
Axiom hangsAppend : forall {kinds front back indent pre middle post},
  HangLaysAll kinds front indent pre middle -> HangLaysAll kinds back indent middle post ->
  HangLaysAll kinds (front ++ back) indent pre post.
Axiom closerLeadingHangs : forall kinds w a k indent state entry note rest,
  hoisted a = false -> above (comments w) = note :: rest -> isCloserText (text w) = true ->
  NotesComment (note :: rest) ->
  HangLaysAll kinds (leading w a k) indent
    (fun p hang => p = entry /\ hang = At state /\ CloserSeat indent (before a) false state entry)
    (LandsAt (closerAt (carry entry) k indent) (At state)).
Axiom closerAtLineHangs : forall kinds w a indent column state block outer,
  CloserToken kinds (text w) -> CloserFold indent state block outer -> TrailsComment w ->
  leftOf column block = true -> inForce outer (top state) <= column ->
  HangLaysAll kinds (Closing (text w) :: trailing w) indent (LandsAt column (At state)) (CloserExit w a state outer).
Axiom closerLeafIs : forall w a k, isCloserText (text w) = true ->
  leaf w a k = concat (leading w a k ++ (if lone w a then [CloserLine k] else []) ++ [Closing (text w)] ++ trailing w).

(* sample: notedCloserHangs *)
Lemma notedCloserHangs (kinds : string -> Tok) (w : Word) (a : Around) (k indent : nat)
    (state : HangState)
  (block : option nat) (outer : list (option nat)) (note : Note) (rest : list Note)
  (token : CloserToken kinds (text w))
  (fold : CloserFold indent state block outer)
  (isHoisted : hoisted a = false)
  (isNoted : above (comments w) = note :: rest)
  (notes : NotesComment (note :: rest))
  (trailed : TrailsComment w) :
  HangLays kinds (leaf w a k) indent (CloserEntry kinds w a k indent state block outer)
      (CloserExit w a state outer).
Proof.
  assert (closer : isCloserText (text w) = true) by apply token.
  assert (isLone : lone w a = false) by (unfold lone, noted; now rewrite isNoted).
  rewrite (closerLeafIs w a k closer), isLone.
  unfold CloserEntry; apply hangsBy; intros p trace next [folded [seat fits]] after.
  rewrite isLone in seat. unfold CloserFits in fits.
  destruct fits as [left right]; [unfold noted; now rewrite isNoted |].
  refine (laysBy (hangsConcat (hangsAppend
    (closerLeadingHangs kinds w a k indent state p note rest isHoisted isNoted closer notes)
    (closerAtLineHangs kinds w a indent _ state block outer token fold trailed left right))) p
        trace next _ after).
  repeat split; auto.
Qed.

End NotedCloser.

(** * printer 8: anyHangsOf (Fmt/ElementsProofs.sw) *)
Module AnyHangs.

Parameters Expr Word Around Doc Tok : Type.
Parameters before item : Around -> bool.
Parameter plainAt : Expr -> Around -> bool.
Parameter trails : Expr -> bool.
Parameter el : Expr -> Around -> Doc.
Parameter inChain : Expr -> option nat -> bool.
Parameter lead : Expr -> Word.
Parameter leadsLine : Word -> Around -> bool.
Parameter lexKind : string -> Tok.
Parameter HangsAt : (string -> Tok) -> bool -> bool -> Doc -> Prop.
Parameter Links : (string -> Tok) -> bool -> option nat -> bool -> Expr -> Around -> bool -> Prop.

Definition AnyFacts (e : Expr) : Prop :=
  (forall a, plainAt e a = true -> HangsAt lexKind (before a) (trails e) (el e a))
    /\ (forall level first a, ((inChain e level && negb (item a)) || plainAt e a) = true ->
      Links lexKind (inChain e level && leadsLine (lead e) a) level first e a (trails e)).

(* sample: anyHangsOf *)
Lemma anyHangsOf (e : Expr)
  (facts : AnyFacts e) (a : Around)
  (plain : plainAt e a = true) :
  HangsAt lexKind (before a) (trails e) (el e a).
Proof. now apply facts. Qed.

End AnyHangs.

(** * printer 10: placedSteps (Fmt/TouchProofs.sw) *)
Module Placed.

Parameters Doc Spacing Word : Type.
Parameter Displaced : Doc -> Doc.
Parameter admits : Spacing -> bool -> bool.
Parameter admitsWord : Spacing -> Word -> bool.
Parameter isComment : string -> bool.

(* Cut down from Fmt.TouchSteps.Seam: Along's argument stands for the word before. *)
Inductive Seam := Begun | Along (w : Word) | Awaiting (w : Word) (comment : string).

Parameter Quiet : Seam -> Prop.
Parameter Steps : Doc -> (Seam -> Prop) -> list Spacing -> (Seam -> Prop) -> Prop.

Definition Fits (bef : bool) (first : Spacing) (seam : Seam) : Prop :=
  match seam with
  | Begun => admits first false = true
  | Along w => admitsWord first w = true
  | Awaiting _ comment => bef = true /\ admits first false = true /\ isComment comment = true
  end.

Definition Loose (first : Spacing) : Prop := admits first false = true.

Axiom fitsQuiet : forall bef first seam, Fits bef first seam -> Quiet seam.
Axiom stepsDisplaced : forall {inner} (pre : Seam -> Prop) {spacing} (post : Seam -> Prop),
  Steps inner pre spacing post -> pre Begun -> (forall seam, pre seam -> Quiet seam) ->
  Steps (Displaced inner) pre spacing post.

(* sample: placedSteps *)
Lemma placedSteps (displaced : bool) (doc : Doc) (first : Spacing) (spacing : list Spacing)
    (post : Seam -> Prop)
  (inner : Steps doc (Fits true first) spacing post)
  (fresh : displaced = true -> Loose first) :
  Steps (if displaced then Displaced doc else doc) (Fits true first) spacing post.
Proof. destruct displaced; auto. apply stepsDisplaced; eauto using fitsQuiet. now apply fresh. Qed.

End Placed.

(** * printer 11: statementsWalk (Fmt/BlankProofs.sw) *)
Module StatementsWalk.

Parameters Let_ Attributes Header DefBody Expr Pure : Type.
Parameter meaningPure : Pure.
Parameter blankLet : Let_ -> Let_.
Parameter blankBody : DefBody -> DefBody.
Parameter walkLet : Pure -> Let_ -> Let_.
Parameter walkAttributes : Pure -> list Attributes -> list Attributes.
Parameter walkHeader : Pure -> Header -> Header.
Parameter walkDefBody : Pure -> DefBody -> DefBody.
Parameter walkExpr : Expr -> Pure -> Expr.

Inductive Statement :=
  | LetStatement (binding : Let_)
  | LocalDef (attributes : list Attributes) (header : Header) (body : DefBody)
  | ExprStatement (value : Expr).

Definition blank (s : Statement) : Statement :=
  match s with
  | LetStatement binding => LetStatement (blankLet binding)
  | LocalDef attributes header body => LocalDef attributes header (blankBody body)
  | ExprStatement value => ExprStatement value
  end.

Definition blankStatements (ss : list Statement) : list Statement := map blank ss.

Definition walkStatement (on : Pure) (s : Statement) : Statement :=
  match s with
  | LetStatement binding => LetStatement (walkLet on binding)
  | LocalDef attributes header body =>
    LocalDef (walkAttributes on attributes) (walkHeader on header) (walkDefBody on body)
  | ExprStatement value => ExprStatement (walkExpr value on)
  end.

Definition walkStatements (on : Pure) (ss : list Statement) : list Statement := map (walkStatement on) ss.

Axiom letWalk : forall binding, blankLet (walkLet meaningPure (blankLet binding)) = blankLet (walkLet meaningPure binding).
Axiom defBodyWalk : forall body,
  blankBody (walkDefBody meaningPure (blankBody body)) = blankBody (walkDefBody meaningPure body).

(* sample: statementsWalk *)
Lemma statementsWalk (statements : list Statement) :
  blankStatements (walkStatements meaningPure (blankStatements statements))
    = blankStatements (walkStatements meaningPure statements).
Proof.
  induction statements as [| [] rest IH]; simpl; f_equal; auto.
  - now rewrite letWalk.
  - now rewrite defBodyWalk.
Qed.

End StatementsWalk.

(** * top 2: firstThreeKeepMeaning (Fmt/MeaningProofs.sw) *)
Module FirstThree.

Parameters SourceFile Meaning : Type.
Parameters withForall withoutTrailingCommas withoutSpareBrackets : SourceFile -> SourceFile.
Parameter meaning : SourceFile -> Meaning.
Axiom forallKeepsFile : forall file, meaning (withForall file) = meaning file.
Axiom commaKeepsFile : forall file, meaning (withoutTrailingCommas file) = meaning file.
Axiom bracketKeepsFile : forall file, meaning (withoutSpareBrackets file) = meaning file.

(* sample: firstThreeKeepMeaning *)
Lemma firstThreeKeepMeaning (file : SourceFile) :
  meaning (withoutSpareBrackets (withoutTrailingCommas (withForall file))) = meaning file.
Proof. now rewrite bracketKeepsFile, commaKeepsFile, forallKeepsFile. Qed.

End FirstThree.

(** * top 3: witnessUnreturned (Fmt/TopStatements.sw) *)
Module Witness.

Parameters Lexed SourceFile Decl Leaf : Type.
Parameters leaves settledOnce : Lexed -> list Leaf.
Parameter lex : string -> string + Lexed.
Parameter leavesWithin1 : list Leaf -> bool.
Parameter parseFile : list Leaf -> string + SourceFile.
Parameter within1 : SourceFile -> bool.
Parameter tidy1 : SourceFile -> SourceFile.
Parameter printed1 : SourceFile -> string.
Parameter unreturned : SourceFile -> bool.
Parameter decls : SourceFile -> list Decl.
Parameter declUnreturned : Decl -> bool.
Parameter formatWithin1 : string -> string + string.
Parameters witnessSource witnessOut : string.

Definition Formats1 (source out : string) (lexed : Lexed) (parsed : SourceFile) : Prop :=
  lex source = inr lexed /\ leavesWithin1 (leaves lexed) = true /\ parseFile (settledOnce lexed) = inr parsed
    /\ within1 parsed = true /\ out = printed1 (tidy1 parsed).

Axiom witnessFormats : formatWithin1 witnessSource = inr witnessOut.
Axiom formatsOf : forall source out, formatWithin1 source = inr out ->
  exists lexed parsed, Formats1 source out lexed parsed.
Axiom tidiedDeclsUnreturned1 : forall source lexed parsed, lex source = inr lexed ->
  leavesWithin1 (leaves lexed) = true -> parseFile (settledOnce lexed) = inr parsed -> within1 parsed = true ->
  forallb declUnreturned (decls (tidy1 parsed)) = true.
Axiom tidiedUnreturned1 : forall source lexed parsed, lex source = inr lexed ->
  leavesWithin1 (leaves lexed) = true -> parseFile (settledOnce lexed) = inr parsed -> within1 parsed = true ->
  unreturned (tidy1 parsed) = true.

(* sample: witnessUnreturned *)
Lemma witnessUnreturned : exists (lexed : Lexed) (parsed : SourceFile),
    unreturned (tidy1 parsed) = true
  /\ forallb declUnreturned (decls (tidy1 parsed)) = true.
Proof.
  destruct (formatsOf _ _ witnessFormats) as (lexed & parsed & lexes & lvs & parses & within & _).
  exists lexed, parsed; eauto using tidiedUnreturned1, tidiedDeclsUnreturned1.
Qed.

End Witness.
