/- SW-4540, batch C of SW-4537: the printer (printer 2 to 11) and the top (top 1 to 3), in Lean 4 (core only).
   Counted theorems follow a `-- sample:` line; everything else is uncounted support (cut-down definitions, and
   lemmas the Stitchwort proof names, as axioms). Check: nix shell nixpkgs#lean4 -c lean BatchC.lean -/

/-! ## printer 5: `exprBlanks` (Fmt/TraverseFail.sw) -/
namespace ExprBlanks

/- The node types below `Expr` are mutual with it in Stitchwort; the drawn theorem reaches them only through
   their own `…Blanks` theorems (rule 8), so they and their walks, blankings and traversals are opaque. -/
axiom Word : Type
axiom Comments : Type
axiom Tok : Type
axiom InfixKind : Type
axiom BindingKind : Type
axiom FactsKind : Type
axiom Param : Type
axiom Piece : Type
axiom Scrutinee : Type
axiom Arm : Type
axiom Group : Type
axiom Row : Type
axiom Statement : Type
axiom Let : Type
axiom HandlerClause : Type
axiom InductArm : Type
axiom CalcStep : Type
axiom Rules : Type
axiom Word.blank : Word → Word
axiom Comments.none : Comments

inductive Expr
  | Atom (kind : Tok) (word : Word)
  | Paren (opener : Word) (inner : Expr) (close : Word)
  | Unit (opener : Word) (close : Word)
  | Universe (keyword : Word) (level : Word)
  | Include (keyword : Word) (path : Word)
  | Tuple (opener : Word) (items : List Expr) (trailingComma : Bool) (close : Word)
  | ListOf (opener : Word) (items : List Expr) (trailingComma : Bool) (close : Word)
  | Spread (dots : Word) (list : Expr)
  | Record (opener : Word) (base : Option (Expr × Word)) (fields : List Expr) (trailingComma : Bool) (close : Word)
  | RecordField (name : Word) (equals : Word) (value : Expr)
  | CtorFields (ctor : Expr) (record : Expr)
  | App (head : Expr) (arguments : List Expr)
  | NamedArg (opener : Word) (name : Word) (colonEq : Word) (value : Expr) (close : Word)
  | FieldAccess (target : Option Expr) (dot : Word) (field : Word)
  | Section (body : Expr)
  | OperatorSection (opener : Word) (left : Option Expr) (operator : Word) (right : Option Expr) (close : Word)
  | Infix (kind : InfixKind) (left : Expr) (operator : Word) (right : Expr)
  | Chain (first : Expr) (rest : List (Word × Expr))
  | Prefix (operator : Word) (operand : Expr)
  | Binding (kind : BindingKind) (keyword : Option Word) (params : List Param) (arrow : Word) (body : Expr)
  | If (keyword : Word) (binder : Option (Word × Word)) (condition : Expr) (thenKeyword : Word)
      (whenTrue : Expr) (elseKeyword : Word) (whenFalse : Expr)
  | Annotation (opener : Word) (value : Expr) (colon : Word) (annotation : Expr) (close : Word)
  | Interpolated (pieces : List Piece)
  | Match (keyword : Word) (scrutinees : List Scrutinee) (withKeyword : Word) (arms : List Arm)
  | ClauseLambda (keyword : Word) (word : Option Word) (arms : List Arm)
  | Facts (kind : FactsKind) (keyword : Word) (facts : Expr)
  | FunctionType (binder : Group) (arrow : Word) (result : Expr)
  | Effect (row : Row) (result : Expr)
  | Block (first : Statement) (rest : List Statement) (result : Expr)
  | LetIn (binding : Let) (semicolon : Comments) (body : Expr)
  | Handle (keyword : Comments) (computation : Expr) (withKeyword : Comments) (clauses : List HandlerClause)
  | Reify (keyword : Comments) (reify : Comments) (computation : Expr) (withKeyword : Comments)
      (clauses : List HandlerClause)
  | Induct (keyword : Comments) (induct : Comments) (call : Expr) (withKeyword : Comments)
      (arms : List InductArm)
  | Calc (keyword : Comments) (first : Expr) (steps : List CalcStep)
  | Rewrite (keyword : Comments) (rules : Rules) (target : Option (Comments × Expr))
      (body : Option (Comments × Expr))
  | Cases (keyword : Comments) (targets : List Word) (body : Option (Comments × Expr))
  | Walk (keyword : Comments) (items : Expr) (body : Option (Comments × Expr))

/-- Cut down from `Fmt.Walk.Pure` and `Syntax.Steps`: only the `expr` step is kept; the others reach the
    proof only inside the opaque walks and traversals of the other node types. -/
structure Pure where
  expr : Expr → Expr

structure Steps where
  expr : Expr → Except String Expr

noncomputable section

axiom walkExprs : Pure → List Expr → List Expr
axiom walkBefore : Pure → Option (Expr × Word) → Option (Expr × Word)
axiom walkOptional : Pure → Option Expr → Option Expr
axiom walkLinks : Pure → List (Word × Expr) → List (Word × Expr)
axiom walkParams : Pure → List Param → List Param
axiom walkPieces : Pure → List Piece → List Piece
axiom walkScrutinees : Pure → List Scrutinee → List Scrutinee
axiom walkArms : Pure → List Arm → List Arm
axiom walkGroup : Pure → Group → Group
axiom walkRow : Pure → Row → Row
axiom walkStatement : Pure → Statement → Statement
axiom walkStatements : Pure → List Statement → List Statement
axiom walkLet : Pure → Let → Let
axiom walkClauses : Pure → List HandlerClause → List HandlerClause
axiom walkInductArms : Pure → List InductArm → List InductArm
axiom walkSteps : Pure → List CalcStep → List CalcStep
axiom walkRules : Pure → Rules → Rules
axiom walkAfter : Pure → Option (Comments × Expr) → Option (Comments × Expr)

axiom traverseExprs : Steps → List Expr → Except String (List Expr)
axiom traverseBefore : Steps → Option (Expr × Word) → Except String (Option (Expr × Word))
axiom traverseOptional : Steps → Option Expr → Except String (Option Expr)
axiom traverseLinks : Steps → List (Word × Expr) → Except String (List (Word × Expr))
axiom traverseParams : Steps → List Param → Except String (List Param)
axiom traversePieces : Steps → List Piece → Except String (List Piece)
axiom traverseScrutinees : Steps → List Scrutinee → Except String (List Scrutinee)
axiom traverseArms : Steps → List Arm → Except String (List Arm)
axiom traverseGroup : Steps → Group → Except String Group
axiom traverseRow : Steps → Row → Except String Row
axiom traverseStatement : Steps → Statement → Except String Statement
axiom traverseStatements : Steps → List Statement → Except String (List Statement)
axiom traverseLet : Steps → Let → Except String Let
axiom traverseClauses : Steps → List HandlerClause → Except String (List HandlerClause)
axiom traverseInductArms : Steps → List InductArm → Except String (List InductArm)
axiom traverseSteps : Steps → List CalcStep → Except String (List CalcStep)
axiom traverseRules : Steps → Rules → Except String Rules
axiom traverseAfter : Steps → Option (Comments × Expr) → Except String (Option (Comments × Expr))

axiom blankBase : Option (Expr × Word) → Option (Expr × Word)
axiom blankLinks : List (Word × Expr) → List (Word × Expr)
axiom blankParams : List Param → List Param
axiom blankPair : Option (Word × Word) → Option (Word × Word)
axiom blankPieces : List Piece → List Piece
axiom blankScrutinees : List Scrutinee → List Scrutinee
axiom blankArms : List Arm → List Arm
axiom Group.blank : Group → Group
axiom Row.blank : Row → Row
axiom Statement.blank : Statement → Statement
axiom blankStatements : List Statement → List Statement
axiom Let.blank : Let → Let
axiom blankClauses : List HandlerClause → List HandlerClause
axiom blankInductArms : List InductArm → List InductArm
axiom blankCalcSteps : List CalcStep → List CalcStep
axiom Rules.blank : Rules → Rules
axiom blankAfter : Option (Comments × Expr) → Option (Comments × Expr)
axiom blankWords : List Word → List Word

def blankExpr : Expr → Expr
  | .Atom kind word => .Atom kind word.blank
  | .Paren o inner c => .Paren o.blank inner c.blank
  | .Unit o c => .Unit o.blank c.blank
  | .Universe keyword level => .Universe keyword.blank level.blank
  | .Include keyword path => .Include keyword.blank path.blank
  | .Tuple o items comma c => .Tuple o.blank items comma c.blank
  | .ListOf o items comma c => .ListOf o.blank items comma c.blank
  | .Spread dots list => .Spread dots.blank list
  | .Record o base fields comma c => .Record o.blank (blankBase base) fields comma c.blank
  | .RecordField name equals value => .RecordField name.blank equals.blank value
  | .NamedArg o name colonEq value c => .NamedArg o.blank name.blank colonEq.blank value c.blank
  | .FieldAccess target dot field => .FieldAccess target dot.blank field.blank
  | .OperatorSection o left operator right c => .OperatorSection o.blank left operator.blank right c.blank
  | .Infix kind left operator right => .Infix kind left operator.blank right
  | .Chain first rest => .Chain first (blankLinks rest)
  | .Prefix operator operand => .Prefix operator.blank operand
  | .Binding kind keyword params arrow body =>
    .Binding kind (keyword.map Word.blank) (blankParams params) arrow.blank body
  | .If keyword binder condition thenKeyword whenTrue elseKeyword whenFalse =>
    .If keyword.blank (blankPair binder) condition thenKeyword.blank whenTrue elseKeyword.blank whenFalse
  | .Annotation o value colon annotation c => .Annotation o.blank value colon.blank annotation c.blank
  | .Interpolated pieces => .Interpolated (blankPieces pieces)
  | .Match keyword scrutinees withKeyword arms =>
    .Match keyword.blank (blankScrutinees scrutinees) withKeyword.blank (blankArms arms)
  | .ClauseLambda keyword word arms => .ClauseLambda keyword.blank (word.map Word.blank) (blankArms arms)
  | .Facts kind keyword facts => .Facts kind keyword.blank facts
  | .FunctionType binder arrow result => .FunctionType binder.blank arrow.blank result
  | .Effect row result => .Effect row.blank result
  | .Block first rest result => .Block first.blank (blankStatements rest) result
  | .LetIn binding _ body => .LetIn binding.blank Comments.none body
  | .Handle _ computation _ clauses => .Handle Comments.none computation Comments.none (blankClauses clauses)
  | .Reify _ _ computation _ clauses =>
    .Reify Comments.none Comments.none computation Comments.none (blankClauses clauses)
  | .Induct _ _ call _ arms => .Induct Comments.none Comments.none call Comments.none (blankInductArms arms)
  | .Calc _ first steps => .Calc Comments.none first (blankCalcSteps steps)
  | .Rewrite _ rules target body => .Rewrite Comments.none rules.blank (blankAfter target) (blankAfter body)
  | .Cases _ targets body => .Cases Comments.none (blankWords targets) (blankAfter body)
  | .Walk _ items body => .Walk Comments.none items (blankAfter body)
  | other => other

abbrev blankPure : Pure := { expr := blankExpr }

def Expr.walk (on : Pure) : Expr → Expr
  | .Atom kind word => on.expr (.Atom kind word)
  | .Paren o inner c => on.expr (.Paren o (inner.walk on) c)
  | .Unit o c => on.expr (.Unit o c)
  | .Universe keyword level => on.expr (.Universe keyword level)
  | .Include keyword path => on.expr (.Include keyword path)
  | .Tuple o items comma c => on.expr (.Tuple o (walkExprs on items) comma c)
  | .ListOf o items comma c => on.expr (.ListOf o (walkExprs on items) comma c)
  | .Spread dots list => on.expr (.Spread dots (list.walk on))
  | .Record o base fields comma c => on.expr (.Record o (walkBefore on base) (walkExprs on fields) comma c)
  | .RecordField name equals value => on.expr (.RecordField name equals (value.walk on))
  | .CtorFields ctor record => on.expr (.CtorFields (ctor.walk on) (record.walk on))
  | .App head arguments => on.expr (.App (head.walk on) (walkExprs on arguments))
  | .NamedArg o name colonEq value c => on.expr (.NamedArg o name colonEq (value.walk on) c)
  | .FieldAccess target dot field => on.expr (.FieldAccess (walkOptional on target) dot field)
  | .Section body => on.expr (.Section (body.walk on))
  | .OperatorSection o left operator right c =>
    on.expr (.OperatorSection o (walkOptional on left) operator (walkOptional on right) c)
  | .Infix kind left operator right => on.expr (.Infix kind (left.walk on) operator (right.walk on))
  | .Chain first rest => on.expr (.Chain (first.walk on) (walkLinks on rest))
  | .Prefix operator operand => on.expr (.Prefix operator (operand.walk on))
  | .Binding kind keyword params arrow body =>
    on.expr (.Binding kind keyword (walkParams on params) arrow (body.walk on))
  | .If keyword binder condition thenKeyword whenTrue elseKeyword whenFalse =>
    on.expr (.If keyword binder (condition.walk on) thenKeyword (whenTrue.walk on) elseKeyword (whenFalse.walk on))
  | .Annotation o value colon annotation c => on.expr (.Annotation o (value.walk on) colon (annotation.walk on) c)
  | .Interpolated pieces => on.expr (.Interpolated (walkPieces on pieces))
  | .Match keyword scrutinees withKeyword arms =>
    on.expr (.Match keyword (walkScrutinees on scrutinees) withKeyword (walkArms on arms))
  | .ClauseLambda keyword word arms => on.expr (.ClauseLambda keyword word (walkArms on arms))
  | .Facts kind keyword facts => on.expr (.Facts kind keyword (facts.walk on))
  | .FunctionType binder arrow result => on.expr (.FunctionType (walkGroup on binder) arrow (result.walk on))
  | .Effect row result => on.expr (.Effect (walkRow on row) (result.walk on))
  | .Block first rest result =>
    on.expr (.Block (walkStatement on first) (walkStatements on rest) (result.walk on))
  | .LetIn binding semicolon body => on.expr (.LetIn (walkLet on binding) semicolon (body.walk on))
  | .Handle keyword computation withKeyword clauses =>
    on.expr (.Handle keyword (computation.walk on) withKeyword (walkClauses on clauses))
  | .Reify keyword reify computation withKeyword clauses =>
    on.expr (.Reify keyword reify (computation.walk on) withKeyword (walkClauses on clauses))
  | .Induct keyword induct call withKeyword arms =>
    on.expr (.Induct keyword induct (call.walk on) withKeyword (walkInductArms on arms))
  | .Calc keyword first steps => on.expr (.Calc keyword (first.walk on) (walkSteps on steps))
  | .Rewrite keyword rules target body =>
    on.expr (.Rewrite keyword (walkRules on rules) (walkAfter on target) (walkAfter on body))
  | .Cases keyword targets body => on.expr (.Cases keyword targets (walkAfter on body))
  | .Walk keyword items body => on.expr (.Walk keyword (items.walk on) (walkAfter on body))

def Expr.traverse (on : Steps) : Expr → Except String Expr
  | .Atom kind word => on.expr (.Atom kind word)
  | .Paren o inner c => do on.expr (.Paren o (← inner.traverse on) c)
  | .Unit o c => on.expr (.Unit o c)
  | .Universe keyword level => on.expr (.Universe keyword level)
  | .Include keyword path => on.expr (.Include keyword path)
  | .Tuple o items comma c => do on.expr (.Tuple o (← traverseExprs on items) comma c)
  | .ListOf o items comma c => do on.expr (.ListOf o (← traverseExprs on items) comma c)
  | .Spread dots list => do on.expr (.Spread dots (← list.traverse on))
  | .Record o base fields comma c =>
    do on.expr (.Record o (← traverseBefore on base) (← traverseExprs on fields) comma c)
  | .RecordField name equals value => do on.expr (.RecordField name equals (← value.traverse on))
  | .CtorFields ctor record => do on.expr (.CtorFields (← ctor.traverse on) (← record.traverse on))
  | .App head arguments => do on.expr (.App (← head.traverse on) (← traverseExprs on arguments))
  | .NamedArg o name colonEq value c => do on.expr (.NamedArg o name colonEq (← value.traverse on) c)
  | .FieldAccess target dot field => do on.expr (.FieldAccess (← traverseOptional on target) dot field)
  | .Section body => do on.expr (.Section (← body.traverse on))
  | .OperatorSection o left operator right c =>
    do on.expr (.OperatorSection o (← traverseOptional on left) operator (← traverseOptional on right) c)
  | .Infix kind left operator right =>
    do on.expr (.Infix kind (← left.traverse on) operator (← right.traverse on))
  | .Chain first rest => do on.expr (.Chain (← first.traverse on) (← traverseLinks on rest))
  | .Prefix operator operand => do on.expr (.Prefix operator (← operand.traverse on))
  | .Binding kind keyword params arrow body =>
    do on.expr (.Binding kind keyword (← traverseParams on params) arrow (← body.traverse on))
  | .If keyword binder condition thenKeyword whenTrue elseKeyword whenFalse =>
    do on.expr (.If keyword binder (← condition.traverse on) thenKeyword (← whenTrue.traverse on) elseKeyword
      (← whenFalse.traverse on))
  | .Annotation o value colon annotation c =>
    do on.expr (.Annotation o (← value.traverse on) colon (← annotation.traverse on) c)
  | .Interpolated pieces => do on.expr (.Interpolated (← traversePieces on pieces))
  | .Match keyword scrutinees withKeyword arms =>
    do on.expr (.Match keyword (← traverseScrutinees on scrutinees) withKeyword (← traverseArms on arms))
  | .ClauseLambda keyword word arms => do on.expr (.ClauseLambda keyword word (← traverseArms on arms))
  | .Facts kind keyword facts => do on.expr (.Facts kind keyword (← facts.traverse on))
  | .FunctionType binder arrow result =>
    do on.expr (.FunctionType (← traverseGroup on binder) arrow (← result.traverse on))
  | .Effect row result => do on.expr (.Effect (← traverseRow on row) (← result.traverse on))
  | .Block first rest result =>
    do on.expr (.Block (← traverseStatement on first) (← traverseStatements on rest) (← result.traverse on))
  | .LetIn binding semicolon body =>
    do on.expr (.LetIn (← traverseLet on binding) semicolon (← body.traverse on))
  | .Handle keyword computation withKeyword clauses =>
    do on.expr (.Handle keyword (← computation.traverse on) withKeyword (← traverseClauses on clauses))
  | .Reify keyword reify computation withKeyword clauses =>
    do on.expr (.Reify keyword reify (← computation.traverse on) withKeyword (← traverseClauses on clauses))
  | .Induct keyword induct call withKeyword arms =>
    do on.expr (.Induct keyword induct (← call.traverse on) withKeyword (← traverseInductArms on arms))
  | .Calc keyword first steps => do on.expr (.Calc keyword (← first.traverse on) (← traverseSteps on steps))
  | .Rewrite keyword rules target body =>
    do on.expr (.Rewrite keyword (← traverseRules on rules) (← traverseAfter on target) (← traverseAfter on body))
  | .Cases keyword targets body => do on.expr (.Cases keyword targets (← traverseAfter on body))
  | .Walk keyword items body => do on.expr (.Walk keyword (← items.traverse on) (← traverseAfter on body))

abbrev runExpr (on : Steps) (input : Expr) : Except String Expr := input.traverse on

/-- Cut down from `Fmt.TraverseFail.Blanks`: only the `expr` field, the one the proof reads. -/
structure Blanks (on : Steps) : Prop where
  expr : ∀ z : Expr, on.expr (z.walk blankPure) = (·.walk blankPure) <$> on.expr z

/- The other members of `exprBlanks`' mutual group (rule 8), on the forms their inputs take in a blanked tree. -/
axiom exprsBlanks (on : Steps) (deaf : Blanks on) (z : List Expr) :
  traverseExprs on (walkExprs blankPure z) = walkExprs blankPure <$> traverseExprs on z
axiom beforeBlanks (on : Steps) (deaf : Blanks on) (z : Option (Expr × Word)) :
  traverseBefore on (blankBase (walkBefore blankPure z)) = (blankBase ∘ walkBefore blankPure) <$> traverseBefore on z
axiom optionalBlanks (on : Steps) (deaf : Blanks on) (z : Option Expr) :
  traverseOptional on (walkOptional blankPure z) = walkOptional blankPure <$> traverseOptional on z
axiom linksBlanks (on : Steps) (deaf : Blanks on) (z : List (Word × Expr)) :
  traverseLinks on (blankLinks (walkLinks blankPure z)) = (blankLinks ∘ walkLinks blankPure) <$> traverseLinks on z
axiom paramsBlanks (on : Steps) (deaf : Blanks on) (z : List Param) :
  traverseParams on (blankParams (walkParams blankPure z)) =
    (blankParams ∘ walkParams blankPure) <$> traverseParams on z
axiom piecesBlanks (on : Steps) (deaf : Blanks on) (z : List Piece) :
  traversePieces on (blankPieces (walkPieces blankPure z)) =
    (blankPieces ∘ walkPieces blankPure) <$> traversePieces on z
axiom scrutineesBlanks (on : Steps) (deaf : Blanks on) (z : List Scrutinee) :
  traverseScrutinees on (blankScrutinees (walkScrutinees blankPure z)) =
    (blankScrutinees ∘ walkScrutinees blankPure) <$> traverseScrutinees on z
axiom armsBlanks (on : Steps) (deaf : Blanks on) (z : List Arm) :
  traverseArms on (blankArms (walkArms blankPure z)) = (blankArms ∘ walkArms blankPure) <$> traverseArms on z
axiom groupBlanks (on : Steps) (deaf : Blanks on) (z : Group) :
  traverseGroup on (walkGroup blankPure z).blank = (Group.blank ∘ walkGroup blankPure) <$> traverseGroup on z
axiom rowBlanks (on : Steps) (deaf : Blanks on) (z : Row) :
  traverseRow on (walkRow blankPure z).blank = (Row.blank ∘ walkRow blankPure) <$> traverseRow on z
axiom statementBlanks (on : Steps) (deaf : Blanks on) (z : Statement) :
  traverseStatement on (walkStatement blankPure z).blank =
    (Statement.blank ∘ walkStatement blankPure) <$> traverseStatement on z
axiom statementsBlanks (on : Steps) (deaf : Blanks on) (z : List Statement) :
  traverseStatements on (blankStatements (walkStatements blankPure z)) =
    (blankStatements ∘ walkStatements blankPure) <$> traverseStatements on z
axiom letBlanks (on : Steps) (deaf : Blanks on) (z : Let) :
  traverseLet on (walkLet blankPure z).blank = (Let.blank ∘ walkLet blankPure) <$> traverseLet on z
axiom clausesBlanks (on : Steps) (deaf : Blanks on) (z : List HandlerClause) :
  traverseClauses on (blankClauses (walkClauses blankPure z)) =
    (blankClauses ∘ walkClauses blankPure) <$> traverseClauses on z
axiom inductArmsBlanks (on : Steps) (deaf : Blanks on) (z : List InductArm) :
  traverseInductArms on (blankInductArms (walkInductArms blankPure z)) =
    (blankInductArms ∘ walkInductArms blankPure) <$> traverseInductArms on z
axiom calcStepsBlanks (on : Steps) (deaf : Blanks on) (z : List CalcStep) :
  traverseSteps on (blankCalcSteps (walkSteps blankPure z)) =
    (blankCalcSteps ∘ walkSteps blankPure) <$> traverseSteps on z
axiom rulesBlanks (on : Steps) (deaf : Blanks on) (z : Rules) :
  traverseRules on (walkRules blankPure z).blank = (Rules.blank ∘ walkRules blankPure) <$> traverseRules on z
axiom afterBlanks (on : Steps) (deaf : Blanks on) (z : Option (Comments × Expr)) :
  traverseAfter on (blankAfter (walkAfter blankPure z)) = (blankAfter ∘ walkAfter blankPure) <$> traverseAfter on z

-- sample: exprBlanks
theorem exprBlanks (on : Steps) (deaf : Blanks on) (input : Expr) :
    runExpr on (input.walk blankPure) = (·.walk blankPure) <$> runExpr on input := by
  cases input <;> simp only [runExpr, Expr.traverse, map_bind, ← deaf.expr] <;>
    simp only [Expr.walk, blankExpr, Expr.traverse, exprBlanks on deaf, exprsBlanks on deaf,
      beforeBlanks on deaf, optionalBlanks on deaf, linksBlanks on deaf, paramsBlanks on deaf,
          piecesBlanks on deaf,
      scrutineesBlanks on deaf, armsBlanks on deaf, groupBlanks on deaf, rowBlanks on deaf,
      statementBlanks on deaf, statementsBlanks on deaf, letBlanks on deaf, clausesBlanks on deaf,
      inductArmsBlanks on deaf, calcStepsBlanks on deaf, rulesBlanks on deaf, afterBlanks on deaf,
      bind_map_left, Function.comp]

end

end ExprBlanks

/-! ## printer 9: `blankItemHangs` (Fmt/ElementsBlank.sw) -/
namespace BlankItem

axiom Note : Type
axiom Tok : Type
axiom Doc : Type
axiom Place : Type
axiom HangState : Type
axiom Hang : Type
axiom Hang.At : HangState → Hang
axiom Doc.concat : List Doc → Doc

structure Comments where
  above : List Note
  after : Option String
  blankBefore : Bool

structure Word where
  text : String
  comments : Comments

def Word.none : Word := { text := "", comments := { above := [], after := .none, blankBefore := false } }

axiom Word.trails : Word → Bool
axiom Word.sound : Word → Bool

/-- Cut down from `Fmt.Rules.Around`: `at` renamed `col` (`at` is a Lean keyword). -/
structure Around where
  before : Bool
  hoisted : Bool
  item : Bool
  col : Nat
  inArm : Bool

def Around.next (around : Around) (before : Bool) (skipped : Nat) : Around :=
  { before, hoisted := false, item := false, col := around.col + skipped, inArm := around.inArm }

/-- Cut down from `Syntax.InfixKind`: the kinds outside slice 1 merged into `InfixOther`. -/
inductive InfixKind
  | InfixBinary | InfixArrow | InfixOther

/-- Cut down from `Syntax.Expr` to slice 1's constructors: `within1` is false on the rest, so the proof's case
    split only refutes them. -/
inductive Expr
  | Atom (kind : Tok) (word : Word)
  | Paren (opener : Word) (inner : Expr) (close : Word)
  | Tuple (opener : Word) (items : List Expr) (trailing : Bool) (close : Word)
  | ListOf (opener : Word) (items : List Expr) (trailing : Bool) (close : Word)
  | App (head : Expr) (arguments : List Expr)
  | Infix (kind : InfixKind) (left : Expr) (operator : Word) (right : Expr)
  | Prefix (operator : Word) (operand : Expr)

open Expr InfixKind

noncomputable section

axiom Tok.wordWithin1 : Tok → Bool
axiom textSpells1 : Tok → String → Bool
axiom binaryText1 : String → Bool
axiom arrowText1 : String → Bool
axiom prefixText1 : String → Bool
axiom allWithin1 : List Expr → Bool
axiom allSound : List Expr → Bool

def Expr.within1 : Expr → Bool
  | Atom kind word => kind.wordWithin1 && textSpells1 kind word.text
  | Paren _ inner _ => inner.within1
  | Tuple _ items _ _ | ListOf _ items _ _ => allWithin1 items
  | App head arguments => head.within1 && allWithin1 arguments
  | Infix InfixBinary left operator right => left.within1 && right.within1 && binaryText1 operator.text
  | Infix InfixArrow left operator right => left.within1 && right.within1 && arrowText1 operator.text
  | Prefix operator operand => operand.within1 && prefixText1 operator.text
  | _ => false

def Expr.sound : Expr → Bool
  | Atom _ word => word.sound
  | Paren o inner c => o.sound && inner.sound && c.sound
  | Tuple o items _ c | ListOf o items _ c => o.sound && allSound items && c.sound
  | App head arguments => head.sound && allSound arguments
  | Infix _ left operator right => left.sound && operator.sound && right.sound
  | Prefix operator operand => operator.sound && operand.sound

def Expr.lead : Expr → Word
  | Atom _ word | Paren word _ _ | Tuple word _ _ _ | ListOf word _ _ _ => word
  | App head _ | Infix _ head _ _ => head.lead
  | Prefix operator _ => operator

mutual
def Expr.words : Expr → List Word
  | Atom _ word => [word]
  | Paren o inner c => o :: inner.words ++ [c]
  | Tuple o items _ c | ListOf o items _ c => o :: itemsWords items ++ [c]
  | App head arguments => head.words ++ itemsWords arguments
  | Infix _ left operator right => left.words ++ operator :: right.words
  | Prefix operator operand => operator :: operand.words
def itemsWords : List Expr → List Word
  | [] => []
  | item :: rest => item.words ++ itemsWords rest
end

def Expr.firstWord (expr : Expr) : Word := expr.words.headD Word.none
axiom Expr.trails : Expr → Bool

axiom framedBy : Word → Around → Doc → Doc
axiom Word.leaf : Word → Around → Nat → Doc
axiom parenDoc : Word → Expr → Word → Around → Doc
axiom commaBracket (list : Bool) : Word → List Expr → Word → Around → Doc
/-- Cut down from `appDocs`, whose `Applied` result the element reads only `.doc` of. -/
axiom appDoc : Expr → List Expr → Around → Doc
axiom Expr.chainLevel : Expr → Option Nat
axiom chain : Option Nat → Expr → Word → Expr → Around → Doc
axiom prefixGap : Word → Expr → Doc

def Expr.framed (expr : Expr) (around : Around) (doc : Doc) : Doc := framedBy expr.firstWord around doc

/-- Cut down from `Fmt.Rules.Expr.el`: the clauses outside slice 1 dropped. -/
def Expr.el (expr : Expr) (around : Around) : Doc :=
  let inside := { around with hoisted := true }
  match expr with
  | Atom _ word => word.leaf around around.col
  | Paren o inner c => expr.framed around (parenDoc o inner c inside)
  | Tuple o items _ c => expr.framed around (commaBracket false o items c inside)
  | ListOf o items _ c => expr.framed around (commaBracket true o items c inside)
  | App head arguments => expr.framed around (appDoc head arguments inside)
  | Infix InfixBinary left operator right | Infix InfixArrow left operator right =>
    expr.framed around (chain expr.chainLevel left operator right inside)
  | Infix InfixOther _ _ _ => Doc.concat []
  | Prefix operator operand =>
    expr.framed around
      (Doc.concat [operator.leaf inside around.col, prefixGap operator operand,
        operand.el (around.next operator.trails 1)])

axiom lexKind : String → Tok
axiom Plain : Tok → Prop
axiom isLayout : String → Bool
axiom isCloserText : String → Bool
axiom TrailsComment : Word → Prop
axiom plainStart : Place → Bool
axiom wordStart : Nat → Place → Option Nat
axiom leadStart : Nat → Place → Option Nat
axiom openedBy : HangState → Option Nat → HangState
axiom Ended : HangState → Bool → Place → Prop
axiom Entered : Nat → Nat → Bool → HangState → Place → Option Nat → Place → Hang → Prop
axiom HangLays : (String → Tok) → Doc → Nat → (Place → Hang → Prop) → (Place → Hang → Prop) → Prop
axiom ElHangs : (String → Tok) → Doc → Nat → Nat → Bool → Bool → (Nat → Place → Option Nat) → Prop

def WordToken (text : String) : Prop :=
  text.startsWith "--" = false ∧ isLayout text = false ∧ isCloserText text = false ∧ (text == ",") = false

def LedAt (kinds : String → Tok) (doc : Doc) (indent : Nat) (before trails : Bool) (state : HangState)
    (entry : Place) : Prop :=
  HangLays kinds doc indent (Entered indent indent before state entry (leadStart indent entry)) fun place hang =>
    Ended (openedBy state (leadStart indent entry)) trails place ∧ hang = Hang.At (openedBy state (leadStart indent entry))

axiom wordFacts (kind : Tok) (text : String) (within : (kind.wordWithin1 && textSpells1 kind text) = true) :
  Plain (lexKind text) ∧ WordToken text

axiom atomTrailsIs (kind : Tok) (word : Word) : (Atom kind word).trails = word.trails

axiom trailsOfSound (word : Word) (sound : word.sound = true) : TrailsComment word

axiom firstWordLead (expr : Expr) (within : expr.within1 = true) : expr.firstWord = expr.lead

axiom blankLeafHangs {kinds : String → Tok} {word : Word} {around : Around} {key indent : Nat} {state : HangState}
  {entry : Place}
  (plain : Plain (kinds word.text))
  (token : word.text.startsWith "--" = false)
  (solid : isLayout word.text = false)
  (closer : isCloserText word.text = false)
  (comma : (word.text == ",") = false)
  (hoisted : around.hoisted = false)
  (item : around.item = true)
  (unnoted : word.comments.above = [])
  (blank : word.comments.blankBefore = true)
  (trailed : TrailsComment word)
  (fresh : plainStart entry = false) :
  HangLays kinds (word.leaf around key) indent (Entered indent indent around.before state entry (leadStart indent entry))
    fun place hang =>
      Ended (openedBy state (leadStart indent entry)) word.trails place
        ∧ hang = Hang.At (openedBy state (leadStart indent entry))

axiom blankNodeAt {expr : Expr} {word : Word} (node : Around → Doc) {around : Around} {indent : Nat} {trails : Bool}
  {state : HangState} {entry : Place}
  (elIs : ∀ ar : Around, expr.el ar = framedBy word ar (node ar))
  (same : node { around with hoisted := true } = node around)
  (hoisted : around.hoisted = false)
  (item : around.item = true)
  (unnoted : word.comments.above = [])
  (blank : word.comments.blankBefore = true)
  (fresh : plainStart entry = false)
  (hoistedHangs : ∀ inset : Nat,
    ElHangs lexKind (expr.el { around with hoisted := true }) inset inset around.before trails wordStart) :
  LedAt lexKind (expr.el around) indent around.before trails state entry

-- sample: blankItemHangs
theorem blankItemHangs (expr : Expr) (around : Around) (indent : Nat) (state : HangState)
    (entry : Place)
    (within : expr.within1 = true)
    (sound : expr.sound = true)
    (hoisted : around.hoisted = false)
    (item : around.item = true)
    (unnoted : expr.lead.comments.above = [])
    (blank : expr.lead.comments.blankBefore = true)
    (fresh : plainStart entry = false)
    (hoistedHangs : ∀ inset : Nat,
      ElHangs lexKind (expr.el { around with hoisted := true }) inset inset around.before
        expr.trails wordStart) :
    LedAt lexKind (expr.el around) indent around.before expr.trails state entry := by
  cases expr with
  | Atom kind word =>
    obtain ⟨plain, notComment, solid, closer, comma⟩ := wordFacts kind word.text within
    rw [atomTrailsIs]
    exact blankLeafHangs plain notComment solid closer comma hoisted item unnoted blank
        (trailsOfSound word sound) fresh
  | Paren o inner c =>
    exact blankNodeAt (fun ar => parenDoc o inner c { ar with hoisted := true }) (fun _ => rfl) rfl
      hoisted item unnoted blank fresh hoistedHangs
  | Tuple o items _ c =>
    exact blankNodeAt (fun ar => commaBracket false o items c { ar with hoisted := true })
        (fun _ => rfl) rfl
      hoisted item unnoted blank fresh hoistedHangs
  | ListOf o items _ c =>
    exact blankNodeAt (fun ar => commaBracket true o items c { ar with hoisted := true })
        (fun _ => rfl) rfl
      hoisted item unnoted blank fresh hoistedHangs
  | App head arguments =>
    exact blankNodeAt (fun ar => appDoc head arguments { ar with hoisted := true })
      (fun _ => by rw [Expr.el, Expr.framed, firstWordLead _ within]) rfl hoisted item unnoted
          blank fresh hoistedHangs
  | Infix kind left operator right =>
    refine blankNodeAt (fun ar => chain
        (Infix kind left operator right).chainLevel left operator right
        { ar with hoisted := true }) (fun _ => ?_) rfl hoisted item unnoted blank fresh hoistedHangs
    cases kind <;> simp_all [Expr.el, Expr.framed, Expr.within1, firstWordLead _ within]
  | Prefix operator operand =>
    exact blankNodeAt (fun ar => Doc.concat [operator.leaf { ar with hoisted := true } ar.col,
        prefixGap operator operand, operand.el (ar.next operator.trails 1)])
      (fun _ => rfl) rfl hoisted item unnoted blank fresh hoistedHangs

end

end BlankItem

/-! ## top 1: `wordsCalmKeep` (Fmt/CommentsKeptProof.sw) -/
namespace WordsCalm

axiom Tok : Type
axiom Comments : Type
axiom Comments.kept : Comments → Bool → Bool → Comments

structure Word where
  text : String
  comments : Comments

noncomputable def Word.kept (word : Word) (item closer : Bool) : Word := { word with comments := word.comments.kept item closer }

/-- Cut down from `Syntax.InfixKind`: the kinds outside slice 1 merged into `InfixOther`. -/
inductive InfixKind
  | InfixBinary | InfixArrow | InfixOther

/-- Cut down from `Syntax.Expr` to slice 1's constructors: `within1` is false on the rest. -/
inductive Expr
  | Atom (kind : Tok) (word : Word)
  | Paren (opener : Word) (inner : Expr) (close : Word)
  | Tuple (opener : Word) (items : List Expr) (trailing : Bool) (close : Word)
  | ListOf (opener : Word) (items : List Expr) (trailing : Bool) (close : Word)
  | App (head : Expr) (arguments : List Expr)
  | Infix (kind : InfixKind) (left : Expr) (operator : Word) (right : Expr)
  | Prefix (operator : Word) (operand : Expr)

open Expr InfixKind

noncomputable section

axiom Tok.wordWithin1 : Tok → Bool
axiom textSpells1 : Tok → String → Bool
axiom binaryText1 : String → Bool
axiom arrowText1 : String → Bool
axiom prefixText1 : String → Bool
axiom isCloserText : String → Bool
axiom Expr.plainItem : Expr → Bool
axiom Word.keeps : Word → Word → Prop

mutual
def Expr.within1 : Expr → Bool
  | Atom kind word => kind.wordWithin1 && textSpells1 kind word.text
  | Paren _ inner _ => inner.within1
  | Tuple _ items _ _ | ListOf _ items _ _ => allWithin1 items
  | App head arguments => head.within1 && allWithin1 arguments
  | Infix InfixBinary left operator right => left.within1 && right.within1 && binaryText1 operator.text
  | Infix InfixArrow left operator right => left.within1 && right.within1 && arrowText1 operator.text
  | Prefix operator operand => operand.within1 && prefixText1 operator.text
  | _ => false
def allWithin1 : List Expr → Bool
  | [] => true
  | expr :: rest => expr.within1 && allWithin1 rest
end

mutual
def Expr.closed : Expr → Bool
  | Atom _ _ => true
  | Paren _ inner close => isCloserText close.text && inner.closed
  | Tuple _ items _ close | ListOf _ items _ close => isCloserText close.text && allClosed items
  | App head arguments => head.closed && allClosed arguments
  | Infix _ left _ right => left.closed && right.closed
  | Prefix _ operand => operand.closed
def allClosed : List Expr → Bool
  | [] => true
  | expr :: rest => expr.closed && allClosed rest
end

mutual
def Expr.words : Expr → List Word
  | Atom _ word => [word]
  | Paren o inner c => (o :: inner.words) ++ [c]
  | Tuple o items _ c | ListOf o items _ c => (o :: itemsWords items) ++ [c]
  | App head arguments => head.words ++ itemsWords arguments
  | Infix _ left operator right => left.words ++ operator :: right.words
  | Prefix operator operand => operator :: operand.words
def itemsWords : List Expr → List Word
  | [] => []
  | item :: rest => item.words ++ itemsWords rest
end

mutual
def Expr.calm : Expr → Bool → Expr
  | Atom kind word, item => Atom kind (word.kept item false)
  | Paren o inner c, item => Paren (o.kept item false) (inner.calm false) (c.kept false true)
  | Tuple o items comma c, item => Tuple (o.kept item false) (calmAll true items) comma (c.kept false true)
  | ListOf o items comma c, item => ListOf (o.kept item false) (calmItems items) comma (c.kept false true)
  | App head arguments, item => App (head.calm item) (calmAll false arguments)
  | Infix kind left operator right, item => Infix kind (left.calm item) (operator.kept false false) (right.calm false)
  | Prefix operator operand, item => Prefix (operator.kept item false) (operand.calm false)
def calmAll (item : Bool) : List Expr → List Expr
  | [] => []
  | expr :: rest => expr.calm item :: calmAll item rest
def calmLead : List Expr → List Expr
  | [] => []
  | first :: rest => first.calm false :: calmAll true rest
def pickItems (plain : Bool) (items : List Expr) : List Expr := if plain then calmLead items else calmAll true items
def calmItems (items : List Expr) : List Expr := pickItems (items.all Expr.plainItem) items
end

def AllKeep : List Word → List Word → Prop
  | [], [] => True
  | before :: more, after :: later => before.keeps after ∧ AllKeep more later
  | _, _ => False

axiom keptKeeps (word : Word) (item closer : Bool) (closes : (!closer || isCloserText word.text) = true) :
  word.keeps (word.kept item closer)

axiom allKeepAppend (front later back after : List Word) (fronts : AllKeep front later) (backs : AllKeep back after) :
  AllKeep (front ++ back) (later ++ after)

/- The other members of `wordsCalmKeep`'s mutual group (rule 8). -/
axiom itemsKeepAll (items : List Expr) (item : Bool) (within : allWithin1 items = true)
  (closed : allClosed items = true) : AllKeep (itemsWords items) (itemsWords (calmAll item items))

axiom itemsKeepPick (plain : Bool) (items : List Expr) (within : allWithin1 items = true)
  (closed : allClosed items = true) : AllKeep (itemsWords items) (itemsWords (pickItems plain items))

-- sample: wordsCalmKeep
theorem wordsCalmKeep (expr : Expr) (item : Bool)
    (within : expr.within1 = true)
    (closed : expr.closed = true) :
    AllKeep expr.words (expr.calm item).words := by
  rcases expr with _ | _ | _ | _ | _ | ⟨_ | _ | _, _, _, _⟩ | _ <;>
    simp only [Expr.within1, Expr.closed, Expr.words, Expr.calm, Bool.and_eq_true,
        Bool.false_eq_true]
      at within closed ⊢ <;>
    first
    | apply allKeepAppend <;> simp_all [calmItems, AllKeep, keptKeeps, itemsKeepAll, itemsKeepPick,
        wordsCalmKeep]
    | simp_all [AllKeep, keptKeeps, wordsCalmKeep]

end

end WordsCalm

/-! ## printer 2: `heldItemSeat` (Fmt/BracketHangProofs.sw) -/
namespace HeldItem

structure OpenMark where
  key : Nat
  marked : Nat
  least : Option Nat

structure Carry where
  floor : Option Nat
  marks : List OpenMark

inductive Place
  | AtStart (col : Nat) (carry : Carry)
  | Broken (col : Nat) (carry : Carry)
  | Mid (col : Nat) (carry : Carry)
  | Held (col : Nat) (carry : Carry)

open Place

structure HangState where
  blocks : List (Option Nat)
  top : Option Nat
  start : Bool
  glue : Bool

inductive Hang
  | Opening | At (state : HangState) | Broke

def floored (carry : Carry) (indent : Nat) : Nat :=
  match carry.floor with
  | none => indent
  | some least => max indent least

def inForce : List (Option Nat) → Option Nat → Nat
  | some column :: _, _ => column
  | none :: rest, top => inForce rest top
  | [], top => top.getD 0

def itemState (outer : List (Option Nat)) (top : Option Nat) : HangState :=
  { blocks := none :: outer, top, start := true, glue := false }

def plainStart : Place → Bool
  | AtStart _ _ => true
  | _ => false

def wordStart (indent : Nat) : Place → Option Nat
  | AtStart col _ | Broken col _ => some col
  | Mid _ _ => none
  | Held col carry => some (floored carry (max indent (col + 2)))

def Seated (column : Nat) (before : Bool) (state : HangState) : Place → Prop
  | AtStart col carry | Broken col carry => col = column ∧ floored carry column = column
  | Mid col carry => carry.floor = none ∧ inForce state.blocks state.top ≤ col
  | Held col carry => before = true ∧ carry.floor = none ∧ inForce state.blocks state.top ≤ col

def Room (state : HangState) : Option Nat → Prop
  | none => True
  | some column => state.glue = false ∧ column > inForce state.blocks state.top

def Seat (indent column : Nat) (before : Bool) (state : HangState) (entry : Place) (first : Option Nat) : Prop :=
  Seated column before state entry ∧ column ≤ indent ∧ inForce state.blocks state.top ≤ indent ∧ Room state first

def ItemSeat (inset : Nat) (outer : List (Option Nat)) (top : Option Nat) (before : Bool) (place : Place)
    (hang : Hang) : Prop :=
  hang = .At (itemState outer top) ∧ plainStart place = false
    ∧ Seat inset inset before (itemState outer top) place (wordStart inset place)

-- sample: heldItemSeat
theorem heldItemSeat (inset col : Nat) (outer : List (Option Nat)) (top : Option Nat)
    (carry : Carry)
    (floor : carry.floor = none)
    (left : inForce outer top ≤ col)
    (bound : inForce outer top < inset) :
    ItemSeat inset outer top true (Held col carry) (.At (itemState outer top)) := by
  simp [ItemSeat, Seat, Seated, Room, plainStart, wordStart, itemState, inForce, floored, floor]
  omega

end HeldItem

/-! ## printer 3: `stepsIfBroken` (Fmt/TouchSteps.sw) -/
namespace IfBroken

axiom Seam : Type
axiom Touch : Type
axiom Spacing : Type
axiom admitsGlue : List Spacing → List Touch → Bool
axiom codeTouching : List Touch → List Touch

/-- Cut down from std's `Doc`: one leaf kept as a stand-in for the rest, which this proof never reaches. -/
inductive Doc
  | Chunk (text : String)
  | IfBroken (id : Nat) (broken flat : Doc)

axiom ChunkTouches : String → Seam → List Touch → (Seam → List Touch → Prop) → Prop

/-- Cut down from std's `Doc.Touches` to the two constructors above. -/
def Touches : Doc → Seam → List Touch → (Seam → List Touch → Prop) → Prop
  | .Chunk text, seam, trace, next => ChunkTouches text seam trace next
  | .IfBroken _ broken flat, seam, trace, next => Touches broken seam trace next ∧ Touches flat seam trace next

def Steps (doc : Doc) (pre : Seam → Prop) (spacing : List Spacing) (post : Seam → Prop) : Prop :=
  ∀ (seam : Seam) (trace : List Touch) (next : Seam → List Touch → Prop), pre seam →
    (∀ (after : Seam) (added : List Touch), post after → admitsGlue spacing (codeTouching added) = true →
      next after (trace ++ added)) →
    Touches doc seam trace next

-- sample: stepsIfBroken
theorem stepsIfBroken (id : Nat) {broken flat : Doc} (pre : Seam → Prop) {spacing : List Spacing}
    (post : Seam → Prop)
    (brokenSteps : Steps broken pre spacing post)
    (flatSteps : Steps flat pre spacing post) :
    Steps (.IfBroken id broken flat) pre spacing post :=
  fun seam trace next holds after => ⟨brokenSteps seam trace next holds after,
      flatSteps seam trace next holds after⟩

end IfBroken

/-! ## printer 4: `parenInnerKept` (Fmt/CalmProofs.sw) -/
namespace ParenInner

axiom Tok : Type
axiom Doc : Type
axiom Around : Type
axiom Around.item : Around → Bool
axiom Statement : Type
axiom Comments : Type
axiom Comments.kept : Comments → Bool → Bool → Comments
axiom Doc.concat : List Doc → Doc
axiom Doc.Nest : Nat → Doc → Doc
axiom Doc.Align : Doc → Doc
axiom Doc.HardLine : Doc

structure Word where
  text : String
  comments : Comments

noncomputable def Word.kept (word : Word) (item closer : Bool) : Word :=
  { word with comments := word.comments.kept item closer }

inductive InfixKind
  | InfixBinary | InfixArrow | InfixOther

/-- Cut down from `Syntax.Expr`: slice 1's constructors, and `Block` and `If`, which `parenInner` reads; the rest
    fall to `parenInner`'s and `calm`'s last clauses as these two do, and `within1` is false on them. -/
inductive Expr
  | Atom (kind : Tok) (word : Word)
  | Paren (opener : Word) (inner : Expr) (close : Word)
  | Tuple (opener : Word) (items : List Expr) (trailing : Bool) (close : Word)
  | ListOf (opener : Word) (items : List Expr) (trailing : Bool) (close : Word)
  | App (head : Expr) (arguments : List Expr)
  | Infix (kind : InfixKind) (left : Expr) (operator : Word) (right : Expr)
  | Prefix (operator : Word) (operand : Expr)
  | Block (first : Statement) (rest : List Statement) (result : Expr)
  | If (keyword : Word) (binder : Option (Word × Word)) (condition : Expr) (thenKeyword : Word) (whenTrue : Expr)
      (elseKeyword : Word) (whenFalse : Expr)

open Expr InfixKind

noncomputable section

axiom Expr.within1 : Expr → Bool
axiom Expr.closed : Expr → Bool
axiom Expr.el : Expr → Around → Doc
axiom calmAll : Bool → List Expr → List Expr
axiom calmItems : List Expr → List Expr
axiom blockWithin (first : Statement) (rest : List Statement) (result : Expr) : (Block first rest result).within1 = false
axiom ifWithin (k : Word) (b : Option (Word × Word)) (c : Expr) (t : Word) (x : Expr) (e : Word) (y : Expr) :
  (If k b c t x e y).within1 = false

/-- `calmAll` and `calmItems` are mutual with `calm`; the proof only needs `calm` to keep the constructor. -/
def Expr.calm : Expr → Bool → Expr
  | Atom kind word, item => Atom kind (word.kept item false)
  | Paren o inner c, item => Paren (o.kept item false) (inner.calm false) (c.kept false true)
  | Tuple o items comma c, item => Tuple (o.kept item false) (calmAll true items) comma (c.kept false true)
  | ListOf o items comma c, item => ListOf (o.kept item false) (calmItems items) comma (c.kept false true)
  | App head arguments, item => App (head.calm item) (calmAll false arguments)
  | Infix kind left operator right, item => Infix kind (left.calm item) (operator.kept false false) (right.calm false)
  | Prefix operator operand, item => Prefix (operator.kept item false) (operand.calm false)
  | other, _ => other

def Expr.good (expr : Expr) : Bool := expr.within1 && expr.closed

def parenInner (inner : Expr) (innerAround : Around) : Doc :=
  match inner with
  | Block _ _ _ => .Nest 2 (Doc.concat [.HardLine, inner.el innerAround])
  | If _ _ _ _ _ _ _ => .Align (inner.el innerAround)
  | _ => inner.el innerAround

-- sample: parenInnerKept
theorem parenInnerKept (inner : Expr) (around : Around)
    (good : inner.good = true)
    (each : (inner.calm false).el around = inner.el around) :
    parenInner (inner.calm false) around = parenInner inner around := by
  cases inner <;> simp_all [Expr.good, Expr.calm, parenInner, blockWithin, ifWithin]

end

end ParenInner

/-! ## printer 6: `refinesAppend` (Fmt/ToldDeclProofs.sw) -/
namespace Refines

axiom Told : Type
axiom EntryRefines : Told → Told → Prop

def Refines : List Told → List Told → Prop
  | [], [] => True
  | entry :: more, other :: rest => EntryRefines entry other ∧ Refines more rest
  | _, _ => False

-- sample: refinesAppend
theorem refinesAppend {one two three four : List Told}
    (front : Refines one three)
    (back : Refines two four) :
    Refines (one ++ two) (three ++ four) := by
  induction one generalizing three <;> cases three <;> simp_all [Refines]

end Refines

/-! ## printer 7: `notedCloserHangs` (Fmt/HangProofs.sw) -/
namespace NotedCloser

axiom Tok : Type
axiom Doc : Type
axiom Event : Type
axiom Note : Type
axiom Doc.concat : List Doc → Doc
axiom Doc.Closing : String → Doc
axiom Doc.CloserLine : Nat → Doc

structure OpenMark where
  key : Nat
  marked : Nat
  least : Option Nat

structure Carry where
  floor : Option Nat
  marks : List OpenMark

def Carry.closerAt (carry : Carry) (key indent : Nat) : Nat :=
  match carry.marks.find? (fun mark => mark.key == key) with
  | some { least := some least, marked, .. } => if least ≤ indent then min marked indent else indent
  | _ => indent

inductive Place
  | AtStart (col : Nat) (carry : Carry)
  | Broken (col : Nat) (carry : Carry)
  | Mid (col : Nat) (carry : Carry)
  | Held (col : Nat) (carry : Carry)

def Place.carry : Place → Carry
  | AtStart _ carry | Broken _ carry | Mid _ carry | Held _ carry => carry

structure HangState where
  blocks : List (Option Nat)
  top : Option Nat
  start : Bool
  glue : Bool

inductive Hang
  | Opening | At (state : HangState) | Broke

structure Comments where
  above : List Note
  after : Option String
  blankBefore : Bool

structure Word where
  text : String
  comments : Comments

/-- Cut down from `Fmt.Rules.Around`: `at` renamed `col` (`at` is a Lean keyword). -/
structure Around where
  before : Bool
  hoisted : Bool
  item : Bool
  col : Nat
  inArm : Bool

def inForce : List (Option Nat) → Option Nat → Nat
  | some column :: _, _ => column
  | none :: rest, top => inForce rest top
  | [], top => top.getD 0

def leftOf (column : Nat) : Option Nat → Bool
  | some block => column < block
  | none => true

noncomputable section

axiom Word.trails : Word → Bool
axiom Word.leaf : Word → Around → Nat → Doc
axiom Word.leading : Word → Around → Nat → List Doc
axiom Word.trailing : Word → List Doc
axiom isCloserText : String → Bool
axiom closesText : String → Bool
axiom isLayout : String → Bool
axiom Tok.isCloser : Tok → Bool
axiom NotesComment : List Note → Prop
axiom TrailsComment : Word → Prop
axiom hangOf : (String → Tok) → List Event → Hang
axiom Lays : Doc → Nat → Place → List Event → (Place → List Event → Prop) → Prop
axiom HangLays : (String → Tok) → Doc → Nat → (Place → Hang → Prop) → (Place → Hang → Prop) → Prop
axiom HangLaysAll : (String → Tok) → List Doc → Nat → (Place → Hang → Prop) → (Place → Hang → Prop) → Prop
axiom LandsAt : Nat → Hang → Place → Hang → Prop
axiom CloserExit : Word → Around → HangState → List (Option Nat) → Place → Hang → Prop
axiom CloserFold : Nat → HangState → Option Nat → List (Option Nat) → Prop

def Word.noted (word : Word) : Bool := !word.comments.above.isEmpty

def Word.lone (word : Word) (around : Around) : Bool := !word.noted && around.before && word.trails

def CloserToken (kinds : String → Tok) (text : String) : Prop :=
  (kinds text).isCloser = true ∧ closesText text = true ∧ isCloserText text = true ∧ text.startsWith "--" = false
    ∧ isLayout text = false

def CloserSeat (indent : Nat) (before lone : Bool) (state : HangState) : Place → Prop
  | .AtStart _ _ => False
  | .Broken col carry =>
    lone = true ∨ (col = indent ∧ carry.floor = none ∧ leftOf indent (state.blocks.headD none) = true)
  | .Mid col carry => carry.floor = none ∧ inForce state.blocks state.top ≤ col
  | .Held col carry => before = true ∧ carry.floor = none ∧ inForce state.blocks state.top ≤ col

def CloserFits (key indent : Nat) (block : Option Nat) (outside : Nat) (carry : Carry) : Prop :=
  leftOf (carry.closerAt key indent) block = true ∧ outside ≤ carry.closerAt key indent

def CloserEntry (kinds : String → Tok) (word : Word) (around : Around) (key indent : Nat) (state : HangState)
    (block : Option Nat) (outer : List (Option Nat)) (place : Place) (hang : Hang) : Prop :=
  hang = .At state ∧ CloserSeat indent around.before (word.lone around) state place
    ∧ ((word.noted || word.lone around) = true → CloserFits key indent block (inForce outer state.top) place.carry)

axiom hangsBy {kinds : String → Tok} {doc : Doc} {indent : Nat} {pre post : Place → Hang → Prop}
  (lays : ∀ (place : Place) (trace : List Event) (next : Place → List Event → Prop), pre place (hangOf kinds trace) →
    (∀ (after : Place) (later : List Event), post after (hangOf kinds later) → next after later) →
    Lays doc indent place trace next) :
  HangLays kinds doc indent pre post

axiom laysBy {kinds : String → Tok} {doc : Doc} {indent : Nat} {pre post : Place → Hang → Prop}
  (hangs : HangLays kinds doc indent pre post)
  (place : Place) (trace : List Event) (next : Place → List Event → Prop) (holds : pre place (hangOf kinds trace))
  (after : ∀ (left : Place) (later : List Event), post left (hangOf kinds later) → next left later) :
  Lays doc indent place trace next

axiom hangsConcat {kinds : String → Tok} {docs : List Doc} {indent : Nat} {pre post : Place → Hang → Prop}
  (each : HangLaysAll kinds docs indent pre post) : HangLays kinds (Doc.concat docs) indent pre post

axiom hangsAppend {kinds : String → Tok} {front back : List Doc} {indent : Nat} {pre middle post : Place → Hang → Prop}
  (first : HangLaysAll kinds front indent pre middle) (second : HangLaysAll kinds back indent middle post) :
  HangLaysAll kinds (front ++ back) indent pre post

axiom closerLeadingHangs (kinds : String → Tok) (word : Word) (around : Around) (key indent : Nat)
  (state : HangState) (entry : Place) (note : Note) (rest : List Note)
  (hoisted : around.hoisted = false)
  (noted : word.comments.above = note :: rest)
  (closer : isCloserText word.text = true)
  (comments : NotesComment (note :: rest)) :
  HangLaysAll kinds (word.leading around key) indent
    (fun place hang => place = entry ∧ hang = .At state ∧ CloserSeat indent around.before false state entry)
    (LandsAt (entry.carry.closerAt key indent) (.At state))

axiom closerAtLineHangs (kinds : String → Tok) (word : Word) (around : Around) (indent column : Nat)
  (state : HangState) (block : Option Nat) (outer : List (Option Nat))
  (token : CloserToken kinds word.text)
  (fold : CloserFold indent state block outer)
  (trailed : TrailsComment word)
  (left : leftOf column block = true)
  (right : inForce outer state.top ≤ column) :
  HangLaysAll kinds (.Closing word.text :: word.trailing) indent (LandsAt column (.At state))
    (CloserExit word around state outer)

/-- Stitchwort's `++` groups to the right; Lean's to the left, so the grouping is written out. -/
axiom closerLeafIs (word : Word) (around : Around) (key : Nat) (closer : isCloserText word.text = true) :
  word.leaf around key
    = Doc.concat (word.leading around key ++ ((if word.lone around then [.CloserLine key] else [])
      ++ ([.Closing word.text] ++ word.trailing)))

-- sample: notedCloserHangs
theorem notedCloserHangs (kinds : String → Tok) (word : Word) (around : Around) (key indent : Nat)
    (state : HangState) (block : Option Nat) (outer : List (Option Nat)) (note : Note)
        (rest : List Note)
    (token : CloserToken kinds word.text)
    (fold : CloserFold indent state block outer)
    (hoisted : around.hoisted = false)
    (noted : word.comments.above = note :: rest)
    (comments : NotesComment (note :: rest))
    (trailed : TrailsComment word) :
    HangLays kinds (word.leaf around key) indent
        (CloserEntry kinds word around key indent state block outer)
      (CloserExit word around state outer) := by
  have text := token.2.2.1
  have lone : word.lone around = false := by simp [Word.lone, Word.noted, noted]
  rw [closerLeafIs word around key text, lone]
  refine hangsBy fun place trace next ⟨folded, seat, fits⟩ after => ?_
  obtain ⟨left, right⟩ := fits (by simp [Word.noted, noted])
  rw [lone] at seat
  exact laysBy (hangsConcat (hangsAppend
      (closerLeadingHangs kinds word around key indent state place note rest hoisted noted text
          comments)
      (closerAtLineHangs kinds word around indent _ state block outer token fold trailed left
          right)))
    place trace next ⟨rfl, folded, seat⟩ after

end

end NotedCloser

/-! ## printer 8: `anyHangsOf` (Fmt/ElementsProofs.sw) -/
namespace AnyHangs

axiom Expr : Type
axiom Word : Type
axiom Around : Type
axiom Doc : Type
axiom Tok : Type
axiom Around.before : Around → Bool
axiom Around.item : Around → Bool
axiom Expr.plainAt : Expr → Around → Bool
axiom Expr.trails : Expr → Bool
axiom Expr.el : Expr → Around → Doc
axiom Expr.inChain : Expr → Option Nat → Bool
axiom Expr.lead : Expr → Word
axiom Word.leadsLine : Word → Around → Bool
axiom lexKind : String → Tok
axiom HangsAt : (String → Tok) → Bool → Bool → Doc → Prop
axiom Links : (String → Tok) → Bool → Option Nat → Bool → Expr → Around → Bool → Prop

def AnyFacts (expr : Expr) : Prop :=
  (∀ around : Around, expr.plainAt around = true → HangsAt lexKind around.before expr.trails (expr.el around))
    ∧ (∀ (level : Option Nat) (first : Bool) (around : Around),
      ((expr.inChain level && !around.item) || expr.plainAt around) = true →
      Links lexKind (expr.inChain level && expr.lead.leadsLine around) level first expr around expr.trails)

-- sample: anyHangsOf
theorem anyHangsOf (expr : Expr)
    (facts : AnyFacts expr) (around : Around)
    (plain : expr.plainAt around = true) :
    HangsAt lexKind around.before expr.trails (expr.el around) :=
  facts.1 around plain

end AnyHangs

/-! ## printer 10: `placedSteps` (Fmt/TouchProofs.sw) -/
namespace Placed

axiom Doc : Type
axiom Spacing : Type
axiom Word : Type
axiom Doc.Displaced : Doc → Doc
axiom Spacing.admits : Spacing → Bool → Bool
axiom Spacing.admitsWord : Spacing → Word → Bool
axiom isComment : String → Bool
axiom Quiet : Seam → Prop

/-- Cut down from `Fmt.TouchSteps.Seam`: `Along`'s argument stands for the word before. -/
inductive Seam
  | Begun | Along (word : Word) | Awaiting (word : Word) (comment : String)

axiom Steps : Doc → (Seam → Prop) → List Spacing → (Seam → Prop) → Prop

def Fits (before : Bool) (first : Spacing) : Seam → Prop
  | .Begun => first.admits false = true
  | .Along word => first.admitsWord word = true
  | .Awaiting _ comment => before = true ∧ first.admits false = true ∧ isComment comment = true

def Loose (first : Spacing) : Prop := first.admits false = true

axiom fitsQuiet (before : Bool) (first : Spacing) (seam : Seam) (fits : Fits before first seam) : Quiet seam

axiom stepsDisplaced {inner : Doc} (pre : Seam → Prop) {spacing : List Spacing} (post : Seam → Prop)
  (steps : Steps inner pre spacing post) (fresh : pre .Begun) (quiet : ∀ seam : Seam, pre seam → Quiet seam) :
  Steps (.Displaced inner) pre spacing post

-- sample: placedSteps
theorem placedSteps (displaced : Bool) (doc : Doc) (first : Spacing) (spacing : List Spacing)
    (post : Seam → Prop)
    (inner : Steps doc (Fits true first) spacing post)
    (fresh : displaced = true → Loose first) :
    Steps (if displaced then .Displaced doc else doc) (Fits true first) spacing post := by
  cases displaced
  · exact inner
  · exact stepsDisplaced _ _ inner (fresh rfl) (fitsQuiet true first)

end Placed

/-! ## printer 11: `statementsWalk` (Fmt/BlankProofs.sw) -/
namespace StatementsWalk

axiom Let : Type
axiom Attributes : Type
axiom Header : Type
axiom DefBody : Type
axiom Expr : Type
axiom Pure : Type
axiom meaningPure : Pure
axiom Let.blank : Let → Let
axiom DefBody.blank : DefBody → DefBody
axiom walkLet : Pure → Let → Let
axiom walkAttributes : Pure → List Attributes → List Attributes
axiom walkHeader : Pure → Header → Header
axiom walkDefBody : Pure → DefBody → DefBody
axiom Expr.walk : Expr → Pure → Expr

inductive Statement
  | LetStatement (binding : Let)
  | LocalDef (attributes : List Attributes) (header : Header) (body : DefBody)
  | ExprStatement (value : Expr)

open Statement

noncomputable section

def Statement.blank : Statement → Statement
  | LetStatement binding => LetStatement binding.blank
  | LocalDef attributes header body => LocalDef attributes header body.blank
  | ExprStatement value => ExprStatement value

def blankStatements : List Statement → List Statement
  | [] => []
  | first :: rest => first.blank :: blankStatements rest

def walkStatement (on : Pure) : Statement → Statement
  | LetStatement binding => LetStatement (walkLet on binding)
  | LocalDef attributes header body => LocalDef (walkAttributes on attributes) (walkHeader on header) (walkDefBody on body)
  | ExprStatement value => ExprStatement (value.walk on)

def walkStatements (on : Pure) : List Statement → List Statement
  | [] => []
  | first :: rest => walkStatement on first :: walkStatements on rest

axiom letWalk (binding : Let) : (walkLet meaningPure binding.blank).blank = (walkLet meaningPure binding).blank

axiom defBodyWalk (body : DefBody) :
  (walkDefBody meaningPure body.blank).blank = (walkDefBody meaningPure body).blank

-- sample: statementsWalk
theorem statementsWalk (statements : List Statement) :
    blankStatements (walkStatements meaningPure (blankStatements statements))
      = blankStatements (walkStatements meaningPure statements) := by
  induction statements with
  | nil => rfl
  | cons first rest ih =>
    cases first <;> simp [blankStatements, walkStatements, walkStatement, Statement.blank, letWalk,
        defBodyWalk, ih]

end

end StatementsWalk

/-! ## top 2: `firstThreeKeepMeaning` (Fmt/MeaningProofs.sw) -/
namespace FirstThree

axiom SourceFile : Type
axiom Meaning : Type
axiom SourceFile.withForall : SourceFile → SourceFile
axiom SourceFile.withoutTrailingCommas : SourceFile → SourceFile
axiom SourceFile.withoutSpareBrackets : SourceFile → SourceFile
axiom SourceFile.meaning : SourceFile → Meaning

axiom forallKeepsFile (file : SourceFile) : file.withForall.meaning = file.meaning
axiom commaKeepsFile (file : SourceFile) : file.withoutTrailingCommas.meaning = file.meaning
axiom bracketKeepsFile (file : SourceFile) : file.withoutSpareBrackets.meaning = file.meaning

-- sample: firstThreeKeepMeaning
theorem firstThreeKeepMeaning (file : SourceFile) :
    file.withForall.withoutTrailingCommas.withoutSpareBrackets.meaning = file.meaning := by
  simp [bracketKeepsFile, commaKeepsFile, forallKeepsFile]

end FirstThree

/-! ## top 3: `witnessUnreturned` (Fmt/TopStatements.sw) -/
namespace Witness

axiom Lexed : Type
axiom SourceFile : Type
axiom Decl : Type
axiom Leaf : Type
axiom Lexed.leaves : Lexed → List Leaf
axiom Lexed.settledOnce : Lexed → List Leaf
axiom lex : String → Except String Lexed
axiom leavesWithin1 : List Leaf → Bool
axiom parseFile : List Leaf → Except String SourceFile
axiom SourceFile.within1 : SourceFile → Bool
axiom SourceFile.tidy1 : SourceFile → SourceFile
axiom SourceFile.printed1 : SourceFile → String
axiom SourceFile.unreturned : SourceFile → Bool
axiom SourceFile.decls : SourceFile → List Decl
axiom Decl.unreturned : Decl → Bool
axiom formatWithin1 : String → Except String String
axiom witnessSource : String
axiom witnessOut : String

def Formats1 (source out : String) (lexed : Lexed) (parsed : SourceFile) : Prop :=
  lex source = .ok lexed ∧ leavesWithin1 lexed.leaves = true ∧ parseFile lexed.settledOnce = .ok parsed
    ∧ parsed.within1 = true ∧ out = parsed.tidy1.printed1

axiom witnessFormats : formatWithin1 witnessSource = .ok witnessOut

axiom formatsOf (source out : String) (formats : formatWithin1 source = .ok out) :
  ∃ (lexed : Lexed) (parsed : SourceFile), Formats1 source out lexed parsed

axiom tidiedDeclsUnreturned1 (source : String) (lexed : Lexed) (parsed : SourceFile)
  (lexes : lex source = .ok lexed) (leaves : leavesWithin1 lexed.leaves = true)
  (parses : parseFile lexed.settledOnce = .ok parsed) (within : parsed.within1 = true) :
  parsed.tidy1.decls.all Decl.unreturned = true

axiom tidiedUnreturned1 (source : String) (lexed : Lexed) (parsed : SourceFile)
  (lexes : lex source = .ok lexed) (leaves : leavesWithin1 lexed.leaves = true)
  (parses : parseFile lexed.settledOnce = .ok parsed) (within : parsed.within1 = true) :
  parsed.tidy1.unreturned = true

-- sample: witnessUnreturned
theorem witnessUnreturned : ∃ (lexed : Lexed) (parsed : SourceFile), parsed.tidy1.unreturned = true
      ∧ parsed.tidy1.decls.all Decl.unreturned = true := by
  obtain ⟨lexed, parsed, lexes, leaves, parses, within, _⟩ := formatsOf _ _ witnessFormats
  exact ⟨lexed, parsed, tidiedUnreturned1 _ _ _ lexes leaves parses within,
    tidiedDeclsUnreturned1 _ _ _ lexes leaves parses within⟩

end Witness
