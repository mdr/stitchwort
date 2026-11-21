--| Stage 2c's constructs on small cases: blocks, `let`, local
--| definitions, `handle`, `calc`, `rewrite`, `cases`, `match induct` and
--| the errors whose order depends on layout. The harness compares whole
--| files with the Rust side; these pin the shapes.

namespace Syntax.Tests
import Std (Bool, List, Option, Result, Text)
import Syntax (Decl, DefBody, Expr, HandlerClause, InfixKind, Rules, SourceFile, Statement)

--| The body of the file's one definition, if it parses.
def bodyOf (source: Text): Option Expr := match file source with
  | Ok { decls = [Definition _ _ (Assigned _ value)], end } => Some value
  | _ => None

test "a block keeps its lines and value, and no column" :=
  match bodyOf "def f: Nat :=\n  let x := 1\n  print x\n  x" with
    | Some (Block (LetStatement _) [ExprStatement _] (Atom _ value)) => value.text == "x"
    | _ => False

test "a block of one line is that line's expression" := match bodyOf "def f: Nat :=\n  g x" with
  | Some (App _ _) => True
  | _ => False

test "a block's lines may be indented anywhere: the same tree" :=
  bodyOf "def f: Nat :=\n  let x := 1\n  x" == bodyOf "def f: Nat :=\n        let x := 1\n        x"

test "a let with a semicolon on its line is an expression" :=
  tree "def f: Nat := (let y := 1; y)"
    == "Def\n  def\n  f\n  ResultType\n    :\n    Nat\n  Body\n    :=\n    Paren\n      (\n      LetExpr\n        Let\n          let\n          y\n          :=\n          1\n        ;\n        y\n      )\n"

test "a semicolon inside brackets in a let's value is a sequence" :=
  match bodyOf "def f: Nat := (let x := (a; b); x)" with
    | Some (Paren _ (LetIn ({ value = Paren _ (Infix InfixSeq _ _ _) _, .. }) _ _) _) => True
    | _ => False

test "a local definition is a statement of its own" :=
  match bodyOf "def f: Nat :=\n  @[tailrec]\n  def go (k: Nat): Nat := k\n  go 1" with
    | Some (Block (LocalDef [_] header (Assigned _ _)) [] _) => header.name.text == "go"
    | _ => False

test "a block can't end on a let or a local definition" :=
  tree "def f: Nat :=\n  let x := 1" == "error: a block must end with an expression, not `let`"
    && tree "def f: Nat :=\n  def g: Nat := 1"
      == "error: a block must end with an expression, not a local `def` or `theorem`"

test "a gap in a block's last let reports the let, which comes first" :=
  tree "def f: Nat :=\n  let x := 1 +" == "error: a block must end with an expression, not `let`"
    && tree "def f: Nat :=\n  let x := 1 +\n  x" == "error: expected an expression, but the line ends here"

test "a local definition's parameters are checked like a top-level one's" :=
  tree "def f: Nat :=\n  def g (a a: Nat): Nat := a\n  g 1 1" == "error: `a` is already a parameter of `g`"

test "handler clauses: return, and an operation with its continuation" :=
  match bodyOf "def f: Nat := handle run () with\n  | return x => x\n  | get _, k => k 0" with
    | Some (Handle _ _ _ [ReturnClause _ _ _ _ _, OperationClause _ operation _ _ continuation _ _]) =>
      operation.text == "get" && continuation.text == "k"
    | _ => False

test "match induct names its cases" :=
  match bodyOf "def f: Nat := match induct g x with\n  | eq1 a _ => a\n  | eq2 => 0" with
    | Some (Induct _ _ _ _ [first, second]) => first.names.length == 2 && second.case.text == "eq2"
    | _ => False

test "calc keeps each step's relation and proof" :=
  match bodyOf "theorem t: a = b := calc a\n  _ = c := p\n  _ <= b" with
    | Some (Calc _ _ [first, second]) => first.proof.isSome && second.proof.isNone && second.relation.text == "<="
    | _ => False

test "a calc chain goes one way" :=
  tree "theorem t: a = b := calc a\n  _ < c := p\n  _ > b := q"
    == "error: a `calc` chain goes one way: `<` and `<=` can't be mixed with `>` and `>=`"

test "a rewrite's rules end at then, at and in, outside brackets" :=
  match bodyOf "theorem t: a = b := rewrite p, <- (if c then a else b) at h then rfl" with
    | Some
        (Rewrite _
          (RuleList [{ reverse = None, .. }, { reverse = Some _, rule = Paren _ (If _ _ _ _ _ _ _) _ }])
          (Some _)
          (Some _)) => True
    | _ => False

test "then ending its line takes the lines below at the block's column" :=
  match bodyOf "theorem t: a = b :=\n  rewrite p then\n  let x := 1\n  rfl" with
    | Some (Rewrite _ _ None (Some (_, Block (LetStatement _) [] _))) => True
    | _ => False

test "cases alone is a word; with then, a node" :=
  match bodyOf "theorem t: a = b := cases", bodyOf "theorem t: a = b := cases then rfl" with
    | Some (Atom _ _), Some (Cases _ [] (Some _)) => True
    | _, _ => False

--| A `cases`'s names, if the expression is a `Cases`.
def casesNames: Option Expr → Option (List Text)
  | Some (Cases _ targets _) => Some (targets.map (word => word.text))
  | _ => None

test "cases takes the names after it on its line, each later one after a comma, with or without then" :=
  casesNames (bodyOf "theorem t: P := cases a, b then rfl") == Some ["a", "b"]
    && casesNames (bodyOf "theorem t: P := cases a") == Some ["a"]
    && casesNames (bodyOf "theorem t: P :=\n  cases\n  a") == None

test "a name followed by => starts the next item, not a name for cases to split" :=
  tree "def f: P := [cases a, b, c => d]"
    == "Def\n  def\n  f\n  ResultType\n    :\n    P\n  Body\n    :=\n    List\n      [\n      Cases\n        cases\n        a\n        ,\n        b\n      ,\n      Lambda\n        c\n        =>\n        d\n      ]\n"

test "a rule set may end with a comma" :=
  tree "rules simps := [a, <- b,]"
    == "Rules\n  rules\n  simps\n  Body\n    :=\n    RewriteRules\n      [\n      RewriteRule\n        a\n      ,\n      RewriteRule\n        <\n        -\n        b\n      ,\n      ]\n"

test "brackets pair by kind when looking for a lambda" :=
  tree "def f: Nat := [a: (x: Type] a) => x" == "error: expected `)` to close the parameter `(x: …`, but found `]`"

test "a lambda has no result type" :=
  tree "def f: Nat := (x: A): B => x" == "error: a lambda doesn't take a result type"
