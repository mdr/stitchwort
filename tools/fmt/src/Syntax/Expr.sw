--| The tree's expressions and patterns (stage 2a): a constructor for each
--| of `crates/syntax`'s expression and pattern `NodeKind`s that stage 2a
--| parses, holding its tokens as `Leaf`s and its parts as subtrees, in the
--| order written, so the dump can print it as `dev tree --print` does.
--|
--| A token that stands alone, with no node of its own in the Rust tree (a
--| name, a number, a text, `_`), is a `Word`. Each constructor's comment
--| names its Rust `NodeKind` where the two names differ.

namespace Syntax
import Std (List, Nat, Option, Text)

--| An item of a list written with commas, and the comma after it, if one
--| was written: the last item's is a trailing comma.
type Sep (a: Type) = { item: a, comma: Option Leaf }

type Expr =
  | Word (leaf: Leaf)
  | Paren (open: Leaf) (inner: Expr) (close: Leaf)
  | Unit (open: Leaf) (close: Leaf)
  --| `Type 1`
  | Universe (keyword: Leaf) (level: Leaf)
  | Include (keyword: Leaf) (path: Leaf)
  | Tuple (open: Leaf) (items: List (Sep Expr)) (close: Leaf)
  --| `List`: `[a, ..xs]`, its spreads `Spread`s among the items.
  | ListOf (open: Leaf) (items: List (Sep Expr)) (close: Leaf)
  | Spread (dots: Leaf) (list: Expr)
  --| `{ x = 1, y }` or `{ r | x = 1 }`: `base` is the updated record and
  --| its `|`. A field is a `RecordField`, or a `Word` when punned.
  | Record (open: Leaf) (base: Option (Expr, Leaf)) (fields: List (Sep Expr)) (close: Leaf)
  | RecordField (name: Leaf) (equals: Leaf) (value: Expr)
  | CtorFields (ctor: Expr) (record: Expr)
  --| `f a b`, one node however many arguments.
  | App (head: Expr) (arguments: List Expr)
  --| `(x := e)` or `[x := e]`.
  | NamedArg (open: Leaf) (name: Leaf) (colonEq: Leaf) (value: Expr) (close: Leaf)
  --| `e.f`, or `.f` (no receiver) at the start of a method section.
  | FieldAccess (target: Option Expr) (dot: Leaf) (field: Leaf)
  | Section (body: Expr)
  --| `(+ 1)`, `(k +)`, `(&&)`.
  | OperatorSection (open: Leaf) (left: Option Expr) (operator: Leaf) (right: Option Expr) (close: Leaf)
  | Binary (left: Expr) (operator: Leaf) (right: Expr)
  --| `a ≤ b < c`: the first operand, then each operator and operand.
  | Chain (first: Expr) (rest: List (Leaf, Expr))
  | Membership (element: Expr) (operator: Leaf) (collection: Expr)
  | Range (low: Expr) (operator: Leaf) (high: Expr)
  | Prefix (operator: Leaf) (operand: Expr)
  | Piped (value: Expr) (operator: Leaf) (function: Expr)
  | ArrowType (domain: Expr) (arrow: Leaf) (codomain: Expr)
  | Iff (left: Expr) (operator: Leaf) (right: Expr)
  | Seq (first: Expr) (semicolon: Leaf) (rest: Expr)
  --| `x (a, b) => e`; with a keyword, `∀ x => P` (`Forall`) or `∃ x => P`
  --| (`Exists`), the keyword's token naming which.
  | Lambda (keyword: Option Leaf) (params: List Param) (arrow: Leaf) (body: Expr)
  --| `if c then a else b`; `binder` is `h` and `:` in `if h: c then …`.
  | If
      (keyword: Leaf)
      (binder: Option (Leaf, Leaf))
      (condition: Expr)
      (thenKeyword: Leaf)
      (whenTrue: Expr)
      (elseKeyword: Leaf)
      (whenFalse: Expr)
  | Annotation (open: Leaf) (value: Expr) (colon: Leaf) (annotation: Expr) (close: Leaf)
  --| `"a${x}b"`: the text pieces and the interpolations between them.
  | Interpolated (pieces: List Piece)
  --| `match e, f with | …`
  | Match (keyword: Leaf) (scrutinees: List (Sep Scrutinee)) (withKeyword: Leaf) (arms: List Arm)
  --| `match | …`, `match some | …` (`some` is `word`), `matches | …` (the
  --| keyword is `matches`).
  | ClauseLambda (keyword: Leaf) (word: Option Leaf) (arms: List Arm)
  --| `Omega` (`arithmetic [h]`) or `Ring` (`algebra [h]`): the keyword and
  --| its facts, a list.
  | Facts (keyword: Leaf) (facts: Expr)

--| A piece of an interpolated text: a token of text, or `${e}`.
type Piece =
  | TextPiece (leaf: Leaf)
  | Interpolation (open: Leaf) (value: Expr) (close: Leaf)

--| A lambda's (or `∀`'s, `∃`'s) parameter: a name or `_`, a pattern, or a
--| `LambdaParam` with a written type, `(x y: A)` or `[a: Type]`;
--| `[auto P]` has `auto` for its names and no colon.
type Param =
  | NameParam (leaf: Leaf)
  | PatternParam (pattern: Pattern)
  | TypedParam (open: Leaf) (names: List Leaf) (colon: Option Leaf) (annotation: Expr) (close: Leaf)
  --| `PatternTyped`: `((a, b): A)`.
  | TypedPattern (open: Leaf) (pattern: Pattern) (colon: Leaf) (annotation: Expr) (close: Leaf)

--| One matched expression, `h: e` or `e`.
type Scrutinee = { name: Option (Leaf, Leaf), value: Expr }

--| `| p, q if c => e`; with an absurd pattern and no `=>`, no body. A
--| `matches` arm may stop after its guard.
type Arm = {
  bar: Leaf,
  patterns: List (Sep Pattern),
  guard: Option Guard,
  body: Option (Leaf, Expr)
}

--| `if c` or `if h: c` after an arm's patterns.
type Guard = { keyword: Leaf, binder: Option (Leaf, Leaf), condition: Expr }

type Pattern =
  | PatternWord (leaf: Leaf)
  --| `Cons x xs`: its arguments are patterns, `PatternNegative`s and
  --| `PatternRecord`s.
  | PatternCtor (name: Leaf) (arguments: List Pattern)
  | PatternCtorFields (name: Leaf) (fields: FieldsPattern)
  | PatternRecord (fields: FieldsPattern)
  | PatternTuple (open: Leaf) (items: List (Sep Pattern)) (close: Leaf)
  --| `[a, ..rest]`: the items, then the tail's `..` and pattern.
  | PatternList (open: Leaf) (items: List (Sep Pattern)) (tail: Option (Leaf, Pattern)) (close: Leaf)
  | PatternNamed (open: Leaf) (name: Leaf) (colonEq: Leaf) (value: Pattern) (close: Leaf)
  | PatternOr (first: Pattern) (rest: List (Leaf, Pattern))
  | PatternParen (open: Leaf) (inner: Pattern) (close: Leaf)
  | PatternNegative (minus: Leaf) (number: Leaf)
  | PatternAbsurd (open: Leaf) (close: Leaf)
  | PatternAppend (start: Pattern) (operator: Leaf) (rest: Pattern)

--| `{ x, y = p, .. }`, which has no node of its own.
type FieldsPattern = {
  open: Leaf,
  fields: List (Sep FieldPattern),
  rest: Option Leaf,
  close: Leaf
}

--| `x` or `x = p` in a record pattern.
type FieldPattern = { name: Leaf, value: Option (Leaf, Pattern) }

-- The dump: each node's kind on a line, its children one level deeper.

def Expr.dump (expr: Expr) (depth: Nat): Text := match expr with
  | Word leaf => leaf.treeLine depth
  | Paren open inner close =>
    node depth "Paren" "${open.treeLine (depth + 1)}${inner.dump (depth + 1)}${close.treeLine (depth + 1)}"
  | Unit open close => node depth "Unit" "${open.treeLine (depth + 1)}${close.treeLine (depth + 1)}"
  | Universe keyword level => node depth "Universe" "${keyword.treeLine (depth + 1)}${level.treeLine (depth + 1)}"
  | Include keyword path => node depth "Include" "${keyword.treeLine (depth + 1)}${path.treeLine (depth + 1)}"
  | Tuple open items close =>
    node depth "Tuple" "${open.treeLine (depth + 1)}${dumpSepExprs (depth + 1) items}${close.treeLine (depth + 1)}"
  | ListOf open items close =>
    node depth "List" "${open.treeLine (depth + 1)}${dumpSepExprs (depth + 1) items}${close.treeLine (depth + 1)}"
  | Spread dots list => node depth "Spread" "${dots.treeLine (depth + 1)}${list.dump (depth + 1)}"
  | Record open base fields close =>
    let based := match base with
      | Some (record, bar) => "${record.dump (depth + 1)}${bar.treeLine (depth + 1)}"
      | None => ""
    node depth "Record"
      "${open.treeLine (depth + 1)}${based}${dumpSepExprs (depth + 1) fields}${close.treeLine (depth + 1)}"
  | RecordField name equals value =>
    node depth "RecordField" "${name.treeLine (depth + 1)}${equals.treeLine (depth + 1)}${value.dump (depth + 1)}"
  | CtorFields ctor record => node depth "CtorFields" "${ctor.dump (depth + 1)}${record.dump (depth + 1)}"
  | App head arguments => node depth "App" "${head.dump (depth + 1)}${dumpExprs (depth + 1) arguments}"
  | NamedArg open name colonEq value close =>
    node depth "NamedArg"
      "${open.treeLine (depth + 1)}${name.treeLine (depth + 1)}${colonEq.treeLine (depth + 1)}${value.dump (depth + 1)}${close.treeLine (depth + 1)}"
  | FieldAccess target dot field =>
    let receiver := match target with
      | Some target => target.dump (depth + 1)
      | None => ""
    node depth "FieldAccess" "${receiver}${dot.treeLine (depth + 1)}${field.treeLine (depth + 1)}"
  | Section body => node depth "Section" (body.dump (depth + 1))
  | OperatorSection open left operator right close =>
    let leftPart := match left with
      | Some left => left.dump (depth + 1)
      | None => ""
    let rightPart := match right with
      | Some right => right.dump (depth + 1)
      | None => ""
    node depth "OperatorSection"
      "${open.treeLine (depth + 1)}${leftPart}${operator.treeLine (depth + 1)}${rightPart}${close.treeLine (depth + 1)}"
  | Binary left operator right => infix depth "Binary" (left.dump (depth + 1)) operator (right.dump (depth + 1))
  | Chain first rest => node depth "Chain" "${first.dump (depth + 1)}${dumpLinks (depth + 1) rest}"
  | Membership element operator collection =>
    infix depth "Membership" (element.dump (depth + 1)) operator (collection.dump (depth + 1))
  | Range low operator high => infix depth "Range" (low.dump (depth + 1)) operator (high.dump (depth + 1))
  | Prefix operator operand => node depth "Prefix" "${operator.treeLine (depth + 1)}${operand.dump (depth + 1)}"
  | Piped value operator function => infix depth "Pipe" (value.dump (depth + 1)) operator (function.dump (depth + 1))
  | ArrowType domain arrow codomain => infix depth "Arrow" (domain.dump (depth + 1)) arrow (codomain.dump (depth + 1))
  | Iff left operator right => infix depth "Iff" (left.dump (depth + 1)) operator (right.dump (depth + 1))
  | Seq first semicolon rest => infix depth "Seq" (first.dump (depth + 1)) semicolon (rest.dump (depth + 1))
  | Lambda keyword params arrow body =>
    let (kind, word) := match keyword with
      | Some keyword => (if keyword.token.kind == KwForall then "Forall" else "Exists", keyword.treeLine (depth + 1))
      | None => ("Lambda", "")
    node depth kind "${word}${dumpParams (depth + 1) params}${arrow.treeLine (depth + 1)}${body.dump (depth + 1)}"
  | If keyword binder condition thenKeyword whenTrue elseKeyword whenFalse =>
    node depth "If"
      "${keyword.treeLine (depth + 1)}${dumpBinder (depth + 1) binder}${condition.dump (depth + 1)}${thenKeyword.treeLine (depth + 1)}${whenTrue.dump (depth + 1)}${elseKeyword.treeLine (depth + 1)}${whenFalse.dump (depth + 1)}"
  | Annotation open value colon annotation close =>
    node depth "Annotation"
      "${open.treeLine (depth + 1)}${value.dump (depth + 1)}${colon.treeLine (depth + 1)}${annotation.dump (depth + 1)}${close.treeLine (depth + 1)}"
  | Interpolated pieces => node depth "Interpolated" (dumpPieces (depth + 1) pieces)
  | Match keyword scrutinees withKeyword arms =>
    node depth "Match"
      "${keyword.treeLine (depth + 1)}${dumpScrutinees (depth + 1) scrutinees}${withKeyword.treeLine (depth + 1)}${dumpArms (depth + 1) arms}"
  | ClauseLambda keyword word arms =>
    node depth "ClauseLambda" "${keyword.treeLine (depth + 1)}${dumpLeaf (depth + 1) word}${dumpArms (depth + 1) arms}"
  | Facts keyword facts =>
    node depth
      (if keyword.token.kind == KwArithmetic then "Omega" else "Ring")
      "${keyword.treeLine (depth + 1)}${facts.dump (depth + 1)}"

--| A node's line, then its children's lines (already one level deeper).
def node (depth: Nat) (kind children: Text): Text := "${nodeLine depth kind}${children}"

--| A node of an operand, an operator token and an operand.
def infix (depth: Nat) (kind left: Text) (operator: Leaf) (right: Text): Text :=
  node depth kind "${left}${operator.treeLine (depth + 1)}${right}"

def dumpLeaf (depth: Nat): Option Leaf → Text
  | Some leaf => leaf.treeLine depth
  | None => ""

def dumpBinder (depth: Nat): Option (Leaf, Leaf) → Text
  | Some (name, colon) => "${name.treeLine depth}${colon.treeLine depth}"
  | None => ""

def dumpExprs (depth: Nat): List Expr → Text
  | [] => ""
  | [first, ..rest] => "${first.dump depth}${dumpExprs depth rest}"

def dumpSepExprs (depth: Nat): List (Sep Expr) → Text
  | [] => ""
  | [{ item, comma }, ..rest] => "${item.dump depth}${dumpLeaf depth comma}${dumpSepExprs depth rest}"

def dumpLinks (depth: Nat): List (Leaf, Expr) → Text
  | [] => ""
  | [(operator, operand), ..rest] => "${operator.treeLine depth}${operand.dump depth}${dumpLinks depth rest}"

def dumpPieces (depth: Nat): List Piece → Text
  | [] => ""
  | [TextPiece leaf, ..rest] => "${leaf.treeLine depth}${dumpPieces depth rest}"
  | [Interpolation open value close, ..rest] =>
    let inner := "${open.treeLine (depth + 1)}${value.dump (depth + 1)}${close.treeLine (depth + 1)}"
    "${node depth "Interpolation" inner}${dumpPieces depth rest}"

def dumpParams (depth: Nat): List Param → Text
  | [] => ""
  | [NameParam leaf, ..rest] => "${leaf.treeLine depth}${dumpParams depth rest}"
  | [PatternParam pattern, ..rest] => "${pattern.dump depth}${dumpParams depth rest}"
  | [TypedParam open names colon annotation close, ..rest] =>
    let inner :=
      "${open.treeLine (depth + 1)}${dumpLeaves (depth + 1) names}${dumpLeaf (depth + 1) colon}${annotation.dump (depth + 1)}${close.treeLine (depth + 1)}"
    "${node depth "LambdaParam" inner}${dumpParams depth rest}"
  | [TypedPattern open pattern colon annotation close, ..rest] =>
    let inner :=
      "${open.treeLine (depth + 1)}${pattern.dump (depth + 1)}${colon.treeLine (depth + 1)}${annotation.dump (depth + 1)}${close.treeLine (depth + 1)}"
    "${node depth "PatternTyped" inner}${dumpParams depth rest}"

def dumpLeaves (depth: Nat): List Leaf → Text
  | [] => ""
  | [leaf, ..rest] => "${leaf.treeLine depth}${dumpLeaves depth rest}"

def dumpScrutinees (depth: Nat): List (Sep Scrutinee) → Text
  | [] => ""
  | [{ item = { name, value }, comma }, ..rest] =>
    let inner := "${dumpBinder (depth + 1) name}${value.dump (depth + 1)}"
    "${node depth "Scrutinee" inner}${dumpLeaf depth comma}${dumpScrutinees depth rest}"

def dumpArms (depth: Nat): List Arm → Text
  | [] => ""
  | [{ bar, patterns, guard, body }, ..rest] =>
    let guarded := match guard with
      | Some { keyword, binder, condition } =>
        node
          (depth + 1)
          "Guard"
          "${keyword.treeLine (depth + 2)}${dumpBinder (depth + 2) binder}${condition.dump (depth + 2)}"
      | None => ""
    let bodied := match body with
      | Some (arrow, value) => "${arrow.treeLine (depth + 1)}${value.dump (depth + 1)}"
      | None => ""
    let inner := "${bar.treeLine (depth + 1)}${dumpSepPatterns (depth + 1) patterns}${guarded}${bodied}"
    "${node depth "Arm" inner}${dumpArms depth rest}"

def Pattern.dump (pattern: Pattern) (depth: Nat): Text := match pattern with
  | PatternWord leaf => leaf.treeLine depth
  | PatternCtor name arguments =>
    node depth "PatternCtor" "${name.treeLine (depth + 1)}${dumpPatterns (depth + 1) arguments}"
  | PatternCtorFields name fields =>
    node depth "PatternCtorFields" "${name.treeLine (depth + 1)}${dumpFields (depth + 1) fields}"
  | PatternRecord fields => node depth "PatternRecord" (dumpFields (depth + 1) fields)
  | PatternTuple open items close =>
    node depth "PatternTuple"
      "${open.treeLine (depth + 1)}${dumpSepPatterns (depth + 1) items}${close.treeLine (depth + 1)}"
  | PatternList open items tail close =>
    let tailed := match tail with
      | Some (dots, rest) => "${dots.treeLine (depth + 1)}${rest.dump (depth + 1)}"
      | None => ""
    node depth "PatternList"
      "${open.treeLine (depth + 1)}${dumpSepPatterns (depth + 1) items}${tailed}${close.treeLine (depth + 1)}"
  | PatternNamed open name colonEq value close =>
    node depth "PatternNamed"
      "${open.treeLine (depth + 1)}${name.treeLine (depth + 1)}${colonEq.treeLine (depth + 1)}${value.dump (depth + 1)}${close.treeLine (depth + 1)}"
  | PatternOr first rest => node depth "PatternOr" "${first.dump (depth + 1)}${dumpPatternLinks (depth + 1) rest}"
  | PatternParen open inner close =>
    node depth "PatternParen" "${open.treeLine (depth + 1)}${inner.dump (depth + 1)}${close.treeLine (depth + 1)}"
  | PatternNegative minus number =>
    node depth "PatternNegative" "${minus.treeLine (depth + 1)}${number.treeLine (depth + 1)}"
  | PatternAbsurd open close => node depth "PatternAbsurd" "${open.treeLine (depth + 1)}${close.treeLine (depth + 1)}"
  | PatternAppend start operator rest =>
    infix depth "PatternAppend" (start.dump (depth + 1)) operator (rest.dump (depth + 1))

def dumpPatterns (depth: Nat): List Pattern → Text
  | [] => ""
  | [first, ..rest] => "${first.dump depth}${dumpPatterns depth rest}"

def dumpSepPatterns (depth: Nat): List (Sep Pattern) → Text
  | [] => ""
  | [{ item, comma }, ..rest] => "${item.dump depth}${dumpLeaf depth comma}${dumpSepPatterns depth rest}"

def dumpPatternLinks (depth: Nat): List (Leaf, Pattern) → Text
  | [] => ""
  | [(bar, alternative), ..rest] => "${bar.treeLine depth}${alternative.dump depth}${dumpPatternLinks depth rest}"

def dumpFields (depth: Nat): FieldsPattern → Text
  | { open, fields, rest, close } =>
    "${open.treeLine depth}${dumpFieldPatterns depth fields}${dumpLeaf depth rest}${close.treeLine depth}"

def dumpFieldPatterns (depth: Nat): List (Sep FieldPattern) → Text
  | [] => ""
  | [{ item = { name, value }, comma }, ..rest] =>
    let valued := match value with
      | Some (equals, pattern) => "${equals.treeLine depth}${pattern.dump depth}"
      | None => ""
    "${name.treeLine depth}${valued}${dumpLeaf depth comma}${dumpFieldPatterns depth rest}"
