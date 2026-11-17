--| The tree's expressions and patterns (stage 2a), and their dump in
--| `stitchwort dev tree --print`'s form.
--|
--| What the tree keeps of a token is what printing must reproduce and
--| nothing of the author's layout (tools/fmt-sketch/SKETCH.md §1): its
--| text and its comments, a `Word`, with no column, no "starts its line"
--| and no count of blank lines. Commas aren't kept, since rule N leaves
--| them no comments: a list keeps its items and whether a comma followed
--| the last (`trailingComma`), and the dump writes the `,` lines back.
--|
--| A constructor is a shape, with a tag where shapes coincide (`Infix`
--| for every "left, operator, right"); the dump prints the Rust
--| `NodeKind` each stands for. A token with no node of its own (a name, a
--| number, a text, `_`) is an `Atom`, tagged with its token kind, which
--| the parser's checks read (a text before `++` in a pattern, a name an
--| or-pattern would bind).

namespace Syntax
import Std (Bool, List, Nat, Option, Text)

--| An own-line comment, `--` included, and whether a blank line was above
--| it.
type Note = { text: Text, blankBefore: Bool }

--| The comments a token holds once rule N has run: the own-line comments
--| above it, in order, and the trailing comment after it on its line.
type Comments = { above: List Note, after: Option Text }

--| A token in the tree: its text as written and its comments.
type Word = { text: Text, comments: Comments }

--| A leaf's text and comments; its layout is left behind.
def Leaf.word (leaf: Leaf): Word :=
  let above := leaf.trivia.leading.map (comment => { text = comment.text, blankBefore = comment.blankLines > 0 })
  { text = leaf.token.text, comments = { above, after = leaf.trivia.trailing.map (comment => comment.text) } }

--| The "left, operator, right" kinds.
type InfixKind =
  | InfixBinary
  | InfixMembership
  | InfixRange
  | InfixPipe
  | InfixArrow
  | InfixIff
  | InfixSeq

def InfixKind.name: InfixKind → Text
  | InfixBinary => "Binary"
  | InfixMembership => "Membership"
  | InfixRange => "Range"
  | InfixPipe => "Pipe"
  | InfixArrow => "Arrow"
  | InfixIff => "Iff"
  | InfixSeq => "Seq"

--| What binds parameters before a `=>`.
type BindingKind = | BindsLambda | BindsForall | BindsExists

def BindingKind.name: BindingKind → Text
  | BindsLambda => "Lambda"
  | BindsForall => "Forall"
  | BindsExists => "Exists"

--| `arithmetic [h]` (`Omega`) or `algebra [h]` (`Ring`).
type FactsKind = | FactsOmega | FactsRing

type Expr =
  --| A token alone: a name, a number, a text, `_`, `?`, `Type`.
  | Atom (kind: Tok) (word: Word)
  | Paren (open: Word) (inner: Expr) (close: Word)
  | Unit (open: Word) (close: Word)
  --| `Type 1`
  | Universe (keyword: Word) (level: Word)
  | Include (keyword: Word) (path: Word)
  | Tuple (open: Word) (items: List Expr) (trailingComma: Bool) (close: Word)
  --| `List`: `[a, ..xs]`, its spreads `Spread`s among the items.
  | ListOf (open: Word) (items: List Expr) (trailingComma: Bool) (close: Word)
  | Spread (dots: Word) (list: Expr)
  --| `{ x = 1, y }` or `{ r | x = 1 }`: `base` is the updated record and
  --| its `|`. A field is a `RecordField`, or an `Atom` when punned.
  | Record (open: Word) (base: Option (Expr, Word)) (fields: List Expr) (trailingComma: Bool) (close: Word)
  | RecordField (name: Word) (equals: Word) (value: Expr)
  | CtorFields (ctor: Expr) (record: Expr)
  --| `f a b`, one node however many arguments.
  | App (head: Expr) (arguments: List Expr)
  --| `(x := e)` or `[x := e]`.
  | NamedArg (open: Word) (name: Word) (colonEq: Word) (value: Expr) (close: Word)
  --| `e.f`, or `.f` (no receiver) at the start of a method section.
  | FieldAccess (target: Option Expr) (dot: Word) (field: Word)
  | Section (body: Expr)
  --| `(+ 1)`, `(k +)`, `(&&)`.
  | OperatorSection (open: Word) (left: Option Expr) (operator: Word) (right: Option Expr) (close: Word)
  --| `a + b`, `x ∈ xs`, `a ..< b`, `x |> f`, `A → B`, `p ↔ q`, `a; b`.
  | Infix (kind: InfixKind) (left: Expr) (operator: Word) (right: Expr)
  --| `a ≤ b < c`: the first operand, then each operator and operand.
  | Chain (first: Expr) (rest: List (Word, Expr))
  | Prefix (operator: Word) (operand: Expr)
  --| `x (a, b) => e`, `∀ x => P`, `∃ x => P`: the keyword (for `∀` and
  --| `∃`), the parameters, `=>` and the body.
  | Binding (kind: BindingKind) (keyword: Option Word) (params: List Param) (arrow: Word) (body: Expr)
  --| `if c then a else b`; `binder` is `h` and `:` in `if h: c then …`.
  | If
      (keyword: Word)
      (binder: Option (Word, Word))
      (condition: Expr)
      (thenKeyword: Word)
      (whenTrue: Expr)
      (elseKeyword: Word)
      (whenFalse: Expr)
  | Annotation (open: Word) (value: Expr) (colon: Word) (annotation: Expr) (close: Word)
  --| `"a${x}b"`: the text pieces and the interpolations between them.
  | Interpolated (pieces: List Piece)
  --| `match e, f with | …`
  | Match (keyword: Word) (scrutinees: List Scrutinee) (withKeyword: Word) (arms: List Arm)
  --| `match | …`, `match some | …` (`some` is `word`), `matches | …` (the
  --| keyword is `matches`).
  | ClauseLambda (keyword: Word) (word: Option Word) (arms: List Arm)
  --| `arithmetic [h]` or `algebra [h]`: the keyword and its facts, a list.
  | Facts (kind: FactsKind) (keyword: Word) (facts: Expr)

--| A piece of an interpolated text: a token of text, or `${e}`.
type Piece =
  | TextPiece (word: Word)
  | Interpolation (open: Word) (value: Expr) (close: Word)

--| A lambda's (or `∀`'s, `∃`'s) parameter: a name or `_`, a pattern, or a
--| `LambdaParam` with a written type, `(x y: A)` or `[a: Type]`;
--| `[auto P]` has `auto` for its names and no colon.
type Param =
  | NameParam (word: Word)
  | PatternParam (pattern: Pattern)
  | TypedParam (open: Word) (names: List Word) (colon: Option Word) (annotation: Expr) (close: Word)
  --| `PatternTyped`: `((a, b): A)`.
  | TypedPattern (open: Word) (pattern: Pattern) (colon: Word) (annotation: Expr) (close: Word)

--| One matched expression, `h: e` or `e`.
type Scrutinee = { name: Option (Word, Word), value: Expr }

--| `| p, q if c => e`; with an absurd pattern and no `=>`, no body. A
--| `matches` arm may stop after its guard.
type Arm = {
  bar: Word,
  patterns: List Pattern,
  guard: Option Guard,
  body: Option (Word, Expr)
}

--| `if c` or `if h: c` after an arm's patterns.
type Guard = { keyword: Word, binder: Option (Word, Word), condition: Expr }

type Pattern =
  --| A token alone: a name, a constructor, a literal, `_`.
  | PatternWord (kind: Tok) (word: Word)
  --| `Cons x xs`: its arguments are patterns, `PatternNegative`s and
  --| `PatternRecord`s.
  | PatternCtor (name: Word) (arguments: List Pattern)
  | PatternCtorFields (name: Word) (fields: FieldsPattern)
  | PatternRecord (fields: FieldsPattern)
  | PatternTuple (open: Word) (items: List Pattern) (trailingComma: Bool) (close: Word)
  --| `[a, ..rest]`: the items, then the tail's `..` and pattern; a comma
  --| stands before the tail when there are items.
  | PatternList (open: Word) (items: List Pattern) (trailingComma: Bool) (tail: Option (Word, Pattern)) (close: Word)
  | PatternNamed (open: Word) (name: Word) (colonEq: Word) (value: Pattern) (close: Word)
  | PatternOr (first: Pattern) (rest: List (Word, Pattern))
  | PatternParen (open: Word) (inner: Pattern) (close: Word)
  | PatternNegative (minus: Word) (number: Word)
  | PatternAbsurd (open: Word) (close: Word)
  | PatternAppend (start: Pattern) (operator: Word) (rest: Pattern)

--| `{ x, y = p, .. }`, which has no node of its own; a comma stands before
--| the `..` when there are fields.
type FieldsPattern = {
  open: Word,
  fields: List FieldPattern,
  trailingComma: Bool,
  rest: Option Word,
  close: Word
}

--| `x` or `x = p` in a record pattern.
type FieldPattern = { name: Word, value: Option (Word, Pattern) }

-- The dump: each node's kind on a line, its children one level deeper.
-- Each node gives its lines as a list, joined once at the end: building one
-- text from the pieces of the next would copy the rest of a long list once
-- per item.

def Expr.dump (expr: Expr) (depth: Nat): Text := Text.concat (expr.lines depth)

def Word.line (word: Word) (depth: Nat): List Text := ["${indent depth}${word.text}\n"]

def commaLine (depth: Nat): List Text := ["${indent depth},\n"]

--| A node's line, then its children's lines (already one level deeper).
def node (depth: Nat) (kind: Text) (children: List Text): List Text := [nodeLine depth kind, ..children]

def Expr.lines (expr: Expr) (depth: Nat): List Text :=
  let d := depth + 1
  match expr with
    | Atom _ word => word.line depth
    | Paren open inner close => node depth "Paren" (open.line d ++ inner.lines d ++ close.line d)
    | Unit open close => node depth "Unit" (open.line d ++ close.line d)
    | Universe keyword level => node depth "Universe" (keyword.line d ++ level.line d)
    | Include keyword path => node depth "Include" (keyword.line d ++ path.line d)
    | Tuple open items trailingComma close =>
      node depth "Tuple" (open.line d ++ commaExprs d trailingComma items ++ close.line d)
    | ListOf open items trailingComma close =>
      node depth "List" (open.line d ++ commaExprs d trailingComma items ++ close.line d)
    | Spread dots list => node depth "Spread" (dots.line d ++ list.lines d)
    | Record open base fields trailingComma close =>
      let based := match base with
        | Some (record, bar) => record.lines d ++ bar.line d
        | None => []
      node depth "Record" (open.line d ++ based ++ commaExprs d trailingComma fields ++ close.line d)
    | RecordField name equals value => node depth "RecordField" (name.line d ++ equals.line d ++ value.lines d)
    | CtorFields ctor record => node depth "CtorFields" (ctor.lines d ++ record.lines d)
    | App head arguments => node depth "App" (head.lines d ++ exprLines d arguments)
    | NamedArg open name colonEq value close =>
      node depth "NamedArg" (open.line d ++ name.line d ++ colonEq.line d ++ value.lines d ++ close.line d)
    | FieldAccess target dot field =>
      let receiver := match target with
        | Some target => target.lines d
        | None => []
      node depth "FieldAccess" (receiver ++ dot.line d ++ field.line d)
    | Section body => node depth "Section" (body.lines d)
    | OperatorSection open left operator right close =>
      let leftPart := match left with
        | Some left => left.lines d
        | None => []
      let rightPart := match right with
        | Some right => right.lines d
        | None => []
      node depth "OperatorSection" (open.line d ++ leftPart ++ operator.line d ++ rightPart ++ close.line d)
    | Infix kind left operator right => node depth kind.name (left.lines d ++ operator.line d ++ right.lines d)
    | Chain first rest => node depth "Chain" (first.lines d ++ linkLines d rest)
    | Prefix operator operand => node depth "Prefix" (operator.line d ++ operand.lines d)
    | Binding kind keyword params arrow body =>
      node depth kind.name (wordLines d keyword ++ paramLines d params ++ arrow.line d ++ body.lines d)
    | If keyword binder condition thenKeyword whenTrue elseKeyword whenFalse =>
      node depth "If"
        (keyword.line d
          ++ binderLines d binder
          ++ condition.lines d
          ++ thenKeyword.line d
          ++ whenTrue.lines d
          ++ elseKeyword.line d
          ++ whenFalse.lines d)
    | Annotation open value colon annotation close =>
      node depth "Annotation" (open.line d ++ value.lines d ++ colon.line d ++ annotation.lines d ++ close.line d)
    | Interpolated pieces => node depth "Interpolated" (pieceLines d pieces)
    | Match keyword scrutinees withKeyword arms =>
      node depth "Match" (keyword.line d ++ scrutineeLines d scrutinees ++ withKeyword.line d ++ armLines d arms)
    | ClauseLambda keyword word arms =>
      node depth "ClauseLambda" (keyword.line d ++ wordLines d word ++ armLines d arms)
    | Facts kind keyword facts =>
      let name := match kind with
        | FactsOmega => "Omega"
        | FactsRing => "Ring"
      node depth name (keyword.line d ++ facts.lines d)

def wordLines (depth: Nat): Option Word → List Text
  | Some word => word.line depth
  | None => []

def binderLines (depth: Nat): Option (Word, Word) → List Text
  | Some (name, colon) => name.line depth ++ colon.line depth
  | None => []

def exprLines (depth: Nat): List Expr → List Text
  | [] => []
  | [first, ..rest] => first.lines depth ++ exprLines depth rest

--| Items with a `,` line between each two, and after the last if
--| `trailingComma`.
def commaExprs (depth: Nat) (trailingComma: Bool): List Expr → List Text
  | [] => []
  | [last] => last.lines depth ++ (if trailingComma then commaLine depth else [])
  | [first, ..rest] => first.lines depth ++ commaLine depth ++ commaExprs depth trailingComma rest

def linkLines (depth: Nat): List (Word, Expr) → List Text
  | [] => []
  | [(operator, operand), ..rest] => operator.line depth ++ operand.lines depth ++ linkLines depth rest

def pieceLines (depth: Nat): List Piece → List Text
  | [] => []
  | [TextPiece word, ..rest] => word.line depth ++ pieceLines depth rest
  | [Interpolation open value close, ..rest] =>
    let d := depth + 1
    node depth "Interpolation" (open.line d ++ value.lines d ++ close.line d) ++ pieceLines depth rest

def paramLines (depth: Nat): List Param → List Text
  | [] => []
  | [NameParam word, ..rest] => word.line depth ++ paramLines depth rest
  | [PatternParam pattern, ..rest] => pattern.lines depth ++ paramLines depth rest
  | [TypedParam open names colon annotation close, ..rest] =>
    let d := depth + 1
    node depth "LambdaParam"
      (open.line d ++ wordsLines d names ++ wordLines d colon ++ annotation.lines d ++ close.line d)
      ++ paramLines depth rest
  | [TypedPattern open pattern colon annotation close, ..rest] =>
    let d := depth + 1
    node depth "PatternTyped" (open.line d ++ pattern.lines d ++ colon.line d ++ annotation.lines d ++ close.line d)
      ++ paramLines depth rest

def wordsLines (depth: Nat): List Word → List Text
  | [] => []
  | [word, ..rest] => word.line depth ++ wordsLines depth rest

--| Scrutinees, a `,` line between each two.
def scrutineeLines (depth: Nat): List Scrutinee → List Text
  | [] => []
  | [{ name, value }] => node depth "Scrutinee" (binderLines (depth + 1) name ++ value.lines (depth + 1))
  | [{ name, value }, ..rest] =>
    node depth "Scrutinee" (binderLines (depth + 1) name ++ value.lines (depth + 1))
      ++ commaLine depth
      ++ scrutineeLines depth rest

def armLines (depth: Nat): List Arm → List Text
  | [] => []
  | [{ bar, patterns, guard, body }, ..rest] =>
    let d := depth + 1
    let guarded := match guard with
      | Some { keyword, binder, condition } =>
        node d "Guard" (keyword.line (d + 1) ++ binderLines (d + 1) binder ++ condition.lines (d + 1))
      | None => []
    let bodied := match body with
      | Some (arrow, value) => arrow.line d ++ value.lines d
      | None => []
    node depth "Arm" (bar.line d ++ commaPatterns d False patterns ++ guarded ++ bodied) ++ armLines depth rest

def Pattern.lines (pattern: Pattern) (depth: Nat): List Text :=
  let d := depth + 1
  match pattern with
    | PatternWord _ word => word.line depth
    | PatternCtor name arguments => node depth "PatternCtor" (name.line d ++ patternLines d arguments)
    | PatternCtorFields name fields => node depth "PatternCtorFields" (name.line d ++ fieldsLines d fields)
    | PatternRecord fields => node depth "PatternRecord" (fieldsLines d fields)
    | PatternTuple open items trailingComma close =>
      node depth "PatternTuple" (open.line d ++ commaPatterns d trailingComma items ++ close.line d)
    | PatternList open items trailingComma tail close =>
      let tailed := match tail with
        | Some (dots, rest) => (if items.isEmpty then [] else commaLine d) ++ dots.line d ++ rest.lines d
        | None => []
      node depth "PatternList" (open.line d ++ commaPatterns d trailingComma items ++ tailed ++ close.line d)
    | PatternNamed open name colonEq value close =>
      node depth "PatternNamed" (open.line d ++ name.line d ++ colonEq.line d ++ value.lines d ++ close.line d)
    | PatternOr first rest => node depth "PatternOr" (first.lines d ++ patternLinkLines d rest)
    | PatternParen open inner close => node depth "PatternParen" (open.line d ++ inner.lines d ++ close.line d)
    | PatternNegative minus number => node depth "PatternNegative" (minus.line d ++ number.line d)
    | PatternAbsurd open close => node depth "PatternAbsurd" (open.line d ++ close.line d)
    | PatternAppend start operator rest => node depth "PatternAppend" (start.lines d ++ operator.line d ++ rest.lines d)

def patternLines (depth: Nat): List Pattern → List Text
  | [] => []
  | [first, ..rest] => first.lines depth ++ patternLines depth rest

def commaPatterns (depth: Nat) (trailingComma: Bool): List Pattern → List Text
  | [] => []
  | [last] => last.lines depth ++ (if trailingComma then commaLine depth else [])
  | [first, ..rest] => first.lines depth ++ commaLine depth ++ commaPatterns depth trailingComma rest

def patternLinkLines (depth: Nat): List (Word, Pattern) → List Text
  | [] => []
  | [(bar, alternative), ..rest] => bar.line depth ++ alternative.lines depth ++ patternLinkLines depth rest

--| `{ … }`; a `,` line stands before `..` when there are fields.
def fieldsLines (depth: Nat): FieldsPattern → List Text
  | { open, fields, trailingComma, rest, close } =>
    let restLines := match rest with
      | Some dots => (if fields.isEmpty then [] else commaLine depth) ++ dots.line depth
      | None => []
    open.line depth ++ fieldPatternLines depth trailingComma fields ++ restLines ++ close.line depth

def fieldPatternLines (depth: Nat) (trailingComma: Bool): List FieldPattern → List Text
  | [] => []
  | [last] => fieldLines depth last ++ (if trailingComma then commaLine depth else [])
  | [first, ..rest] => fieldLines depth first ++ commaLine depth ++ fieldPatternLines depth trailingComma rest

def fieldLines (depth: Nat): FieldPattern → List Text
  | { name, value = Some (equals, pattern) } => name.line depth ++ equals.line depth ++ pattern.lines depth
  | { name, value = None } => name.line depth
