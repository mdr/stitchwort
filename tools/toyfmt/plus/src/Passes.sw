--| The four passes (toy-plus-plus.md §3.2) and the traversal two of them
--| share (§3.4). Each pass is a function on trees, right on every tree; a
--| tree is tidy for a pass when the pass leaves it alone.

namespace Toy.Plus
import Toy.Syntax (Comment, Comments, Operator, Spaced)
import Std (Bool, List, NonEmptyList, Option, Text)

-- The shared traversal.

--| What an expression's place asks of its form: nothing (`Whole`: a
--| body's expression, an item, a condition, a bracket pair's content), a
--| postfix expression (a callee, a field's target), an operand (after
--| `-`), or a side of an operator of `level`.
type Slot =
  | Whole
  | PostfixSlot
  | OperandSlot
  | LeftOf (level: Nat)
  | RightOf (level: Nat)

--| Where an expression stands: its slot, and whether a bracket pair is
--| open around it (inside one, line starts and own-line comments don't
--| make blocks).
type Position = { bracketed: Bool, slot: Slot }

--| `expr` walked bottom-up: each expression inside it first, then
--| `step` at `expr` itself, told where it stands.
def Expr.walk (expr: Expr) (step: Position → Expr → Expr) (position: Position): Expr :=
  step position (expr.walkInside step position.bracketed)

--| `expr` with each expression directly inside it walked.
def Expr.walkInside (expr: Expr) (step: Position → Expr → Expr) (bracketed: Bool): Expr := match expr with
  | Bracketed open inner close => Bracketed open (inner.walk step { bracketed = True, slot = Whole }) close
  | ListLiteral open items trailingComma close => ListLiteral open (walkItems step items) trailingComma close
  | Call callee open arguments trailingComma close =>
    Call (callee.walk step { bracketed, slot = PostfixSlot }) open (walkItems step arguments) trailingComma close
  | Field target dot name nameComments =>
    Field (target.walk step { bracketed, slot = PostfixSlot }) dot name nameComments
  | Negate minus operand => Negate minus (operand.walk step { bracketed, slot = OperandSlot })
  | Binary operator sign left right =>
    Binary operator sign
      (left.walk step { bracketed, slot = LeftOf operator.level })
      (right.walk step { bracketed, slot = RightOf operator.level })
  | If ifComments condition thenComments whenTrue elseComments whenFalse =>
    If ifComments
      (condition.walk step { bracketed, slot = Whole })
      thenComments
      (whenTrue.walk step bracketed)
      elseComments
      (whenFalse.walk step bracketed)
  | leaf => leaf

def walkItems (step: Position → Expr → Expr): List Expr → List Expr
  | [] => []
  | [first, ..rest] => [first.walk step { bracketed = True, slot = Whole }, ..walkItems step rest]

def Body.walk (body: Body) (step: Position → Expr → Expr) (bracketed: Bool): Body := match body with
  | { statements } => { statements = walkLines step bracketed statements }

def walkLines (step: Position → Expr → Expr) (bracketed: Bool): List (Spaced Statement) → List (Spaced Statement)
  | [] => []
  | [{ blankBefore, line }, ..rest] =>
    [{ blankBefore, line = line.walk step bracketed }, ..walkLines step bracketed rest]

def Statement.walk (line: Statement) (step: Position → Expr → Expr) (bracketed: Bool): Statement := match line with
  | Let letComments name nameComments equals body => Let letComments name nameComments equals (body.walk step False)
  | Bare value => Bare (value.walk step { bracketed, slot = Whole })
  | note => note

--| Every expression of the file walked by `step`, and every
--| declaration by `declare` (which sees its body already walked).
def SourceFile.walk (file: SourceFile) (step: Position → Expr → Expr) (declare: Declaration → Declaration):
    SourceFile :=
  { declarations = walkDeclarations step declare file.declarations }

def walkDeclarations (step: Position → Expr → Expr) (declare: Declaration → Declaration):
    List (Spaced Declaration) → List (Spaced Declaration)
  | [] => []
  | [{ blankBefore, line }, ..rest] =>
    [{ blankBefore, line = declare (line.walkBody step) }, ..walkDeclarations step declare rest]

def Declaration.walkBody (line: Declaration) (step: Position → Expr → Expr): Declaration := match line with
  | Function fnComments name nameComments takes open groups trailingComma close equals body =>
    Function fnComments name nameComments takes open groups trailingComma close equals (body.walk step False)
  | Value letComments name nameComments equals body => Value letComments name nameComments equals (body.walk step False)
  | note => note

-- P1: `takes`.

--| P1: a function with parameters says `takes`.
def Declaration.withTakes: Declaration → Declaration
  | Function fnComments name nameComments None open [first, ..rest] trailingComma close equals body =>
    Function fnComments name nameComments (Some Comments.none) open [first, ..rest] trailingComma close equals body
  | other => other

def SourceFile.withTakes (file: SourceFile): SourceFile := file.walk (position expr => expr) Declaration.withTakes

-- P2: trailing commas.

def dropComma (position: Position) (expr: Expr): Expr := match expr with
  | ListLiteral open items _ close => ListLiteral open items False close
  | Call callee open arguments _ close => Call callee open arguments False close
  | other => other

def Declaration.withoutTrailingComma: Declaration → Declaration
  | Function fnComments name nameComments takes open groups _ close equals body =>
    Function fnComments name nameComments takes open groups False close equals body
  | other => other

--| P2: no list, call or parameter list has a comma after its last item.
def SourceFile.withoutTrailingCommas (file: SourceFile): SourceFile :=
  file.walk dropComma Declaration.withoutTrailingComma

-- P3: spare brackets.

def Expr.fits (expr: Expr) (slot: Slot): Bool := match slot with
  | Whole => True
  | PostfixSlot => expr.isPostfix
  | OperandSlot => expr.isOperand
  | LeftOf level => expr.isChain && level <= expr.chainLevel
  | RightOf level => expr.isChain && level < expr.chainLevel

--| Whether the expression, read inside brackets, could be read outside
--| them: there the first token of an `if`'s branch, with an own-line
--| comment above it, would start a block.
def Expr.standsOutside: Expr → Bool
  | Call callee _ _ _ _ => callee.standsOutside
  | Field target _ _ _ => target.standsOutside
  | Negate _ operand => operand.standsOutside
  | Binary _ _ left right => left.standsOutside && right.standsOutside
  | If _ condition _ whenTrue _ whenFalse =>
    condition.standsOutside && whenTrue.standsOutside && whenFalse.standsOutside
  | _ => True

def Body.standsOutside: Body → Bool
  | { statements } => linesStandOutside statements

def linesStandOutside: List (Spaced Statement) → Bool
  | [] => True
  | [{ line, .. }, ..rest] => line.standsOutside && linesStandOutside rest

def Statement.standsOutside: Statement → Bool
  | Bare value => value.firstAbove.isEmpty && value.standsOutside
  | _ => False

--| A bracket pair is dropped when neither bracket holds a comment, no
--| own-line comment is above its content's first token, and the content
--| may stand where the pair stood.
def dropPair (position: Position) (expr: Expr): Expr := match expr with
  | Bracketed open inner close if holdsNone open
      && holdsNone close
      && inner.firstAbove.isEmpty
      && inner.fits position.slot
      && (position.bracketed || inner.standsOutside) => inner
  | other => other

def TypeExpr.withoutSpareBrackets: TypeExpr → TypeExpr
  | TypeBracketed open inner close =>
    if holdsNone open && holdsNone close then inner.withoutSpareBrackets
    else TypeBracketed open inner.withoutSpareBrackets close
  | name => name

def ParameterGroup.withoutSpareBrackets: ParameterGroup → ParameterGroup
  | Typed names colon annotation => Typed names colon annotation.withoutSpareBrackets
  | untyped => untyped

def Declaration.withoutSpareBrackets: Declaration → Declaration
  | Function fnComments name nameComments takes open groups trailingComma close equals body =>
    Function fnComments name nameComments takes open
      (groups.map (group => group.withoutSpareBrackets))
      trailingComma
      close
      equals
      body
  | other => other

--| P3: no bracket pair that could go is left.
def SourceFile.withoutSpareBrackets (file: SourceFile): SourceFile :=
  file.walk dropPair (line => line.withoutSpareBrackets)

-- P4: parameter groups.

def TypeExpr.isNamed (annotation: TypeExpr) (name: Text): Bool := match annotation.bare with
  | TypeName found _ => found == name
  | _ => False

--| `group` before groups already merged: joined to the first of them if
--| it is typed by the same name and holds no comment of its own.
def mergeInto (group: ParameterGroup) (merged: List ParameterGroup): List ParameterGroup := match group, merged with
  | Typed names colon (TypeName name comments), [Typed others otherColon annotation, ..rest] if holdsNone colon
      && holdsNone comments
      && annotation.isNamed name => [Typed (names.append others) otherColon annotation, ..rest]
  | _, _ => [group, ..merged]

def mergeGroups: List ParameterGroup → List ParameterGroup
  | [] => []
  | [group, ..rest] => mergeInto group (mergeGroups rest)

def Declaration.withMergedParameters: Declaration → Declaration
  | Function fnComments name nameComments takes open groups trailingComma close equals body =>
    Function fnComments name nameComments takes open (mergeGroups groups) trailingComma close equals body
  | other => other

--| P4: neighbouring parameters of one type share it, `(w h: Int)`.
def SourceFile.withMergedParameters (file: SourceFile): SourceFile :=
  file.walk (position expr => expr) Declaration.withMergedParameters

--| The four passes, in order. P3 comes before P4: `(w: (Int), h: Int)`
--| merges only once its brackets are gone.
def SourceFile.tidy (file: SourceFile): SourceFile :=
  file.withTakes.withoutTrailingCommas.withoutSpareBrackets.withMergedParameters
