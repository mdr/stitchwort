--| The passes `format` runs between parsing and printing
--| (toy-plus-plus.md §3.2), in order: P1 `withTakes`, P2
--| `withoutTrailingCommas`, P3 `withoutSpareBrackets`, then P4
--| `withMergedParameters`. Each is a function on trees, right on every
--| tree, and a tree is tidy for a pass when the pass leaves it alone.

namespace Toy.Fmt
import Toy.Syntax (..)
import Std (Bool, List, NonEmptyList, Option, Text)

-- P1: `takes`, written on every function that has parameters.

--| The `takes` a function with `parameters` is printed with: one with no
--| comments where none was written, if there are parameters.
def takesFor (takes: Option Comments) (parameters: List ParameterGroup): Option Comments := match parameters with
  | [] => takes
  | [_, .._] => Some (takes.getOrElse Comments.none)

def Declaration.withTakes: Declaration → Declaration
  | Function fnComments name nameComments takes open parameters trailingComma close equals body =>
    Function fnComments name nameComments (takesFor takes parameters) open parameters trailingComma close equals body
  | other => other

def declarationsWithTakes: List (Spaced Declaration) → List (Spaced Declaration)
  | [] => []
  | [{ blankBefore, line }, ..rest] => [{ blankBefore, line = line.withTakes }, ..declarationsWithTakes rest]

def SourceFile.withTakes (file: SourceFile): SourceFile := { declarations = declarationsWithTakes file.declarations }

-- P2: no trailing commas. Rule N has left no comment on a comma, so
-- dropping one loses nothing.

--| P2's step: a list or call is written with no comma after its last
--| item.
def dropComma (position: Position) (expr: Expr): Expr := match expr with
  | ListLiteral open items _ close => ListLiteral open items False close
  | Call callee open arguments _ close => Call callee open arguments False close
  | other => other

def Declaration.withoutTrailingComma: Declaration → Declaration
  | Function fnComments name nameComments takes open parameters _ close equals body =>
    Function fnComments name nameComments takes open parameters False close equals body
  | other => other

--| P2: no list, call or parameter list has a comma after its last item.
def SourceFile.withoutTrailingCommas (file: SourceFile): SourceFile :=
  file.traverse dropComma (line => line.withoutTrailingComma)

-- P3: no spare brackets.

--| Whether the expression, read inside brackets, reads the same outside
--| them: there an own-line comment above the first token of a statement
--| in an `if`'s branch would start a block.
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
  | _ => True

--| Whether the pair `( inner )` can go at `position`: neither bracket
--| holds a comment, no own-line comment is above the content's first
--| token, the content is read as it stands in the pair's place
--| (precedence), and outside brackets it reads the same (`standsOutside`).
def spare (position: Position) (open: Comments) (inner: Expr) (close: Comments): Bool :=
  open.isNone
    && close.isNone
    && inner.firstAbove.isEmpty
    && inner.fits position.slot
    && (position.bracketed || inner.standsOutside)

--| P3's step: a spare pair is replaced by its content.
def dropPair (position: Position) (expr: Expr): Expr := match expr with
  | Bracketed open inner close => if spare position open inner close then inner else Bracketed open inner close
  | other => other

--| A type's brackets with no comments go: a type is a name wherever it
--| stands.
def TypeExpr.withoutSpareBrackets: TypeExpr → TypeExpr
  | TypeBracketed open inner close =>
    if open.isNone && close.isNone then inner.withoutSpareBrackets
    else TypeBracketed open inner.withoutSpareBrackets close
  | name => name

def ParameterGroup.withoutSpareBrackets: ParameterGroup → ParameterGroup
  | Typed names colon annotation => Typed names colon annotation.withoutSpareBrackets
  | untyped => untyped

def groupsWithoutSpareBrackets: List ParameterGroup → List ParameterGroup
  | [] => []
  | [group, ..rest] => [group.withoutSpareBrackets, ..groupsWithoutSpareBrackets rest]

def Declaration.withoutSpareTypeBrackets: Declaration → Declaration
  | Function fnComments name nameComments takes open parameters trailingComma close equals body =>
    Function fnComments name nameComments takes open
      (groupsWithoutSpareBrackets parameters)
      trailingComma
      close
      equals
      body
  | other => other

--| P3: no bracket pair that could go is left. Pairs nested in each other
--| go in one run: the traversal drops the inner pair before it looks at
--| the outer.
def SourceFile.withoutSpareBrackets (file: SourceFile): SourceFile :=
  file.traverse dropPair (line => line.withoutSpareTypeBrackets)

-- P4: parameter groups that share a type are one group. It reads the
-- types P3 left bare: a bracketed type that holds a comment is not merged.

--| The name a type is written with, brackets aside.
def TypeExpr.baseName: TypeExpr → Text
  | TypeName name _ => name
  | TypeBracketed _ inner _ => inner.baseName

--| `first`'s names, then `second`'s.
def joinNames (first second: NonEmptyList Named): NonEmptyList Named :=
  { head = first.head, tail = first.tail ++ [second.head, ..second.tail] }

--| Whether `group`, written just before `next`, is merged into it: both
--| are typed, `group`'s `:` and its type, written as a bare name, hold no
--| comment, and `next`'s type is that name (in brackets or not).
def ParameterGroup.mergesInto (group next: ParameterGroup): Bool := match group, next with
  | Typed _ colon (TypeName name comments), Typed _ _ annotation =>
    colon.isNone && comments.isNone && annotation.baseName == name
  | _, _ => False

--| `group`'s names in front of `next`'s, with `next`'s `:` and type.
def ParameterGroup.mergedWith (group next: ParameterGroup): ParameterGroup := match group, next with
  | Typed names _ _, Typed more colon annotation => Typed (joinNames names more) colon annotation
  | _, _ => group

--| `group` placed before groups that are already merged: merged into the
--| first of them if it can be.
def mergeOnto (group: ParameterGroup) (rest: List ParameterGroup): List ParameterGroup := match rest with
  | [] => [group]
  | [next, ..others] => if group.mergesInto next then [group.mergedWith next, ..others] else [group, ..rest]

--| The groups folded once, right to left, so a run of groups with one type
--| is one group.
def mergeGroups: List ParameterGroup → List ParameterGroup
  | [] => []
  | [group, ..rest] => mergeOnto group (mergeGroups rest)

def Declaration.withMergedParameters: Declaration → Declaration
  | Function fnComments name nameComments takes open parameters trailingComma close equals body =>
    Function fnComments name nameComments takes open (mergeGroups parameters) trailingComma close equals body
  | other => other

--| P4's step: it touches no expression.
def keepExpr (position: Position) (expr: Expr): Expr := expr

--| P4: no two neighbouring parameter groups share a type that can be
--| merged.
def SourceFile.withMergedParameters (file: SourceFile): SourceFile :=
  file.traverse keepExpr (line => line.withMergedParameters)

--| The passes, in order.
def SourceFile.tidy (file: SourceFile): SourceFile :=
  file.withTakes.withoutTrailingCommas.withoutSpareBrackets.withMergedParameters
