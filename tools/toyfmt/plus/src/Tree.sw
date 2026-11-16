--| Sprig++'s syntax tree (docs/proposals/toy-plus-plus.md §1): Sprig's,
--| with the five additions. Stated here beside the toy's tree, which it
--| replaces at stage T2, so that `settle`, `meaning`, the passes and
--| their theorems can be checked for fit before anything is proved
--| (`../SKETCH-PLUS.md`).
--|
--| What differs from `Toy.Syntax`'s tree:
--|
--| - a comma holds no comments (rule N), so a list's items are
--|   expressions and a parameter has no `comma`;
--| - a list, a call's arguments and a function's parameters know whether
--|   a comma was written after the last (`trailingComma`);
--| - a function's parameters come in groups, typed or not, and it may
--|   have the word `takes` before them.

namespace Toy.Plus
import Toy.Syntax (Comment, Comments, Operator, Spaced)
import Std (Bool, List, NonEmptyList, Option, Text)

--| A parameter's type: a name, or a type in brackets.
type TypeExpr =
  | TypeName (name: Text) (comments: Comments)
  | TypeBracketed (open: Comments) (inner: TypeExpr) (close: Comments)

--| A parameter's name and its comments.
type Named = { name: Text, comments: Comments }

type ParameterGroup =
  | Untyped (parameter: Named)
  --| `w h: Int`: one or more names and the type they share.
  | Typed (names: NonEmptyList Named) (colon: Comments) (annotation: TypeExpr)

--| Each `Comments` field is the comments of one token of the construct,
--| named after it: `open` for `(` or `[`, `close` for `)` or `]`.
type Expr =
  | Var (name: Text) (comments: Comments)
  | NumberLiteral (digits: Text) (comments: Comments)
  --| With its quotes and escapes, as written.
  | StringLiteral (written: Text) (comments: Comments)
  | Bracketed (open: Comments) (inner: Expr) (close: Comments)
  | ListLiteral (open: Comments) (items: List Expr) (trailingComma: Bool) (close: Comments)
  | Call (callee: Expr) (open: Comments) (arguments: List Expr) (trailingComma: Bool) (close: Comments)
  | Field (target: Expr) (dot: Comments) (name: Text) (nameComments: Comments)
  | Negate (minus: Comments) (operand: Expr)
  --| Left-nested for a chain of one level: `a - b + c` is `(a - b) + c`.
  | Binary (operator: Operator) (sign: Comments) (left: Expr) (right: Expr)
  | If
      (ifComments: Comments)
      (condition: Expr)
      (thenComments: Comments)
      (whenTrue: Body)
      (elseComments: Comments)
      (whenFalse: Body)

type Statement =
  | Let (letComments: Comments) (name: Text) (nameComments: Comments) (equals: Comments) (body: Body)
  | Bare (value: Expr)
  | StatementNote (comment: Comment)

--| What follows `=`: one or more statements.
type Body = { statements: List (Spaced Statement) }

type Declaration =
  | Function
      (fnComments: Comments)
      (name: Text)
      (nameComments: Comments)
      --| The comments of `takes`, if it was written.
  (takes: Option Comments)
      (open: Comments)
      (parameters: List ParameterGroup)
      (trailingComma: Bool)
      (close: Comments)
      (equals: Comments)
      (body: Body)
  | Value (letComments: Comments) (name: Text) (nameComments: Comments) (equals: Comments) (body: Body)
  | DeclarationNote (comment: Comment)

type SourceFile = { declarations: List (Spaced Declaration) }
