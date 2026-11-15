--| Sprig's syntax tree, as the printing rules read it (toy-formatter.md §1).
--|
--| It keeps what formatting must not change: every construct, the texts of
--| names, numbers and strings as written, brackets as written, comments and
--| kept blank lines. It keeps nothing of the author's layout: no positions,
--| no spacing, no line breaks beyond the kept blank lines. So it is the
--| erased tree of the plan's proofs, and two sources with the same tree
--| print the same.
--|
--| What the parser (stage A) must make of the source:
--|
--| - A body that is one expression with no comment above it, on the `=`
--|   line or below it, is a `Body` of one `Bare` statement; a block is a
--|   `Body` of its statements in order. Its first statement has no blank
--|   line before it, and its last isn't a comment.
--| - A trailing comment (after code on its line) belongs to the `Bare`
--|   statement it ends, or to the list item or argument whose line it ends
--|   (after its comma, if it has one). An own-line comment belongs to the
--|   item below it: a declaration or statement (as its own `Note` line in
--|   the list) or a list item or argument (in its `comments`).
--| - A comment anywhere else makes the whole declaration `AsWritten`, its
--|   text cut from the source from its first character to the end of its
--|   last line, without the line break.
--| - A blank line is kept (`blankBefore`) between declarations and between
--|   statements, however many there were; anywhere else it is dropped.
--| - Line starts inside brackets don't matter to layout.

namespace Toy.Syntax
import Std (List, Option, Text)

--| A `--` comment as written, `--` included.
type Comment = { text: Text }

--| Binary operators, by precedence level, loosest first.
type Operator =
  | Or
  | And
  | Equal
  | NotEqual
  | Less
  | LessEqual
  | Append
  | Plus
  | Minus
  | Times
  | Divide
  | Remainder

def Operator.spelling: Operator → Text
  | Or => "||"
  | And => "&&"
  | Equal => "=="
  | NotEqual => "!="
  | Less => "<"
  | LessEqual => "<="
  | Append => "++"
  | Plus => "+"
  | Minus => "-"
  | Times => "*"
  | Divide => "/"
  | Remainder => "%"

--| 1 for `||` up to 6 for `* / %`: operators of one level chain together.
def Operator.level: Operator → Nat
  | Or => 1
  | And => 2
  | Equal | NotEqual | Less | LessEqual => 3
  | Append => 4
  | Plus | Minus => 5
  | Times | Divide | Remainder => 6

type Expr =
  | Var (name: Text)
  | NumberLiteral (digits: Text)
  --| With its quotes and escapes, as written.
  | StringLiteral (written: Text)
  --| `( … )`: brackets are kept as written.
  | Bracketed (inner: Expr)
  | ListLiteral (items: List Item)
  | Call (callee: Expr) (arguments: List Item)
  | Field (target: Expr) (name: Text)
  | Negate (operand: Expr)
  --| Left-nested for a chain of one level: `a - b + c` is `(a - b) + c`.
  | Binary (operator: Operator) (left: Expr) (right: Expr)
  | If (condition: Expr) (whenTrue: Body) (whenFalse: Body)

--| A list item or a call's argument, with the own-line comments above it and
--| the trailing comment that ends its line.
type Item = { comments: List Comment, value: Expr, trailing: Option Comment }

--| A line of a vertical list (a file's declarations, a block's statements),
--| and whether the author left a blank line above it.
type Spaced (a: Type) = { blankBefore: Bool, line: a }

type Statement =
  | Let (name: Text) (body: Body)
  | Bare (value: Expr) (trailing: Option Comment)
  | StatementNote (comment: Comment)

--| What follows `=`: one or more statements.
type Body = { statements: List (Spaced Statement) }

type Declaration =
  | Function (name: Text) (parameters: List Text) (body: Body)
  | Value (name: Text) (body: Body)
  | DeclarationNote (comment: Comment)
  --| A declaration with a comment where no rule places one, printed as
  --| written.
  | AsWritten (text: Text)

type SourceFile = { declarations: List (Spaced Declaration) }

--| The expression and trailing comment of a body that is one plain
--| expression; `None` for a block.
def Body.single (body: Body): Option (Expr, Option Comment) := match body.statements with
  | [{ line = Bare value trailing, .. }] => Some (value, trailing)
  | _ => None
