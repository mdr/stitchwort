--| Sprig's syntax tree, as the printing rules read it (toy-formatter.md §1).
--|
--| It keeps what formatting must not change: every construct, the texts of
--| names, numbers and strings as written, brackets as written, comments and
--| kept blank lines. It keeps nothing of the author's layout: no positions,
--| no spacing, no line breaks beyond the kept blank lines. So it is the
--| erased tree of the plan's proofs, and two sources with the same tree
--| print the same.
--|
--| What the parser (`Parser.sw`) makes of the source:
--|
--| - A body that is one expression with no comment above it, on the `=`
--|   line or below it, is a `Body` of one `Bare` statement; a block is a
--|   `Body` of its statements in order. Its first statement has no blank
--|   line before it, and its last isn't a comment.
--| - Every comment is held by the token the lexer gave it to, in that
--|   token's `Comments` in the tree: an own-line comment by the token below
--|   it, a trailing comment by the token before it on its line. The parser
--|   copies them there as it reads each token and decides nothing from
--|   them, so every source that parses has a tree, and the tree holds every
--|   comment once.
--| - A comma holds no comments and isn't in the tree: rule N
--|   (`Settle.sw`) gives what was written beside one to the tokens around
--|   it before the parser reads them.
--| - The own-line comments above a declaration's or statement's first
--|   token are the exception: they are lines of the vertical list
--|   (`DeclarationNote`, `StatementNote`), each with its kept blank line,
--|   and that token's own `above` is empty.
--| - A blank line is kept (`blankBefore`) between declarations and between
--|   statements, however many there were; anywhere else it is dropped.
--| - Line starts inside brackets don't matter to layout.

namespace Toy.Syntax
import Std (List, NonEmptyList, Option, Text)

--| A `--` comment as written, `--` included.
type Comment = { text: Text }

--| The comments a token holds: the own-line comments above it, in order,
--| and the trailing comment after it on its line.
type Comments = { above: List Comment, after: Option Comment }

def Comments.none: Comments := { above = [], after = None }

--| Binary operators, by precedence level, loosest first.
type Operator =
  | Or
  | And
  | EqualTo
  | NotEqual
  | LessThan
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
  | EqualTo => "=="
  | NotEqual => "!="
  | LessThan => "<"
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
  | EqualTo | NotEqual | LessThan | LessEqual => 3
  | Append => 4
  | Plus | Minus => 5
  | Times | Divide | Remainder => 6

--| Each `Comments` field is the comments of one token of the construct,
--| named after it: `open` for `(` or `[`, `close` for `)` or `]`.
type Expr =
  | Var (name: Text) (comments: Comments)
  | NumberLiteral (digits: Text) (comments: Comments)
  --| With its quotes and escapes, as written.
  | StringLiteral (written: Text) (comments: Comments)
  --| `( … )`: brackets are kept as written.
  | Bracketed (open: Comments) (inner: Expr) (close: Comments)
  | ListLiteral (open: Comments) (items: List Expr) (close: Comments)
  | Call (callee: Expr) (open: Comments) (arguments: List Expr) (close: Comments)
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


--| A line of a vertical list (a file's declarations, a block's statements),
--| and whether the author left a blank line above it.
type Spaced (a: Type) = { blankBefore: Bool, line: a }

--| `Let`'s comments are its tokens': `let`, the name and `=`.
type Statement =
  | Let (letComments: Comments) (name: Text) (nameComments: Comments) (equals: Comments) (body: Body)
  | Bare (value: Expr)
  | StatementNote (comment: Comment)

--| What follows `=`: one or more statements.
type Body = { statements: List (Spaced Statement) }

--| The comments are the tokens': `fn` or `let`, the name, `takes` if it
--| was written, the brackets around the parameters and `=`.
type Declaration =
  | Function
      (fnComments: Comments)
      (name: Text)
      (nameComments: Comments)
      (takes: Option Comments)
      (open: Comments)
      (parameters: List ParameterGroup)
      (close: Comments)
      (equals: Comments)
      (body: Body)
  | Value (letComments: Comments) (name: Text) (nameComments: Comments) (equals: Comments) (body: Body)
  | DeclarationNote (comment: Comment)

type SourceFile = { declarations: List (Spaced Declaration) }
