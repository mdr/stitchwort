--| The tree the sketch's statements are about: a stand-in for stage 2's
--| typed tree, drawn from the Rust tree's 98 node kinds
--| (`crates/syntax/src/tree.rs`, `NodeKind`).
--|
--| Only the constructs where the formatter has a freedom are typed
--| exactly: a bracket pair, a comma bracket, a type after a row, a
--| parameter group, a binder list, a header. Every other construct is a
--| `Form`: its kind and its parts in the order written. `meaning` and the
--| passes treat a `Form` the same way whatever its kind (they go into its
--| parts), so stage 2's constructor per construct can replace `Form`
--| without changing a statement here; only `traverse` grows.
--|
--| What the tree holds of a token: its text where the text varies, and
--| its comments. Nothing of the author's layout: no column, no "starts
--| its line", no count of blank lines, no comma.

namespace Fmt.Sketch
import Std (Bool, List, Option, Text)

--| An own-line comment, `--` included, and whether a blank line was above
--| it.
type Note = { text: Text, blankBefore: Bool }

--| The comments a token holds once rule N has run: the own-line comments
--| above it, in order, and the trailing comment after it on its line.
type Comments = { above: List Note, after: Option Text }

def Comments.none: Comments := { above = [], after = None }

def Comments.isNone (comments: Comments): Bool := comments.above.isEmpty && comments.after.isNone

--| A token whose text the tree must keep: a name, a numeral, a piece of
--| text, an operator, and in a `Form` every token. A `"""` text's piece
--| holds its lines by value, without the indentation the printer
--| chooses.
type Word = { text: Text, comments: Comments }

--| The Rust tree's node kinds, by their Rust names. `Error` is here for
--| the count only: the formatter's parser is strict, so no tree holds
--| one.
type Kind =
  | Error
  | Namespace
  | Import
  | Def
  | Theorem
  | Instance
  | DataType
  | RecordType
  | TypeSynonym
  | Interface
  | Ability
  | Test
  | Rules
  | Expression
  | Attributes
  | Attribute
  | AttributeName
  | ImportItem
  | Param
  | Default
  | ResultType
  | Decreasing
  | Unfolding
  | Body
  | Arms
  | Arm
  | Guard
  | Binder
  | Constructor
  | Fields
  | Field
  | AbilityOp
  | Block
  | Let
  | Paren
  | Unit
  | Universe
  | Include
  | Tuple
  | ListOf
  | Spread
  | Record
  | RecordField
  | CtorFields
  | App
  | NamedArg
  | FieldAccess
  | Section
  | OperatorSection
  | Binary
  | Chain
  | Membership
  | Range
  | Prefix
  | Pipe
  | Arrow
  | FunctionType
  | Forall
  | Exists
  | Iff
  | Lambda
  | LambdaParam
  | If
  | Annotation
  | Effect
  | Row
  | Seq
  | LetExpr
  | Interpolated
  | Interpolation
  | Handle
  | HandlerClause
  | Match
  | Scrutinee
  | ClauseLambda
  | Induct
  | InductArm
  | Reify
  | Calc
  | CalcStep
  | Rewrite
  | RewriteRule
  | RewriteRules
  | Omega
  | Ring
  | Cases
  | PatternCtor
  | PatternTuple
  | PatternList
  | PatternNamed
  | PatternRecord
  | PatternCtorFields
  | PatternOr
  | PatternParen
  | PatternTyped
  | PatternNegative
  | PatternAbsurd
  | PatternAppend

--| Expressions, types and patterns: one family here. Stage 2 may give
--| patterns their own type; no statement depends on it.
type Expr =
  --| A token that is an expression by itself: a name, a literal, `_`.
  | Token (word: Word)
  --| `( … )` around one expression or type (`Paren`).
  | Pair (open: Comments) (inner: Expr) (close: Comments)
  --| A bracket whose items commas separate: `Unit`, `Tuple`, `ListOf`,
  --| `Record`, `Fields`, `Row`, `Attributes`, `RewriteRules`, an import's
  --| names, and the pattern forms. `lead` is a record update's `r |`. The
  --| commas are not in the tree: rule N leaves them no comment, so the
  --| flag is all there is to know.
  | Commas (kind: Kind) (open: Comments) (lead: Option Lead) (items: List Expr) (trailingComma: Bool) (close: Comments)
  --| `{IO} T` (`Effect`): the row and the type after it.
  | WithRow (row: Expr) (result: Expr)
  --| `x y => e`, `∀ … => P`, `∃ … => P`, `(x: A) -> B`: binders, an arrow
  --| and a body (`Lambda`, `Forall`, `Exists`, `FunctionType`).
  | Binding (kind: Kind) (keyword: Option Comments) (parameters: List Parameter) (arrow: Comments) (body: Expr)
  --| Every other construct: its kind and its parts in the order written.
  | Form (kind: Kind) (parts: List Part)
  --| A definition inside a block.
  | Local (declaration: Declaration)

--| A record update's base and its `|`.
type Lead = { base: Expr, bar: Comments }

type Part =
  | Piece (word: Word)
  | Sub (expr: Expr)
  --| A parameter where no pass merges: a type's, a constructor's field.
  | Bound (parameter: Parameter)
  --| A line of a block, and whether a blank line was kept above it.
  | Line (blankBefore: Bool) (line: Expr)

--| A parameter (`Param`, `Binder`, `LambdaParam`).
type Parameter =
  --| `(a b: T)`, `[a: T]`, `[auto h: P]`, `(x: A := v)`.
  | Group
      (kind: Kind)
      (square: Bool)
      (open: Comments)
      (auto: Option Comments)
      (names: List Word)
      (colon: Comments)
      (annotation: Expr)
      (default: Option Assigned)
      (close: Comments)
  --| `()`
  | NoParameter (open: Comments) (close: Comments)
  --| A lambda's bare name.
  | Bare (name: Word)
  --| A lambda's pattern.
  | Matched (pattern: Expr)

--| `:= v` after a parameter's type.
type Assigned = { assign: Comments, value: Expr }

type Declaration =
  --| `def`, `theorem`, `instance`: attributes, the keywords (`export`,
  --| `opaque`, the keyword itself), the name, `∀` if written, the
  --| parameters, and the rest (result type, `decreasing`, `unfolding`,
  --| body or arms) as parts.
  | Headed
      (kind: Kind)
      (attributes: List Expr)
      (keywords: List Word)
      (name: Word)
      (quantifier: Option Comments)
      (parameters: List Parameter)
      (rest: List Part)
  --| Every other declaration.
  | Plain (kind: Kind) (parts: List Part)

--| A declaration and whether a blank line was kept above it.
type Spaced = { blankBefore: Bool, declaration: Declaration }

--| `end`: the comments after the last token.
type SourceFile = { declarations: List Spaced, end: List Note }
