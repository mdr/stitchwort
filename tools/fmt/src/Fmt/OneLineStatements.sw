--| `Decl.edgeQuiet` (SW-4096; docs/reviews/SW-4096-one-line-elements.md), the test on the tree that
--| once took: an `edgeQuiet` slice 1 declaration meets
--| `DeclElements`. The top theorems take `declElements1` (`Fmt.ElementsProofs`), which asks no such test.
--|
--| `edgeQuiet`: the only comments in the type and the value are at their edges. One may follow the last word that
--| is no closer (the printer writes it after the closers that follow, so it ends the line), and the value's first
--| word may have comments above it. The test is made of the calmed type and value (`Expr.calm`): a blank line the
--| rules never read is no part of it, and the driver's tree is not calmed.

namespace Fmt.OneLineStatements
import Std (Bool, List, Option, Text)
import Syntax (Decl, DefBody, Expr, SourceFile, Word)
import Fmt (..)
import Fmt.Driver1 (..)
import Fmt.OutputStatements (tidiedOf)
import Fmt.ExprHangProofs (..)
import Fmt.DeclFactsProofs (DeclElements)
import Fmt.TreeJoinProofs (lexKind)

-- The class.

--| A token of an edge-quiet expression. Its first token (`lead`) may have own-line comments above it, and a blank
--| line kept below them; any other has neither. The last token that is no closer (`end`) may have a comment after it;
--| any other has none.
def Word.edge (word: Word) (lead end: Bool): Bool :=
  (if lead then word.noted || !word.comments.blankBefore else !word.noted && !word.comments.blankBefore)
    && (end || !word.trails)

--| An expression quiet (`Expr.quiet`) but at its edges: with `lead`, its first token may have own-line comments
--| above it; with `end`, its last token that is no closer may have a comment after it (an empty list's is its
--| opener). With neither it is `quiet`; `lead` alone differs from `leadQuiet` only in the blank line below the
--| comments. Every call has an argument, as in `quiet`.
def Expr.edgeQuiet (expr: Expr) (lead end: Bool): Bool := match expr with
  | Atom _ word => word.edge lead end
  | Paren open inner close => open.edge lead False && inner.edgeQuiet False end && close.quiet
  | Tuple open items _ close => open.edge lead False && lastEdgeQuiet end items && close.quiet
  | ListOf open items _ close => open.edge lead (end && items.isEmpty) && lastEdgeQuiet end items && close.quiet
  | App head arguments => !arguments.isEmpty && head.edgeQuiet lead False && lastEdgeQuiet end arguments
  | Infix _ left operator right => left.edgeQuiet lead False && operator.quiet && right.edgeQuiet False end
  | Prefix operator operand => operator.edge lead False && operand.edgeQuiet False end
  | _ => False

--| Items or arguments, quiet but the last, whose last token that is no closer may have a comment after it (`end`).
def lastEdgeQuiet (end: Bool) (items: List Expr): Bool := match items with
  | [] => True
  | [last] => last.edgeQuiet False end
  | [expr, ..rest] => expr.quiet && lastEdgeQuiet end rest

--| A declaration whose type and value, calmed, hold comments only at their edges: one after the type's last token
--| that is no closer, and in the value that and own-line comments above its first token. Comments above and after
--| the name, the `:` and the `:=` are not looked at.
def Decl.edgeQuiet: Decl → Bool
  | Definition [] header (Assigned _ value) =>
    (header.result.calm False).edgeQuiet False True && (value.calm False).edgeQuiet True True
  | _ => False

-- Sources the two statements apply to (D3684).
