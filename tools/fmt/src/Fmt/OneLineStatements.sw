--| `Decl.edgeQuiet1` (SW-4096; docs/reviews/SW-4096-one-line-elements.md), the test on the tree that
--| `edgeElements1` (proved in `Fmt.EdgeDeclProofs`, the hangs) takes: an `edgeQuiet1` slice 1 declaration meets
--| `DeclElements`. The top theorems take `declElements1` (`Fmt.ElementsProofs`), which asks no such test.
--|
--| `edgeQuiet1`: the only comments in the type and the value are at their edges. One may follow the last word that
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
def Word.edge1 (word: Word) (lead end: Bool): Bool :=
  (if lead then word.noted || !word.comments.blankBefore else !word.noted && !word.comments.blankBefore)
    && (end || !word.trails)

--| An expression quiet (`Expr.quiet1`) but at its edges: with `lead`, its first token may have own-line comments
--| above it; with `end`, its last token that is no closer may have a comment after it (an empty list's is its
--| opener). With neither it is `quiet1`; `lead` alone differs from `leadQuiet1` only in the blank line below the
--| comments. Every call has an argument, as in `quiet1`.
def Expr.edgeQuiet1 (expr: Expr) (lead end: Bool): Bool := match expr with
  | Atom _ word => word.edge1 lead end
  | Paren open inner close => open.edge1 lead False && inner.edgeQuiet1 False end && close.quiet1
  | Tuple open items _ close => open.edge1 lead False && lastEdgeQuiet1 end items && close.quiet1
  | ListOf open items _ close => open.edge1 lead (end && items.isEmpty) && lastEdgeQuiet1 end items && close.quiet1
  | App head arguments => !arguments.isEmpty && head.edgeQuiet1 lead False && lastEdgeQuiet1 end arguments
  | Infix _ left operator right => left.edgeQuiet1 lead False && operator.quiet1 && right.edgeQuiet1 False end
  | Prefix operator operand => operator.edge1 lead False && operand.edgeQuiet1 False end
  | _ => False

--| Items or arguments, quiet but the last, whose last token that is no closer may have a comment after it (`end`).
def lastEdgeQuiet1 (end: Bool) (items: List Expr): Bool := match items with
  | [] => True
  | [last] => last.edgeQuiet1 False end
  | [expr, ..rest] => expr.quiet1 && lastEdgeQuiet1 end rest

--| A declaration whose type and value, calmed, hold comments only at their edges: one after the type's last token
--| that is no closer, and in the value that and own-line comments above its first token. Comments above and after
--| the name, the `:` and the `:=` are not looked at.
def Decl.edgeQuiet1: Decl → Bool
  | Definition [] header (Assigned _ value) =>
    (header.result.calm False).edgeQuiet1 False True && (value.calm False).edgeQuiet1 True True
  | _ => False

-- `edgeElements1`, the hangs, is proved in `Fmt.EdgeDeclProofs`.

-- Sources the two statements apply to (D3684).
