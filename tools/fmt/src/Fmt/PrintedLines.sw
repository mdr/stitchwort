--| Lemmas for `printedLines1` (SW-4086): a printed one-line declaration's items are of the kinds read-back reads on a
--| line, and start lines only where `oneLine1` lets them. The kinds come from `speltExpr` (an expression's items hold
--| no `:=` and no `def` or `:`); the line starts from `onLine1`, read over the items' tokens.

namespace Fmt.PrintedLines
import Std (Bool, Eq, List)
import Syntax (..)
import Fmt.Driver1 (..)
import Syntax.SettleProofs (tokens)
import Syntax.ParseCarriesFile (itemsLeaves)
import Syntax.ReadBackLine (exprAll, exprKind, exprNotColonEq, inLineAll, laterInLine, lineAll, lineKind)

--| The tokens of the items' leaves.
def leafTokens (items: List Item): List Token := items.map (item => item.leaf.token)

--| `tokens` of a leaf list is `leafTokens` of the items made of them.
theorem tokensOfItems ∀ (items: List Item): tokens (items.map Item.leaf) = leafTokens items := match items with
  | [] => byComputing
  | [item, ..more] => rewrite tokensOfItems more

theorem leafTokensAppend ∀ (first rest: List Item): leafTokens (first ++ rest) = leafTokens first ++ leafTokens rest :=
  match first with
    | [] => byComputing
    | [item, ..more] => rewrite leafTokensAppend more rest

theorem exprLineKind ∀ (kind: Tok) (expr: exprKind kind = True): lineKind kind = True := cases

--| An expression's items are of the kinds read on a line.
theorem exprLine ∀ (items: List Item) (expr: exprAll items = True): lineAll items = True := match items with
  | [] => byComputing
  | [item, ..more] => rewrite exprLineKind item.kind (Bool.andLeft expr), exprLine more (Bool.andRight expr)

--| No item starts a line exactly when no token of `leafTokens` does.
theorem inLineOfTokens ∀ (items: List Item)
    (none: (leafTokens items).all (token => !token.lineStart) = True):
    inLineAll items = True :=
  match items with
    | [] => byComputing
    | [item, ..more] => rewrite Bool.andLeft none, inLineOfTokens more (Bool.andRight none)

--| The type's items start no line and the value's, after the first, none: `typeOnLine1` over the type's tokens, the
--| `:=` and the value's.
theorem typeLines ∀ (typeRead valueRead: List Item) (colonEq: Item)
    (expr: exprAll typeRead = True)
    (isColonEq: colonEq.kind = ColonEq)
    (lines: typeOnLine1 (leafTokens typeRead ++ [colonEq.leaf.token, ..leafTokens valueRead]) = True):
    inLineAll typeRead = True ∧ valueOnLine1 (leafTokens valueRead) = True :=
  match typeRead with
    | [] => (byComputing, rewrite isColonEq at lines then lines)
    | [item, ..more] =>
      let notEq := exprNotColonEq item.kind (Bool.andLeft expr)
      let step: (!item.leaf.token.lineStart
        && typeOnLine1 (leafTokens more ++ [colonEq.leaf.token, ..leafTokens valueRead]))
        = True :=
        rewrite notEq at lines then lines
      let (inMore, valueLines) := typeLines more valueRead colonEq (Bool.andRight expr) isColonEq (Bool.andRight step)
      (rewrite Bool.andLeft step, inMore then byComputing, valueLines)

theorem laterOfValue ∀ (valueRead: List Item)
    (lines: valueOnLine1 (leafTokens valueRead) = True):
    laterInLine valueRead = True :=
  match valueRead with
    | [] => byComputing
    | [item, ..more] => inLineOfTokens more lines

--| A group's items' tokens are its leaves'.
theorem groupLeafTokens ∀ (group: List Leaf): leafTokens (items group) = tokens group :=
  Eq.trans (tokensOfItems (items group)).flipped (Eq.cong tokens (itemsLeaves group))
