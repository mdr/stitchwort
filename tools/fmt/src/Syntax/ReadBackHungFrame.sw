--| The frame (H3 of SW-4121's plan): the line rule's state after a spelt expression's leaves is the state its first
--| leaf entered, every bracket inside closed and no `->` left hanging.

namespace Syntax.ReadBackHungFrame
import Std (Bool, List, Nat, Option)
import Syntax (..)
import Fmt (..)
import Syntax.ReadBackProofs (..)
import Syntax.ReadBackLine (Spelt)
import Syntax.ReadBackHung (..)

--| The frame: the line rule's state after a spelt expression's leaves is the state its first leaf entered.
theorem speltHangs ∀ (expr: Expr) (first: Item) (more: List Item) (state next: HangState)
    (spelt: Spelt expr [first, ..more])
    (after: state.after (leavesOf [first, ..more]) = Some next):
    next = state.entered first.leaf :=
  ?
