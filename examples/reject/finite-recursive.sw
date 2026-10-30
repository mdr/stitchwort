-- expect-error: E-INSTANCE-NONE
-- `Finite` isn't derived for a recursive type (docs/proposals/decide.md
-- §6.2): a value can hold another, so there's no list of every one. The
-- error says why.
import Std (List)

type Tree =
  | Leaf
  | Node (left: Tree) (right: Tree)

def trees: List Tree := Finite.all
