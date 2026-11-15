-- The catch-all arm after text literals: the cells the literals were split
-- into (`tail✝`, `code✝`, `valid✝`) serve only the split, so they aren't
-- listed while nothing refers to them. A spelled-out character whose code
-- isn't a scalar keeps its (false) hypothesis in view.
import Std (Char, Nat, Text)

def size: Text → Nat
  | "ab" => 1
  | "" => 0
  | _ => ?

def code (c: Char): Nat := match c with
  | MkChar 55296 _ => ?
  | _ => 0

-- A proof about a variable that stays shown is a fact the arm may need, so it
-- stays, with the variable it is about (`h✝: n✝ < k`).
type Below (k: Nat) = | MkBelow (n: Nat) (h: n < k)

def pick (k: Nat): Below k → Nat
  | MkBelow 0 _ => 0
  | _ => ?
