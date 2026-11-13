-- Goals name every variable apart (SW-1000): a binder doesn't capture a
-- variable of the same name, two variables that can't be referred to are
-- numbered, and an arm's variables are shown by the arm's own names.
import Std (Eq)

type Point = { x: Nat, y: Nat }

-- `Below x xs` unfolds to `∃ (x1: Nat) => x1 < x`, not `∃ (x: Nat) => x < x`.
def Below (y: Nat) (xs: List Nat): Prop := ∃ (x: Nat) => x < y

theorem below ∀ (x: Nat) (xs: List Nat): Below x xs := ?

-- Both points' fields are unnamed: `x✝¹` is `p`'s, `x✝` is `q`'s.
theorem samePoint ∀ (p: Point) (q: Point) (h: p.x = q.x): p = q := match p, q with
  | { x = _, y = _ }, { x = _, y = _ } => ?

type Tree =
  | Leaf (value: Nat)
  | Pair (left: Tree) (right: Tree)

-- The last arm's goal names `left1` and `right1`, not the second arm's
-- `left` and `right`.
theorem symmetric: ∀ (a b: Tree) => a = b → b = a
  | Leaf a, b, same => Eq.sym same
  | Pair left right, Leaf b, same => Eq.sym same
  | Pair left1 right1, Pair left2 right2, same => ?
