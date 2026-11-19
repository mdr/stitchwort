-- `match induct` alternatives that share a proof are one arm with several
-- cases, as an or-pattern is (D3694): the body is checked once for each case,
-- with that case's own binders and hypotheses, and every case binds the same
-- names. `xs.f a` reads as `f xs a`, as an ordinary call does.
import Std (Bool, Eq, List, Nat)

def countAbove (k: Nat): List Nat → Nat
  | [] => 0
  | [x, ..xs] => if Nat.leq k x then Succ (countAbove k xs) else countAbove k xs

-- The two branches of the `if` share a proof, and `h` has a different type in
-- each.
theorem countAboveLe ∀ (k: Nat) (xs: List Nat): countAbove k xs ≤ List.length xs := match induct (countAbove k xs) with
  | eq1 => arithmetic
  | eq2IfTrue x xs h ih | eq2IfFalse x xs h ih => arithmetic

-- `_` for names the proof doesn't use.
theorem countAboveLe2 ∀ (k: Nat) (xs: List Nat): countAbove k xs ≤ List.length xs := match induct (countAbove k xs) with
  | eq1 | eq2IfTrue _ _ _ _ | eq2IfFalse _ _ _ _ => arithmetic

type Pile = | Empty | More (weight: Nat) (rest: Pile)

def Pile.total: Pile → Nat
  | Empty => 0
  | More weight rest => weight + Pile.total rest

-- The call by dot: `pile.total` is `Pile.total pile`.
theorem totalGe ∀ (pile: Pile): pile.total ≥ 0 := match induct pile.total with
  | eq1 => arithmetic
  | eq2 weight rest ih => arithmetic
