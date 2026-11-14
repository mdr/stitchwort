-- P7. 2021 day 18's `explode` in the shape it had before it was reshaped
-- around `explodeIn` (aoc/NOTES-2021.md, item 2): the general arm's
-- branch equations, as the generator would state and prove them.
import Std (Bool, Eq, List, Nat, Option, Void)

type Number = | Regular (value: Nat) | Pair (left: Number) (right: Number)

type Explosion = { toLeft: Nat, number: Number, toRight: Nat }

def addLeftmost (amount: Nat): Number → Number
  | Regular value => Regular (value + amount)
  | Pair left right => Pair (addLeftmost amount left) right

def addRightmost (amount: Nat): Number → Number
  | Regular value => Regular (value + amount)
  | Pair left right => Pair left (addRightmost amount right)

def explode (depth: Nat): Number → Option Explosion
  | Regular _ => None
  | Pair (Regular a) (Regular b) => if 4 ≤ depth then Some ({ toLeft = a, number = Regular 0, toRight = b }) else None
  | Pair left right =>
    match explode (depth + 1) left with
      | Some inLeft =>
        Some ({ toLeft = inLeft.toLeft, number = Pair inLeft.number (addLeftmost inLeft.toRight right), toRight = 0 })
      | None =>
        match explode (depth + 1) right with
          | Some inRight =>
            Some
              ({
                toLeft = 0,
                number = Pair (addRightmost inRight.toLeft left) inRight.number,
                toRight = inRight.toRight
              })
          | None => None

-- `explode.eq3`: the arm as written, its overlap with arm 2 as a hypothesis.
-- (Its right side has the lifted `match`, so only a proof can show it; the
-- generator states it with `explode.%match1`.)

-- `explode.eq3.some`
theorem explodeEq3Some ∀ (depth: Nat) (left right: Number)
    (inLeft: Explosion) (notArm2: (a: Nat) → (b: Nat) → left = Regular a → right = Regular b → Void)
    (found: explode (depth + 1) left = Some inLeft):
    explode depth (Pair left right)
      = Some
        ({ toLeft = inLeft.toLeft, number = Pair inLeft.number (addLeftmost inLeft.toRight right), toRight = 0 }) :=
  match left, right with
    | Regular a, Regular b => Void.exfalso (notArm2 a b rfl rfl)
    | Regular a, Pair x y => cases
    | Pair x y, r => rewrite found in rfl

-- `explode.eq3.none.some`
theorem explodeEq3NoneSome ∀ (depth: Nat) (left right: Number)
    (inRight: Explosion) (notArm2: (a: Nat) → (b: Nat) → left = Regular a → right = Regular b → Void)
    (none: explode (depth + 1) left = None)
    (found: explode (depth + 1) right = Some inRight):
    explode depth (Pair left right)
      = Some
        ({ toLeft = 0, number = Pair (addRightmost inRight.toLeft left) inRight.number, toRight = inRight.toRight }) :=
  match left, right with
    | Regular a, Regular b => Void.exfalso (notArm2 a b rfl rfl)
    | Regular a, Pair x y => rewrite found in rfl
    | Pair x y, r => rewrite none, found in rfl

-- `explode.eq3.none.none`
theorem explodeEq3NoneNone ∀ (depth: Nat)
    (left right: Number) (notArm2: (a: Nat) → (b: Nat) → left = Regular a → right = Regular b → Void)
    (none: explode (depth + 1) left = None)
    (noneRight: explode (depth + 1) right = None):
    explode depth (Pair left right) = None :=
  match left, right with
    | Regular a, Regular b => Void.exfalso (notArm2 a b rfl rfl)
    | Regular a, Pair x y => rewrite none, noneRight in rfl
    | Pair x y, r => rewrite none, noneRight in rfl

-- A use: the left part a pair, so `cases` gives the overlap hypothesis.
theorem leftFound ∀ (depth: Nat) (x y right: Number) (inLeft: Explosion)
    (found: explode (depth + 1) (Pair x y) = Some inLeft):
    explode depth (Pair (Pair x y) right)
      = Some
        ({ toLeft = inLeft.toLeft, number = Pair inLeft.number (addLeftmost inLeft.toRight right), toRight = 0 }) :=
  explodeEq3Some depth (Pair x y) right inLeft cases found
