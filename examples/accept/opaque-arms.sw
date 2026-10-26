-- Opaque definitions by arms (a case tree), recursive ones, and ones that
-- call each other. Each without an `unfolding` clause gets `f.unfold`, whose
-- proof follows the case tree. Unfolding one opaque member of a group that
-- calls itself unfolds its other opaque members too (D1267).
-- (docs/proposals/opaque-definitions.md §6.3, §6.11.)
import Std (List, Nat)

opaque def small: Nat -> Nat
  | 0 => 10
  | 2 => 12
  | n => n

theorem smallTwo: small 2 = 12 := rewrite small.unfold in rfl

theorem smallFive: small 5 = 5 := rewrite small.unfold in rfl

opaque def size: List Nat -> Nat
  | [] => 0
  | Cons _ rest => 1 + size rest

theorem sizeNil: size [] = 0 := rewrite size.unfold in rfl

-- Without `unfolding`, `size rest` is stuck: what's known is its type.
theorem sizeCons (x: Nat) (rest: List Nat): size (Cons x rest) = 1 + size rest :=
  rewrite size.unfold in rfl

theorem sizeTwo (x: Nat) (y: Nat): size [x, y] = 2 unfolding size := rfl

opaque def isEven: Nat -> Bool
  | Zero => True
  | Succ n => isOdd n

opaque def isOdd: Nat -> Bool
  | Zero => False
  | Succ n => isEven n

-- `unfolding isEven` brings `isOdd`, checked in the same group.
theorem evenFour: isEven 4 = True unfolding isEven := rfl

test "small runs" := small 0 == 10 && small 2 == 12 && small 7 == 7
test "size runs" := size [1, 2, 3] == 3
test "isEven runs" := isEven 10 && isOdd 7
