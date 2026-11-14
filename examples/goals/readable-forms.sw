-- Goals print what a definition unfolds to in the form it's written in
-- (SW-1000): membership as `x ∈ xs`, a `Float` comparison as `x < y`,
-- `Float`s in a list as literals, and a record given to a constructor in
-- brackets, so that it reads back.
import Std (List, Float, Int)

type Leaf = { value: Nat, depth: Nat }

-- `List.Mem y ys` computes to `List.Any (z => z = y) ys` on a `Cons`.
theorem memberOfTail ∀ (y: Nat) (ys: List Nat) (h: y ∈ [y, ..ys]): y ∈ ys := ?

-- The order keys `Float.less` compares are `x < y` again.
theorem keysLess ∀ (x y: Float) (h: x < y): x = x :=
  let keys: Int.less (Float.orderKey x) (Float.orderKey y) = True := h
  ?

-- A record given to a constructor is in brackets: `Cons { … } rest` would
-- name `Cons`'s fields.
theorem deeper ∀ (f: List Leaf → Nat) (leaf: Leaf) (rest: List Leaf):
    f [{ value = leaf.value, depth = leaf.depth + 1 }, ..rest] = f rest :=
  ?

-- After a `rewrite … at h`, only the new `h` is listed.
theorem rewritten ∀ (n: Nat) (h: n + 0 = 3): n = 3 := rewrite Std.Nat.addZero n at h in ?
