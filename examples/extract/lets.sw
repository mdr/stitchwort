-- A pure `let` is computed once, with no effects machinery (no `Done`, no
-- `runPure`) around it: a `const` in a case tree's leaf, or a function
-- applied to the value inside an expression. A `let` holding a proof emits
-- nothing, like a proof argument (docs/proposals/let.md §6.1 rule 5).
--
-- run: twice 4
-- run: clamp 1
-- run: clamp 7
-- run: below 3 5
-- run: countUp 5 0
-- run: swapSum 3 4

import Std (Nat)

export def twice (n: Nat): Nat :=
  let m := n + 1
  m + m

export def clamp (n: Nat): Nat :=
  let m := n + 1
  if m < 3 then 0 else m

def lessOf (a b: Nat) (h: a ≤ b): Nat := b - a

export def below (a b: Nat): Nat :=
  let h := Nat.leAddRight a b
  lessOf a (a + b) h

-- A `let` in a loop: a `const` in each turn.
export def countUp: Nat → Nat → Nat
  | Zero, acc => acc
  | Succ k, acc =>
    let next := acc + 2
    let h: next = acc + 2 := rfl
    countUp k next

-- A tuple pattern: projections of the value, computed once.
export def swapSum (x y: Nat): Nat :=
  let (a, b) := (x, y + 1)
  b * 10 + a
