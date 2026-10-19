-- A local helper that calls itself in tail position becomes a loop in the
-- generated JS, like a top-level one (see loops.sw): the snapshot shows
-- `sumTo.go` as a `for (;;)` loop. The helper is lifted to a top-level
-- definition, with the captured variables as leading parameters.
--
-- run: sumTo 1000000
-- run: countIf 3 [1, 3, 5, 3, 3]
-- run: parity 1001

export def sumTo (n: Nat): Nat :=
  def go: Nat -> Nat -> Nat
    | Zero, acc => acc
    | Succ k, acc => go k (acc + Succ k)
  go n 0

-- Captures `target`, which the lifted helper takes as its first parameter.
export def countIf (target: Nat) (xs: List Nat): Nat :=
  def go (acc: Nat): List Nat -> Nat
    | Nil => acc
    | Cons x rest => go (if x == target then acc + 1 else acc) rest
  go 0 xs

-- A group. Mutual tail calls are not loops (as at top level), so the input is small.
export def parity (n: Nat): Bool :=
  def isEven: Nat -> Bool
    | Zero => True
    | Succ k => isOdd k
  def isOdd: Nat -> Bool
    | Zero => False
    | Succ k => isEven k
  isEven n
