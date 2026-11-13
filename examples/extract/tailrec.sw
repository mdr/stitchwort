-- `@[tailrec]` definitions are loops in the generated JavaScript, so a
-- million iterations run on Node's default stack. (The generator fails with
-- an internal error if it can't make a loop of a marked definition.)
--
-- run: sumTo 1000000
-- run: sumTo 10
-- run: evens 1000000
-- run: evens 10
-- run: countList [1, 2, 3] 0
import Std (List, Nat)

@[tailrec]
def sumOnto: Nat → Nat → Nat
  | 0, acc => acc
  | Succ n, acc => sumOnto n (acc + n)

export def sumTo (n: Nat): Nat := sumOnto n 0

-- A local accumulator, with the call under an `if`.
export def evens (n: Nat): Nat :=
  @[tailrec]
  def go: Nat → Nat → Nat
    | 0, acc => acc
    | Succ k, acc => if k % 2 == 0 then go k (acc + 1) else go k acc
  go n 0

@[tailrec]
export def countList (xs: List Nat) (n: Nat): Nat := match xs with
  | [] => n
  | [_, ..rest] => countList rest (n + 1)
