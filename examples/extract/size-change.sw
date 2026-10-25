-- Recursion accepted by size-change termination (see accept/size-change.sw),
-- extracted to JavaScript. `interleave` and `gcdSteps` call themselves in
-- tail position with their arguments in a different order, which the
-- generated loop must keep apart. (Ackermann's function is left out: every
-- export is also run on random inputs, and it grows too fast for that.)
--
-- run: interleave [1, 3, 5] [2, 4]
-- run: interleave [] [7]
-- run: merge [1, 4, 6] [2, 3, 7]
-- run: merge [] []
-- run: gcdSteps 12 18 0
-- run: gcdSteps 0 5 0

import Std (Nat)

export def interleave: List Nat → List Nat → List Nat
  | Nil, ys => ys
  | Cons x xs, ys => Cons x (interleave ys xs)

export def merge: List Nat → List Nat → List Nat
  | Nil, ys => ys
  | Cons x xs, Nil => Cons x xs
  | Cons x xs, Cons y ys =>
    if Nat.leq x y then Cons x (merge xs (Cons y ys)) else Cons y (merge (Cons x xs) ys)

-- Each call takes one off the first argument and swaps the first two,
-- counting the calls: a tail call with its arguments in a different order.
export def gcdSteps: Nat → Nat → Nat → Nat
  | Zero, b, acc => acc
  | Succ a, b, acc => gcdSteps b a (Succ acc)
