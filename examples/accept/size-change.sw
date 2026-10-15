-- Recursion where no one argument gets smaller in every call, but some
-- argument gets smaller however the calls are repeated (size-change
-- termination, docs/proposals/mutual-recursion.md §6). An argument passed on
-- unchanged, or rebuilt from its own pattern, is no smaller but no larger.
-- Pairs with soundness/alternating-growth.sw, soundness/constant-loop*.sw,
-- reject/swap-without-descent.sw, reject/rebuild-parameter.sw and
-- reject/partial-recursive-call.sw.

-- Ackermann's function: each call either makes the first argument smaller,
-- or keeps it (`Succ m` is the first argument, rebuilt) and makes the
-- second smaller.
ack : Nat -> Nat -> Nat
ack Zero     n        = Succ n
ack (Succ m) Zero     = ack m 1
ack (Succ m) (Succ n) = ack m (ack (Succ m) n)

-- The arguments swap places, so no one position gets smaller in every call,
-- but two calls in a row make both smaller.
interleave : List Nat -> List Nat -> List Nat
interleave Nil         ys = ys
interleave (Cons x xs) ys = Cons x (interleave ys xs)

-- Each call keeps one list (rebuilt from its pattern) and takes from the
-- other.
merge : List Nat -> List Nat -> List Nat
merge Nil         ys          = ys
merge (Cons x xs) Nil         = Cons x xs
merge (Cons x xs) (Cons y ys) =
  if leq x y then Cons x (merge xs (Cons y ys)) else Cons y (merge (Cons x xs) ys)

-- A recursive call passed to another function must be given all its
-- arguments: `\x -> sumWith n x`, not `sumWith n` (reject/partial-recursive-call.sw).
applyTo : (Nat -> Nat) -> Nat -> Nat
applyTo f x = f x

sumWith : Nat -> Nat -> Nat
sumWith Zero     acc = acc
sumWith (Succ n) acc = applyTo (\x -> sumWith n x) (acc + Succ n)

eqList : List Nat -> List Nat -> Bool
eqList Nil         Nil         = True
eqList (Cons x xs) (Cons y ys) = if x == y then eqList xs ys else False
eqList Nil         (Cons y ys) = False
eqList (Cons x xs) Nil         = False

test "ack 2 3" = ack 2 3 == 9
test "interleave" = eqList (interleave [1, 3, 5] [2, 4]) [1, 2, 3, 4, 5]
test "sumWith" = sumWith 4 0 == 10
test "merge" = eqList (merge [1, 4, 6] [2, 3, 7]) [1, 2, 3, 4, 6, 7]
