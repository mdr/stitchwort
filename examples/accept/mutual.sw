-- Declarations in any order, and definitions that call each other
-- (docs/proposals/mutual-recursion.md §6.8). Every top-level name is visible
-- throughout the module; definitions that refer to each other are checked
-- together, and their termination is decided for the group.

-- Written top-down: `main` uses what's defined below it.
main : Nat
main = total [[1, 2], [3]] + countdown 4

-- Each calls the other on a smaller number.
isEven : Nat -> Bool
isEven 0        = True
isEven (Succ n) = isOdd n

isOdd : Nat -> Bool
isOdd 0        = False
isOdd (Succ n) = isEven n

-- A wrapper that passes its argument on unchanged, to a helper that makes it
-- smaller: no single call decreases in both, but every way round does.
countdown : Nat -> Nat
countdown n = step n

step : Nat -> Nat
step 0        = 0
step (Succ n) = countdown n

-- The shape of `size`/`sizeForest` on a tree and a forest, on a list of
-- lists: `total` makes the outer list smaller, `inner` the inner one, and
-- `inner` passes the outer list on unchanged.
total : List (List Nat) -> Nat
total Nil           = 0
total (Cons xs xss) = inner xs xss

inner : List Nat -> List (List Nat) -> Nat
inner Nil         xss = total xss
inner (Cons x xs) xss = x + inner xs xss

-- Proofs by mutual induction, about `isEven` and `isOdd`, which are finished
-- before these are checked, so their types compute.
theorem evenNotOdd : (n : Nat) -> isEven n = not (isOdd n)
evenNotOdd 0        = rfl
evenNotOdd (Succ n) = oddNotEven n

theorem oddNotEven : (n : Nat) -> isOdd n = not (isEven n)
oddNotEven 0        = rfl
oddNotEven (Succ n) = evenNotOdd n

-- Effectful functions that call each other: after translation, each call is
-- inside a continuation.
ability Counter where
  bump : () -> {Counter} ()

ping : Nat -> {Counter} ()
ping 0        = ()
ping (Succ n) =
  bump ()
  pong n

pong : Nat -> {Counter} ()
pong 0        = ()
pong (Succ n) = ping n

countBumps : (() -> {Counter} ()) -> Nat
countBumps prog =
  let run : Nat -> Nat =
    handle prog () with
      | return x      -> \n -> n
      | bump u => k   -> \n -> k () (Succ n)
  run 0

-- A callback passed to a helper as a lambda that calls a member with all
-- its arguments: `\x -> stepBy k x` relates `k` to `walk`'s parameter.
walk : Nat -> Nat
walk 0        = 0
walk (Succ k) = applyTo (\x -> stepBy k x) 1

stepBy : Nat -> Nat -> Nat
stepBy k x = x + walk k

applyTo : (Nat -> Nat) -> Nat -> Nat
applyTo f x = f x

-- Names stay local: the pattern variable `step` and the lambda's `isOdd` are
-- not the definitions of those names, so they make no dependency on them.
shadows : Nat -> Nat
shadows step = applyTo (\isOdd -> isOdd + step) 1

test "main" = main == 6
test "isEven 10" = isEven 10
test "isOdd 7" = isOdd 7
test "total" = total [[1, 2], [], [3, 4]] == 10
test "ping 5 bumps 3 times" = countBumps (\u -> ping 5) == 3
test "pong 5 bumps 2 times" = countBumps (\u -> pong 5) == 2
test "walk" = walk 3 == 3
test "shadows" = shadows 2 == 3
