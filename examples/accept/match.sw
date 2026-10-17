-- `match` expressions (docs/proposals/syntax-conveniences.md section 4).
-- A `match` that is the whole right-hand side of an equation on unnamed
-- variables becomes part of the equation's case tree. Any other `match` is
-- lifted into a generated definition named after its owner.

import List (length)

-- In the tree: the whole right-hand side.
describe : List Nat -> Text
describe xs =
  match xs with
    | Nil        -> "empty"
    | Cons x Nil -> "one"
    | _          -> "many"

-- Lifted: the `match` is an argument of `+`. Not a tail call.
count : Nat -> Nat
count n = 1 + match n with
                | Zero   -> 0
                | Succ k -> count k

-- In the tree, with a recursive call in tail position.
countTail : Nat -> Nat
countTail n = match n with | Zero -> 0 | Succ k -> countTail k

-- Lifted, with a variable of the equation used in a branch.
f : Nat -> List Nat -> Nat
f n xs = 1 + match xs with
               | Nil      -> n
               | Cons x _ -> x + n

-- A proof by `match`, in the tree.
theorem appendNil : (xs : List a) -> List.append xs Nil = xs
appendNil xs =
  match xs with
    | Nil       -> rfl
    | Cons y ys -> Eq.cong (Cons y) (appendNil ys)

-- A `match` in a test.
test "describe" = describe [1, 2] == "many"
test "count" = count 3 == 4
test "countTail" = countTail 5 == 0
test "f" = f 2 [5] == 8
test "f nil" = f 2 Nil == 3
test "lifted in test" = (match 3 with | Zero -> False | Succ _ -> True)

-- Expression scrutinee, named: `h` is an equation about the expression.
isEmpty : (xs : List Nat) -> Bool
isEmpty xs = match h : length xs with
  | Zero -> True
  | Succ _ -> False

-- The equation used in a branch.
lenZero : (xs : List Nat) -> Decidable (length xs = 0)
lenZero xs = match h : length xs with
  | Zero -> Yes rfl
  | Succ k -> No (\e -> Nat.equalFalse (Succ k) 0 rfl e)

keep : (p : Prop) -> p -> Bool
keep p _ = True

usesH : (xs : List Nat) -> Bool
usesH xs = match h : length xs with
  | Zero -> keep (List.length xs = 0) h
  | Succ k -> keep (List.length xs = Succ k) h

-- Expression scrutinee generalised in the goal.
theorem same : (n : Nat) -> (n + 0) = (n + 0)
same n = match n + 0 with
  | Zero -> rfl
  | Succ m -> rfl

-- Variable scrutinee with a dependent hypothesis, lifted.
pred : (n : Nat) -> (q : Not (n = 0)) -> Nat
pred n q = 0 + match n with
  | Zero -> Void.absurd (q rfl)
  | Succ m -> m

-- Nested matches.
both : List Nat -> List Nat -> Nat
both xs ys = 1 + match xs with
  | Nil -> 0
  | Cons x _ -> x + match ys with
    | Nil -> 0
    | Cons y _ -> y

-- A `match` in a signature.
Pick : Bool -> Type
Pick b = match b with | True -> Nat | False -> Text

pickType : (b : Bool) -> (match b with | True -> Nat | False -> Text)
pickType b = match b with
  | True -> 1
  | False -> "one"

-- Two scrutinees.
zipLen : List Nat -> List Nat -> Nat
zipLen xs ys = 1 + match xs, ys with
  | Cons _ a, Cons _ b -> zipLen a b
  | _, _ -> 0

-- A user function named `match1` next to a match: no clash with the
-- generated names.
match1 : Nat -> Nat
match1 n = n + match n with | Zero -> 1 | Succ _ -> 2

-- Number patterns in a match.
size : Nat -> Text
size n = match n with
  | 0 -> "none"
  | 1 -> "one"
  | _ -> "many"

-- A record pattern in a match.
type Person = { name : Text, age : Nat }

greeting : Person -> Text
greeting p = "hi " ++ match p with
  | { name, age = 0 } -> name ++ " (newborn)"
  | { name, .. } -> name

-- A tuple pattern in a match.
swapIfZero : (Nat, Nat) -> (Nat, Nat)
swapIfZero p = match p with
  | (0, y) -> (y, 0)
  | (x, y) -> (x, y)

test "isEmpty" = isEmpty Nil
test "both" = both [1] [2] == 4
test "pickType" = pickType True == 1
test "zipLen" = zipLen [1, 2, 3] [4, 5] == 3
test "match1" = match1 0 == 1
test "size 0" = size 0 == "none"
test "size 1" = size 1 == "one"
test "size 7" = size 7 == "many"
test "greeting" = greeting { name = "Bo", age = 3 } == "hi Bo"
test "greeting newborn" = greeting { name = "Bo", age = 0 } == "hi Bo (newborn)"
test "tuple" = swapIfZero (0, 4) == (4, 0)
test "tuple other" = swapIfZero (2, 4) == (2, 4)

-- Effectful scrutinees and branches.
fstOf : Pair a b -> a
fstOf (MkPair x y) = x

sndOf : Pair a b -> b
sndOf (MkPair x y) = y

eqNats : List Nat -> List Nat -> Bool
eqNats Nil         Nil         = True
eqNats (Cons x xs) (Cons y ys) = if x == y then eqNats xs ys else False
eqNats _           _           = False

ability Log where
  say : Nat -> {Log} ()

collect : (() -> {Log | e} a) -> {e} Pair (List Nat) a
collect prog =
  handle prog () with
    | return x     -> MkPair Nil x
    | say n => k   ->
      let rest = k ()
      MkPair (Cons n (fstOf rest)) (sndOf rest)

loud : Nat -> {Log} Nat
loud n =
  say n
  n

-- Two effectful scrutinees: each runs once, left to right, before the
-- branches.
twoScrutinees : () -> {Log} Nat
twoScrutinees u =
  say 0
  let r = match loud 1, loud 2 with
    | Zero, _ -> 10
    | Succ a, b -> a + b
  say 9
  r

-- Abilities performed in the branches of a lifted match.
inBranches : Nat -> {Log} Nat
inBranches n =
  say 0
  let r = match n with
    | Zero ->
      say 1
      5
    | Succ m ->
      say 2
      say m
      6
  r

-- A whole-right-hand-side match in an effectful definition (in the tree).
tailEff : Nat -> {Log} Nat
tailEff n = match n with
  | Zero -> 0
  | Succ m ->
    say m
    tailEff m

-- A named effectful scrutinee: `h` is about the bound result.
named : () -> {Log} Nat
named u = match h : loud 3 with
  | Zero -> 0
  | Succ m -> m

test "scrutinees once, in order" =
  let r = collect twoScrutinees
  if eqNats (fstOf r) [0, 1, 2, 9] then sndOf r == 2 else False
test "branches" =
  let r = collect (\u -> inBranches 3)
  if eqNats (fstOf r) [0, 2, 2] then sndOf r == 6 else False
test "tail" = eqNats (fstOf (collect (\u -> tailEff 3))) [2, 1, 0]
test "named" =
  let r = collect named
  if eqNats (fstOf r) [3] then sndOf r == 2 else False
