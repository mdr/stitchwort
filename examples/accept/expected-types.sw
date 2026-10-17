-- The expected result type is used first (docs/proposals/syntax-conveniences.md,
-- section 7): when `f a b` is checked against a known type, the type of
-- `f a b` is compared with it before the arguments are checked, so they are
-- checked knowing more. If that comparison fails, everything is undone and
-- the application is elaborated the old way.

type Dir : Type =
  | TL
  | TR

type Rot = { dir : Dir, amount : Nat }

type Point = { x : Nat, y : Nat }

-- Record literals take their type from the expected result.

-- The AoC case (docs/aoc-2025.md, section 9, item 4): a record literal in a
-- lambda passed to `maybeThen`. The result `Maybe Rot` fixes `b`.
maybeThen : Maybe a -> (a -> Maybe b) -> Maybe b
maybeThen Nothing f = Nothing
maybeThen (Just x) f = f x

parse : Nat -> Maybe Nat -> Maybe Rot
parse n m = maybeThen m (\x -> Just { dir = TL, amount = n + x })

amountOf : Maybe Rot -> Nat
amountOf Nothing = 0
amountOf (Just r) = r.amount

-- The record literal's type comes from the result `List Point`.
points : List Nat -> List Point
points xs = List.map (\x -> { x = x, y = 0 }) xs

-- Likewise for the accumulator of a fold.
sumPoints : List Nat -> Point
sumPoints rs = List.foldr (\r acc -> { x = r + acc.x, y = acc.y }) { x = 0, y = 0 } rs

test "parse" = amountOf (parse 1 (Just 2)) == 3
test "parse nothing" = amountOf (parse 1 Nothing) == 0
test "sumPoints" = (sumPoints [1, 2, 3]).x == 6

-- Literals take their type from the expected result.
chooseFirst : [a : Type] -> a -> a -> a
chooseFirst x y = x

-- `a := Int` from the result, before `5` is checked.
r : Int -> Int
r i = chooseFirst 5 i

-- A partial application: the remaining function type `a -> a` is compared
-- with `Int -> Int`.
partly : Int -> Int
partly = chooseFirst 5

-- A named implicit argument.
second : [a : Type] -> [b : Type] -> a -> b -> b
second x y = y

named : Int -> Int
named i = second [a := Nat] 5 i

-- Previously rejected (docs/proposals/integers.md, table of numeric
-- expressions): `same 5 + i`.
same : [a : Type] -> a -> a
same x = x

plusOne : Int -> Int
plusOne i = same 5 + i

test "r" = r (-3) == 5
test "partly" = partly 1 == 5
test "named" = named 7 == 7
test "plusOne" = plusOne 1 == 6

-- Where comparing first doesn't fit, the application is retried the old way.
ability Choose where
  choose : () -> {Choose} Bool

ability State (s : Type) where
  get : () -> {State s} s
  put : s -> {State s} ()

type Box (a : Type) : Type =
  | MkBox (x : a)

unbox : [a : Type] -> Box a -> a
unbox (MkBox x) = x

chooser : () -> {Choose} Nat
chooser u = if choose () then 1 else 0

box : Box (() -> {Choose} Nat)
box = MkBox chooser

-- Comparing first makes `a` the wider function type, and then `box` doesn't
-- fit. The retry takes `a` from `box`, then widens the function to the bigger
-- row.
wider : () -> {Choose, State Nat} Nat
wider = unbox box

p : () -> {State Nat, Choose} Nat
p u =
  let b = choose ()
  if b then put 1 else ()
  get ()

pureBox : Box (() -> {State Nat, Choose} Nat)
pureBox = MkBox p

-- The same with a row in a different order.
reordered : () -> {Choose, State Nat} Nat
reordered = unbox pureBox

-- A row-order difference in an argument position.
q : () -> {Choose, State Nat} Nat
q = same p

runIt : (() -> {Choose, State Nat} Nat) -> Nat
runIt f = 0

ran : Nat
ran = runIt p

test "runIt" = ran == 0

-- A total lambda where a partial function is expected.
asPartial : Nat -> {Partial} Nat
asPartial = same (\n -> n)

-- A comparison that fails part-way (the domain is solved before the rows
-- differ), followed by a coercion.
poly : [a : Type] -> a -> {Choose} Nat
poly x = chooser ()

widened : Nat -> {Choose, State Nat} Nat
widened = poly

-- A dependent result type is skipped by the comparison, and still accepted.
idE : (t : Type) -> t -> t
idE t x = x

useE : Int
useE = idE Int 5

test "useE" = useE == 5
