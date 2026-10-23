-- Pipe forward `|>`. `x |> f a b` is `f a b x`: the value on the left becomes
-- the LAST argument, which is why the library puts the main argument last
-- (`List.map f xs`). `|>` is the loosest operator except `->`, and groups to
-- the left, so a pipeline reads top to bottom. The left side is checked, and
-- run, before the arguments on the right.

import Std (IO, List, Nat, Pair)

type Person = { name: Text, age: Nat }

def people: List Person := [{ name = "Ann", age = 30 }, { name = "Bob", age = 25 }]

-- The left side is checked first, so its type is known when the lambda is
-- checked: `p: Person`. `List.map (p => p.name) people` can't do that.
def names: List Text := people |> List.map (p => p.name)

test "inference through a pipe" := names == ["Ann", "Bob"]

-- A multi-line pipeline: a line may start with `|>` when it's indented at
-- least as far as the line the expression starts on, even at the block's own
-- column, as with `then` and `else`.
def total: Nat :=
  people
    |> List.map (p => p.age)
    |> List.sum

def sortedDoubled: List Nat :=
  let xs := [3, 1, 2]
  xs
    |> List.sort
    |> List.map (x => x * 2)

test "total" := total == 55
test "sorted and doubled" := sortedDoubled == [2, 4, 6]

-- Arithmetic binds tighter than `|>`, and a chain groups to the left.
test "precedence" := (1 + 2 |> n => n == 3)
test "left associative" := ([3, 1, 2] |> List.sort |> List.sum) == 6

-- `|>` is looser than `=`, so a comparison on the result needs brackets.
test "brackets" := ([1, 2, 3] |> List.sum) == 6

-- Dot notation on the left of a pipe.
test "dot on the left" := ([1, 2, 3] |> List.map (x => x + 1)).length == 3

-- A lambda on the right; its body takes the rest of the pipeline.
def lam: Nat := 5 |> y => y + 1
def lamChain: Nat := 5 |> y => y + 1 |> z => z * 2

test "lambda" := lam == 6
test "lambda chain" := lamChain == 12

-- A constructor is a function, a local function variable is a head too, and a
-- number literal on the left just takes its type from the function.
def ctor: Option Nat := 3 |> Some
def applyTo (h: Nat -> Nat): Nat := 3 |> h
def literal: Nat := 5 |> Nat.add 1

test "constructor" := ctor == Some 3
test "local function" := applyTo (x => x + 1) == 4
test "literal" := literal == 6

-- Named implicit arguments work on the right as in any call.
def named: List Nat := [1, 2] |> List.map [b := Nat] (x => x)

test "named implicit" := named == [1, 2]

-- A `match` can be piped (a `|>` line left of the alternatives' `|` pipes
-- the whole `match`), and a pipe can be in an alternative.
def classify (n: Nat): Nat :=
  match n with
    | 0 => 1
    | _ => n
  |> k => k + 10

def inArm: Nat -> Nat
  | 0 => [1, 2] |> List.sum
  | n => n

test "match piped" := classify 0 == 11 && classify 5 == 15
test "pipe in an arm" := inArm 0 == 3 && inArm 4 == 4

-- Effects: the left side runs first, then the right side's arguments, then
-- the call.
def say (t: Text) (n: Nat): {IO} Nat :=
  IO.print t
  n

def addSay (a: Nat) (b: Nat): {IO} Nat :=
  IO.print "call"
  a + b

def order(): {IO} Nat := say "left" 1 |> addSay (say "right" 2)

def chain(): {IO} Nat :=
  say "a" 1
    |> addSay 10
    |> x => say "end" x

test "effect order" := Pair.fst (IO.simulate [] order) == ["left", "right", "call"]
test "effect value" := Pair.snd (IO.simulate [] order) == 3
test "effect chain" := Pair.fst (IO.simulate [] chain) == ["a", "call", "end"]
