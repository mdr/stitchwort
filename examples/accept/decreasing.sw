-- Recursion on a measure (docs/proposals/well-founded-recursion.md): a
-- definition says `decreasing m`, a `Nat` of its header's parameters, and
-- every recursive call needs a proof that `m` gets smaller, found by `auto`
-- or given as `[decreasing := proof]`. The compiler turns it into
-- structural recursion on a hidden fuel argument, and proves `f.unfold`,
-- the definition's own equation, so proofs never see the fuel.
-- `stitchwort run` and `run --js` run the recursion as written.
--
--   $ stitchwort run examples/accept/decreasing.sw
--   digits: 4
--   gcd: 6
--   halvings: 7
--   sum of digits: 10
--
-- differential: skip (the recursive reference evaluator computes every proof
-- strictly, and `Nat.divTenLess` at each step takes minutes; the
-- runtimes erase them. decreasing-folded.sw is compared instead)

import Std (IO, List, Nat)

-- The decimal digits of `n`, most significant first, onto `acc`: `n / 10`
-- isn't a piece of `n`, so structural recursion can't show this ends.
def digitsOnto (n: Nat) (acc: List Nat): List Nat
    decreasing n
:=
  if big: Nat.leq n 9 = False
  then digitsOnto (n / 10) (Cons (n % 10) acc) [decreasing := Nat.divTenLess n big]
  else Cons n acc

def digits (n: Nat): List Nat := digitsOnto n Nil

test "digits" := digits 1234 == [1, 2, 3, 4]
test "digits of 0" := digits 0 == [0]

-- Tests and `rfl` compute: the fuel is a number, used up one step per call.
theorem digitsByRfl: digits 1234 = [1, 2, 3, 4] := rfl

-- The equation the compiler proves, with `digitsOnto` itself in the
-- recursive call.
theorem digitsOntoStep (n: Nat) (acc: List Nat):
    digitsOnto n acc = (if big: Nat.leq n 9 = False then digitsOnto (n / 10) (Cons (n % 10) acc) else Cons n acc) :=
  digitsOnto.unfold n acc

-- Euclid's algorithm: `a % b < b` when `b != 0`.
def gcd (a: Nat) (b: Nat): Nat
    decreasing b
:=
  if h: b = 0 then a else gcd b (a % b) [decreasing := Nat.modLess a b h]

test "gcd" := gcd 12 18 == 6 && gcd 17 5 == 1 && gcd 0 9 == 9

-- The guard style: test the decrease, and `auto` finds the proof in scope.
def halvings (n: Nat) (count: Nat): Nat
    decreasing n
:=
  let next := n / 2
  if h: next < n then halvings next (count + 1) else count

test "halvings" := halvings 100 0 == 7 && halvings 0 0 == 0

-- A `match` in the body, with the recursive call in one arm.
def sumDigits (n: Nat): Nat
    decreasing n
:=
  match e: Nat.leq n 9 with
    | True => n
    | False => n % 10 + sumDigits (n / 10) [decreasing := Nat.divTenLess n e]

test "sum of digits" := sumDigits 1234 == 10

-- Arms after the colon, an implicit type, and a measure that isn't a
-- parameter.
def takeFirst [a: Type] (xs: List a): Nat -> List a
    decreasing List.length xs
  | Zero => Nil
  | Succ k =>
    match xs with
      | Nil => Nil
      | Cons x rest => Cons x (takeFirst rest k [decreasing := Nat.leRefl (List.length rest)])

test "takeFirst" := takeFirst [1, 2, 3] 2 == [1, 2] && takeFirst [1, 2, 3] 5 == [1, 2, 3]

-- A recursive call written with a dot.
type Stack =
  | Empty
  | Push (x: Nat) (rest: Stack)

def Stack.count: Stack -> Nat
  | Empty => 0
  | Push x rest => Succ (Stack.count rest)

def Stack.total (s: Stack): Nat
    decreasing Stack.count s
:=
  match s with
    | Empty => 0
    | Push x rest => x + (if h: Stack.count rest < Stack.count s then rest.total else 0)

test "Stack.total" := Stack.total (Push 1 (Push 2 Empty)) == 3

-- A theorem can recurse on the same measure: the proof makes the calls the
-- function makes. `evens.unfold` takes one step of `evens`.
def evens (n: Nat): List Nat
    decreasing n
:=
  match n with
    | Zero => Nil
    | Succ Zero => Nil
    | Succ (Succ k) => Cons k (evens k [decreasing := Nat.leSucc k])

test "evens" := evens 7 == [5, 3, 1]

theorem evensShort (n: Nat): List.length (evens n) <= n
    decreasing n
:=
  rewrite evens.unfold n in
  match n with
    | Zero => rfl
    | Succ Zero => rfl
    | Succ (Succ k) =>
      Nat.leTrans (List.length (evens k)) k (Succ k) (evensShort k [decreasing := Nat.leSucc k]) (Nat.leSucc k)

def main(): {IO} () :=
  IO.print ("digits: " ++ Nat.toText (List.length (digits 1234)))
  IO.print ("gcd: " ++ Nat.toText (gcd 12 18))
  IO.print ("halvings: " ++ Nat.toText (halvings 100 0))
  IO.print ("sum of digits: " ++ Nat.toText (sumDigits 1234))
