-- The expected result type is used first (docs/proposals/syntax-conveniences.md,
-- section 7): when `f a b` is checked against a known type, the type of
-- `f a b` is compared with it before the arguments are checked, so they are
-- checked knowing more. If that comparison fails, everything is undone and
-- the application is elaborated the old way.

import Std (List)

type Dir: Type =
  | TL
  | TR

type Rot = { dir: Dir, amount: Nat }

type Point = { x: Nat, y: Nat }

-- Record literals take their type from the expected result.

-- The AoC case (docs/aoc-2025.md, section 9, item 4): a record literal in a
-- lambda passed to `optionThen`. The result `Option Rot` fixes `b`.
def optionThen: Option a -> (a -> Option b) -> Option b
  | None, f => None
  | Some x, f => f x

def parse (n: Nat) (m: Option Nat): Option Rot := optionThen m (x => Some ({ dir = TL, amount = n + x }))

def amountOf: Option Rot -> Nat
  | None => 0
  | Some r => r.amount

-- The record literal's type comes from the result `List Point`.
def points (xs: List Nat): List Point := List.map xs (x => { x = x, y = 0 })

-- Likewise for the accumulator of a fold.
def sumPoints (rs: List Nat): Point := List.foldRight rs { x = 0, y = 0 } (p acc => { x = p + acc.x, y = acc.y })

test "parse" := amountOf (parse 1 (Some 2)) == 3
test "parse nothing" := amountOf (parse 1 None) == 0
test "sumPoints" := (sumPoints [1, 2, 3]).x == 6

-- Literals take their type from the expected result.
def chooseFirst [a: Type] (x: a) (y: a): a := x

-- `a := Int` from the result, before `5` is checked.
def r (i: Int): Int := chooseFirst 5 i

-- A partial application: the remaining function type `a -> a` is compared
-- with `Int -> Int`.
def partly: Int -> Int := chooseFirst 5

-- A named implicit argument.
def second [a: Type] [b: Type] (x: a) (y: b): b := y

def named (i: Int): Int := second [a := Nat] 5 i

-- Previously rejected (docs/proposals/integers.md, table of numeric
-- expressions): `same 5 + i`.
def same [a: Type] (x: a): a := x

def plusOne (i: Int): Int := same 5 + i

test "r" := r (-3) == 5
test "partly" := partly 1 == 5
test "named" := named 7 == 7
test "plusOne" := plusOne 1 == 6

-- Where comparing first doesn't fit, the application is retried the old way.
ability Choose where
  choose: () -> {Choose} Bool

ability State (s: Type) where
  get: () -> {State s} s
  put: s -> {State s} ()

type Box (a: Type): Type =
  | MkBox (x: a)

def unbox: [a: Type] -> Box a -> a
  | MkBox x => x

def chooser(): {Choose} Nat := if choose() then 1 else 0

def box: Box (() -> {Choose} Nat) := MkBox chooser

-- Comparing first makes `a` the wider function type, and then `box` doesn't
-- fit. The retry takes `a` from `box`, then widens the function to the bigger
-- row.
def wider: () -> {Choose, State Nat} Nat := unbox box

def p(): {State Nat, Choose} Nat :=
  let b := choose()
  if b then put 1 else ()
  get()

def pureBox: Box (() -> {State Nat, Choose} Nat) := MkBox p

-- The same with a row in a different order.
def reordered: () -> {Choose, State Nat} Nat := unbox pureBox

-- A row-order difference in an argument position.
def q: () -> {Choose, State Nat} Nat := same p

def runIt (f: () -> {Choose, State Nat} Nat): Nat := 0

def ran: Nat := runIt p

test "runIt" := ran == 0

-- A total lambda where a partial function is expected.
def asPartial: Nat -> {Partial} Nat := same (n => n)

-- A comparison that fails part-way (the domain is solved before the rows
-- differ), followed by a coercion.
def poly [a: Type] (x: a): {Choose} Nat := chooser()

def widened: Nat -> {Choose, State Nat} Nat := poly

-- A dependent result type is skipped by the comparison, and still accepted.
def idE (t: Type) (x: t): t := x

def useE: Int := idE Int 5

test "useE" := useE == 5
