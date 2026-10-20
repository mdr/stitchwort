-- Patterns in `let` and in lambdas (docs/proposals/syntax-conveniences.md
-- section 5). `let p := e` followed by the rest of the block is
-- `match e with | p => rest`; `\p => body` matches its parameter. The
-- pattern must cover every value of its type.

import List (map, foldLeft, zip)

-- A tuple.
def divMod7 (n: Nat): (Nat, Nat) := (n / 7, n % 7)

def digitsSum (n: Nat): Nat :=
  let (q, r) := divMod7 n
  q + r

-- Nested tuples, and `_`.
def flatten (t: ((Nat, Nat), Nat)): Nat :=
  let ((a, b), c) := t
  let (_, d) := (a, b + c)
  a + d

-- A constructor applied to its fields, without brackets.
def swap (p: Pair Nat Text): Pair Text Nat :=
  let MkPair a b := p
  MkPair b a

-- A record.
type Person = { name: Text, age: Nat }

def greeting (p: Person): Text :=
  let { name, .. } := p
  "hello " ++ name

-- With a type: the right-hand side is checked against it.
def annotated: Nat :=
  let (a, b): (Nat, Nat) := (1, 2)
  a + b

-- Not the whole right-hand side, so the `match` is lifted.
def lifted (p: (Nat, Nat)): Nat :=
  let k := 1
  let (a, b) := p
  a + b + k

-- `()`: the one value of `()`.
def unit (u: ()): Nat :=
  let () := u
  3

-- Lambdas: a pattern parameter, one among others, and a record.
def sums (ps: List (Nat, Nat)): List Nat := ps.map ((a, b) => a + b)

def total (entries: List (Text, Nat)): Nat := entries.foldLeft (acc (k, v) => acc + v) 0

-- A record pattern needs its type known where the lambda is checked, as
-- `p.name` does: here, from the signature.
def nameOf: Person -> Text := { name, .. } => name

def nestedLambda (xs: List ((Nat, Nat), Nat)): List Nat := xs.map (((a, b), c) => a * b + c)

-- A proof: `let (a, b) = p` on a variable refines `p` to `(a, b)`, so the
-- goal computes.
def swapPair: (a, b) -> (b, a)
  | (x, y) => (y, x)

theorem swapTwice (p: (Nat, Nat)): swapPair (swapPair p) = p :=
  let (a, b) := p
  rfl

-- Termination: `kids` is part of the tree `let` matched, so the recursive
-- call is smaller, as for a pattern in the equation.
type Tree: Type =
  | Node (label: Nat) (kids: Forest)

type Forest: Type =
  | FNil
  | FCons (t: Tree) (ts: Forest)

def sumTree (t: Tree): Nat :=
  let Node x kids := t
  x + sumForest kids

def sumForest: Forest -> Nat
  | FNil       => 0
  | FCons t ts => sumTree t + sumForest ts

-- The same, lifted into a helper (the `let` isn't the whole right-hand side).
def sumTreeLifted (t: Tree): Nat :=
  let one := 1
  let Node x kids := t
  x * one + sumForestLifted kids

def sumForestLifted: Forest -> Nat
  | FNil       => 0
  | FCons t ts => sumTreeLifted t + sumForestLifted ts

-- Effects: the right-hand side runs once, before the rest of the block.
def readTwo(): {IO} (Maybe Text, Maybe Text) :=
  let a := IO.readLine()
  let b := IO.readLine()
  (a, b)

def swapLines(): {IO} Nat :=
  let (a, b) := readTwo()
  IO.print (Maybe.withDefault "" b)
  IO.print (Maybe.withDefault "" a)
  let (n, m) := (1, 2)
  IO.print "done"
  n + m

def eqTexts: List Text -> List Text -> Bool
  | Nil,       Nil       => True
  | Cons x xs, Cons y ys => if x == y then eqTexts xs ys else False
  | _,         _         => False

test "tuple" := digitsSum 23 == 5
test "nested" := flatten ((1, 2), 3) == 6
test "constructor" := (swap (MkPair 1 "x")).snd == 1
test "record" := greeting { name = "Ann", age = 3 } == "hello Ann"
test "annotated" := annotated == 3
test "lifted" := lifted (2, 3) == 6
test "unit" := unit() == 3
test "lambda" := sums [(1, 2), (3, 4)] == [3, 7]
test "foldLeft" := total [("a", 1), ("b", 2)] == 3
test "record lambda" := nameOf { name = "Ann", age = 3 } == "Ann"
test "nested lambda" := nestedLambda [((2, 3), 1)] == [7]
test "tree" := sumTree (Node 1 (FCons (Node 2 FNil) FNil)) == 3
test "tree lifted" := sumTreeLifted (Node 1 (FCons (Node 2 FNil) FNil)) == 3
test "effects run once, in order" :=
  eqTexts (IO.simulate ["x", "y", "z", "w"] swapLines).fst ["y", "x", "done"]
test "effects result" := (IO.simulate ["x", "y"] swapLines).snd == 3
test "in a test" :=
  let (a, b) := (1, 2)
  a + b == 3

-- Outside a proof, a tuple or record pattern binds projections of the
-- value (docs/proposals/let.md §7), so a function using one computes even on
-- an unknown pair.
def swapped (p: (Nat, Text)): (Text, Nat) :=
  let (a, b) := p
  (b, a)

theorem swappedUnfolds (p: (Nat, Text)): swapped p = (p.snd, p.fst) := rfl

def sumOf (n: Nat): Nat :=
  let ((a, b), c) := ((n, n + 1), n + 2)
  a + b + c

theorem sumOfIs (n: Nat): sumOf n = n + (n + 1) + (n + 2) := rfl

def nameLength (p: Person): Nat :=
  let { name, age } := p
  name.length + age

theorem nameLengthIs (p: Person): nameLength p = p.name.length + p.age := rfl
