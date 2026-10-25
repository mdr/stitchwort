-- Shared-field update (docs/proposals/variant-fields.md §6): `{ c | id = x }`
-- on a value of a type with several constructors rebuilds whichever
-- constructor `c` is, with the named fields replaced. Every named field
-- must be shared (see examples/accept/shared-fields.sw).

import Std (IO, List, Nat, Pair, Vec)

type Shape =
  | Dot (ref: Nat) (id: Text) (start: Nat)
  | Circle (ref: Nat) (id: Text) (start: Nat) (text: Text)

def s: Shape := Circle 1 "a" 0 "t"

-- One field. The other fields, `text` included, are kept.
test "one field" := { s | id = "b" } == Circle 1 "b" 0 "t"
test "other constructor" := { Dot 1 "x" 2 | ref = 9 } == Dot 9 "x" 2

-- Several at once, in either written order.
test "two fields" := { s | id = "b", start = 5 } == Circle 1 "b" 5 "t"
test "two fields, other order" := { s | start = 5, id = "b" } == Circle 1 "b" 5 "t"

-- A lambda, in a `map`.
test "map" :=
  ([Dot 1 "p" 0, s].map (x => { x | start = 3 })).map .start == [3, 3]

-- Whatever the constructor, the new value is read back.
-- (In a type, `{` starts an effect row, so the update is bracketed.)
theorem idUpdated (c: Shape) (x: Text): ({ c | id = x }).id = x :=
  match c with
    | Dot _ _ _ => rfl
    | Circle _ _ _ _ => rfl

-- A parameterised type.
type Labelled (a: Type) =
  | One (label: a)
  | Two (x: Nat) (label: a)

test "parameter" := { Two 3 "x" | label = "y" } == Two 3 "y"

-- Dependent fields: `xs` has a type that mentions `n`, so `n` and `xs` are
-- updated together, or `xs` alone when its new type is `Vec Nat (Sized.n a)`.
type Sized =
  | A (n: Nat) (xs: Vec Nat n)
  | B (tag: Text) (n: Nat) (xs: Vec Nat n)

def replaceXs (a: Sized) (ys: Vec Nat (Sized.n a)): Sized := { a | xs = ys }

-- The base may be any expression, not only a variable.
def pick (b: Bool) (a: Sized): Sized := if b then a else a

def replaceXsOf (b: Bool) (a: Sized) (ys: Vec Nat (Sized.n (pick b a))): Sized :=
  { pick b a | xs = ys }

def resize (a: Sized): Sized := { a | n = 1, xs = VCons 7 VNil }

test "same length" := (replaceXs (A 1 (VCons 1 VNil)) (VCons 2 VNil)).n == 1
test "new length" := (resize (B "q" 0 VNil)).n == 1

-- An implicit field that does not mention the updated field is kept.
type Labelled2 =
  | LA (n: Nat) [h: n = 0] (label: Text)
  | LB (n: Nat) [h: n = 0] (label: Text)

def relabel (a: Labelled2): Labelled2 := { a | label = "x" }

test "implicit kept" := (relabel (LA 0 [h := rfl] "a")).label == "x"

-- A one-constructor type that is not a record.
test "pair" := { (1, "x") | fst = 2 } == (2, "x")

-- Effects: the base runs once, first; the new values run in the order
-- written, not the order of the fields.
type V =
  | P (a: Text) (b: Text)
  | Q (b: Text) (c: Nat) (a: Text)

def orNone: Option Text → Text
  | None => "none"
  | Some t => t

def next(): {IO} Text := orNone IO.readLine()

def base(): {IO} V :=
  IO.print "base"
  Q "y" 3 "x"

def updated(): {IO} V := { base() | b = next(), a = next() }

test "order" := Pair.snd (IO.simulate ["1", "2"] updated) == Q "1" 3 "2"
test "base once" := Pair.fst (IO.simulate ["1", "2"] updated) == ["base"]
