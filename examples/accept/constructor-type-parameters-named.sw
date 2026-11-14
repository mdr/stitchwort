-- A constructor takes its type's parameters as named implicit arguments,
-- by the names in the type's header, as a function takes its own (D3514):
-- `Nil [a := Nat]` is the empty `List Nat`. They are implicit, so they're
-- given by name only, in any order, mixed with the constructor's fields.

type Pair (a: Type) (b: Type) = | MkPair (first: a) (second: b)

type Vec (a: Type): Nat -> Type = | VNil: Vec a 0 | VCons [n: Nat] (x: a) (xs: Vec a n): Vec a (Succ n)

def noNumbers: List Nat := Nil [a := Nat]
def oneNumber: List Nat := Cons [a := Nat] 1 Nil
def noText: Option Text := None [a := Text]

-- Several parameters, in any order.
def numberAndFlag: Pair Nat Bool := MkPair [b := Bool] [a := Nat] 1 True

-- With nothing else to say the type: `Nil` alone wouldn't know what its
-- items are, and `1` would be a `Nat`.
test "an empty list of a named type" := (Nil [a := Int]).length == 0
test "a literal takes the named type" := MkPair [a := Int] [b := Text] 1 "x" == MkPair (1: Int) "x"

-- Beside the constructor's own implicit fields.
def short: Vec Nat 1 := VCons [a := Nat] [n := 0] 1 VNil

-- With a field given by name, and one left out: a function of the tail.
def startWithZero: List Nat -> List Nat := Cons [a := Nat] (head := 0)
test "partly applied" := startWithZero [1] == [0, 1]
