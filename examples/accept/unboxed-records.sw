-- Unboxed one-field records, the differential example (D866,
-- docs/proposals/map-equality.md §13.1): a record with exactly one run-time
-- field (proof and type fields are erased) is stored as that field's value.
-- Every runner must print the same thing as the reference evaluator.

import Std (IO, List, Map, Mod, Nat, Option, Ord, Set)

type UserId = { value: Text }
type Count = { n: Nat }

def bump: Count -> Count
  | { n = k } => { n = k + 1 }

def reset (c: Count): Count := { c | n = 0 }

-- 2: a data field plus a proof.
type Below (bound: Nat) = { value: Nat, isLt: value < bound }

def two: Below 5 := { value = 2, isLt = rfl }
def four: Below 5 := { value = 4, isLt = rfl }

-- 3: polymorphic.
type Box (a: Type) = { item: a }

def applyBox (b: Box (Nat -> Nat)) (x: Nat): Nat := b.item x

-- 4: nested in data.
type Shape =
  | Circle (r: Count)
  | Square (s: Count)

def area: Shape -> Nat
  | Circle r => 3 * r.n * r.n
  | Square s => s.n * s.n

-- 5: an Option inside.
type Maybe = { inner: Option Nat }

def orZero: Maybe -> Nat
  | { inner = None } => 0
  | { inner = Some k } => k

-- 8: a type field and a data field.
type Tagged: Type 1 = { ty: Type, v: Nat }

-- 9: no run-time field, and two.
type Ok (n: Nat) = { proof: n < 10 }
type Wrapped = { n: Nat, ok: Ok n }
type Pair2 = { a: Nat, b: Text }

def wrapped: Wrapped := { n = 3, ok = { proof = rfl } }

-- 10: containers.
type Inventory = { stock: Map Text Nat }

def inv: Inventory := { stock = Map.fromList [("apple", 3), ("pear", 5)] }

-- 11: a one-method interface.
interface Describe (a: Type) =
  { describe: a -> Text }

instance Describe.instCount: Describe Count :=
  { describe = c => "count " ++ Nat.toText c.n }

def counts: List Count := [{ n = 3 }, { n = 1 }, { n = 2 }]

test "projection" := (bump { n = 1 }).n == 2
test "update" := (reset { n = 9 }).n == 0
test "eq" := (bump { n = 1 }) == { n = 2 } && ({ n = 1 }: Count) != { n = 2 }
test "text eq" := ({ value = "a" }: UserId) == { value = "a" }
test "ord" := Ord.compare ({ n = 1 }: Count) { n = 2 } == Less
test "sort" := List.sort counts == [{ n = 1 }, { n = 2 }, { n = 3 }]
test "below" := two != four && two.value == 2
test "box fn" := applyBox { item = n => n * 2 } 21 == 42
test "box nested" := ({ item = { item = 7 } }: Box (Box Nat)).item.item == 7
test "box list" := ({ item = [1, 2] }: Box (List Nat)).item.length == 2
test "shape" := area (Circle ({ n = 2 })) == 12 && area (Square ({ n = 3 })) == 9
test "maybe" := orZero { inner = None } == 0 && orZero { inner = Some 4 } == 4
test "constructor as function" := (List.map (x => ({ n = x }: Count)) [1, 2, 3]) == [{ n = 1 }, { n = 2 }, { n = 3 }]
test "no field" := wrapped.n == 3
test "two fields" := ({ a = 1, b = "x" }: Pair2) == { a = 1, b = "x" }
test "map of records" := (Map.fromList [(1, ({ n = 5 }: Count))]).get 1 == Some ({ n = 5 })
test "inventory" := inv.stock.get "pear" == Some 5
test "interface" := Describe.describe ({ n = 4 }: Count) == "count 4"

def main(): {IO} () :=
  IO.print "-- plain"
  IO.print "${bump { n = 1 }}"
  IO.print "${({ value = "u1" }: UserId)}"
  IO.print "${reset { n = 9 }}"
  IO.print "${(bump { n = 1 }) == { n = 2 }}"
  IO.print "${Ord.compare ({ n = 1 }: Count) { n = 2 }}"
  IO.print "${List.sort counts}"
  IO.print "${List.map bump counts}"
  IO.print "-- proofs"
  IO.print "${two}"
  IO.print "${two == four} ${two.value}"
  IO.print "${(Mod.ofNat 7: Mod 5)}"
  IO.print "${(Mod.ofNat 7: Mod 5) == Mod.ofNat 2}"
  IO.print "${(List.attach [1, 2]).map (m => m.value)}"
  IO.print "-- box"
  IO.print "${({ item = 3 }: Box Nat)}"
  IO.print "${applyBox { item = n => n + 1 } 1}"
  IO.print "${({ item = [1, 2] }: Box (List Nat))}"
  IO.print "${({ item = { item = 7 } }: Box (Box Nat))}"
  IO.print "-- nested"
  IO.print "${(Some ({ value = "x" }): Option UserId)}"
  IO.print "${(({ n = 1 }: Count), ({ value = "y" }: UserId))}"
  IO.print "${area (Circle ({ n = 2 }))} ${area (Square ({ n = 3 }))}"
  IO.print "${(Circle ({ n = 2 }): Shape) == Circle ({ n = 2 })}"
  IO.print "${orZero { inner = None }} ${orZero { inner = Some 4 }}"
  IO.print "${({ inner = Some 4 }: Maybe)}"
  IO.print "-- erased"
  IO.print "${({ ty = Nat, v = 8 }: Tagged).v}"
  IO.print "${wrapped.n}"
  IO.print "${({ a = 1, b = "x" }: Pair2)}"
  IO.print "-- containers"
  let m: Map Nat Count := Map.fromList [(2, { n = 20 }), (1, { n = 10 })]
  IO.print "${m}"
  IO.print "${m.get 2} ${m.get 3} ${m.size}"
  IO.print "${m.insert 3 { n = 30 }}"
  IO.print "${m.toList}"
  IO.print "${m == Map.fromList [(1, { n = 10 }), (2, { n = 20 })]}"
  let s: Set UserId := Set.fromList [{ value = "b" }, { value = "a" }, { value = "b" }]
  IO.print "${s} ${s.size}"
  IO.print "${s.contains { value = "a" }}"
  IO.print "${s == Set.fromList [{ value = "a" }, { value = "b" }]}"
  IO.print "${inv.stock}"
  IO.print "${inv == { stock = Map.fromList [("pear", 5), ("apple", 3)] }}"
  IO.print "${{ inv | stock = inv.stock.insert "fig" 1 }.stock.size}"
  IO.print "-- interface"
  IO.print (Describe.describe ({ n = 4 }: Count))
