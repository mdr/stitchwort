-- Types shaped like `Nat` (docs/proposals/nat-shaped-types.md): one
-- constructor stores no fields and the other stores one field of the type
-- itself, once proofs, types and fields the result index determines are
-- left out. They run as machine numbers, so every runner must give the
-- same answers as for the unary values the kernel sees: here a type with a
-- parameter, a proof field and its successor first, a family indexed by
-- types, and `Fin`, whose index `n` each constructor's result determines.

import Std (IO, Fin, List, Nat, Vec)

-- The successor comes first, and carries a proof as well as the rest.
type Count (a: Type) = | More (rest: Count a) (ok: 1 = 1) | Stop

def Count.of: Nat → Count a
  | Zero => Stop
  | Succ n => More (Count.of n) rfl

def Count.size: Count a → Nat
  | Stop => 0
  | More rest _ => Succ (Count.size rest)

-- Two levels at a time.
def Count.half: Count a → Nat
  | More (More rest _) _ => Succ (Count.half rest)
  | _ => 0

def Count.join: Count a → Count a → Count a
  | Stop, other => other
  | More rest ok, other => More (Count.join rest other) ok

-- An index of its own, a type (so erased): a field of the family at
-- another index.
type Depth: Type → Type 1 = | Flat: Depth Nat | Deeper (inner: Depth b): Depth (List b)

def Depth.size: Depth t → Nat
  | Flat => 0
  | Deeper inner => Succ (Depth.size inner)

def Nest: Nat → Type
  | Zero => Nat
  | Succ n => List (Nest n)

def Depth.tower: (n: Nat) → Depth (Nest n)
  | Zero => Flat
  | Succ n => Deeper (Depth.tower n)

-- Number patterns on a `Fin` are nested `FZero`/`FSucc` matches.
def label: Fin 5 → Text
  | 0 => "zero"
  | 1 => "one"
  | 3 => "three"
  | _ => "other"

def dropTwo: Fin n → Nat
  | FSucc (FSucc i) => Fin.toNat i
  | _ => 100

def digits: List (Fin 10) := [3, 1, 4, 1, 5, 9, 2, 6]

def largest: List (Fin 10) → Nat
  | [] => 0
  | [x, ..xs] => Nat.max (Fin.toNat x) (largest xs)

def squares: Vec Nat 6 := Vec.tabulate 6 (i => Fin.toNat i * Fin.toNat i)

def report: Text :=
  let c := Count.join (Count.of 7: Count Nat) (Count.of 5)
  let atFour := Vec.get squares (Fin.ofNatLt 6 4 rfl)
  let checked := List.filterMap [0, 3, 10, 12] (Fin.ofNatCheck 11)
  "${Count.size c} ${Count.half c} ${Depth.size (Depth.tower 9)} "
    ++ "${List.filterMap [0, 1, 2, 3, 4, 5] (Fin.ofNatCheck 5) |>.map label} "
    ++ "${dropTwo (7: Fin 9)} ${dropTwo (1: Fin 9)} ${largest digits} ${atFour} "
    ++ "${List.map checked Fin.toNat} ${if (4: Fin 10) < 7 then "lt" else "ge"} ${if (4: Fin 10) == 4 then "eq" else "ne"} ${(6: Fin 8)}"

test "count" := Count.size (Count.join (Count.of 3: Count Bool) (Count.of 4)) == 7
test "half" := Count.half (Count.of 9: Count Bool) == 4
test "depth" := Depth.size (Depth.tower 6) == 6
test "fin label" := label 3 == "three" ∧ label 4 == "other"
test "fin drop" := dropTwo (5: Fin 6) == 3

def main(): {IO} () := IO.print report
