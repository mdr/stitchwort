-- Constructor fields that the result indices determine
-- (docs/proposals/erase-determined-fields.md). The fast runtimes don't
-- store them: a match that reads one rebuilds it from the matched value's
-- index. The reference evaluator stores them, so every runner prints the
-- same (crates/native/tests/it/determined_fields.rs).

import Std (Fin, List, Nat, Text, Vec)

-- `n` is determined: `Floor`'s index is `Succ n`.
type Tower: Nat → Type = | Ground: Tower 0 | Floor (label: Nat) (below: Tower n): Tower (Succ n)

-- Read at run time: `k` is rebuilt as the height less one.
def Tower.height: Tower n → Nat
  | Ground => 0
  | Floor [n := k] _ _ => Succ k

-- Passed on as an implicit argument, never read.
def Tower.labels: Tower n → List Nat
  | Ground => []
  | Floor label below => [label, ..Tower.labels below]

-- Nested patterns: two floors down, the field is the height less two.
def Tower.second: Tower n → Nat
  | Floor [n := k] _ (Floor _ _) => k
  | _ => 0

-- The whole index is the field, so a match reads the scrutinee's index
-- (`Count.tag` is generated, as a shared field).
type Count: Nat → Type = | MkCount (n: Nat) (tag: Text): Count n

def Count.value: Count n → Nat
  | MkCount n _ => n

-- Here the matched value's index is a call, so reading `n` computes it
-- again: the census of rebuilds (`STITCHWORT_REBUILD_CENSUS`) lists this one.
def countOf (xs: List Nat): Count (List.length xs) → Nat
  | MkCount n _ => n

-- An index computed by a definition: `size` stays stored (`Padded.size`
-- is generated, as a shared field).
type Padded: Nat → Type = | MkPadded (size: Nat) (items: List Nat): Padded (Nat.add size 2)

-- The same field in two indices.
type Pair2: Nat → Nat → Type = | Twice (n: Nat): Pair2 n n

def Pair2.value: Pair2 a b → Nat
  | Twice n => n

-- `i` depends on `n`, and `n` is determined by both of them.
type Slot: (n: Nat) → Fin n → Type = | MkSlot (n: Nat) (i: Fin n): Slot (Succ n) (FSucc i)

def Slot.width: Slot n i → Nat
  | MkSlot n i => n + Fin.toNat i

def tower: Tower 3 := Floor 30 (Floor 20 (Floor 10 Ground))

def vector: Vec Nat 4 := VCons 1 (VCons 2 (VCons 3 (VCons 4 VNil)))

def count (xs: List Nat): Count (List.length xs) := MkCount (List.length xs) "items"

def report: Text :=
  "height ${Tower.height tower}, labels ${Tower.labels tower}, second ${Tower.second tower}; "
    ++ "fin ${Fin.toNat (FSucc (FSucc FZero): Fin 5)}, get ${Vec.get vector (Fin.ofNat 2)}; "
    ++ "vector ${Vec.toList (Vec.map vector (x => x * 10))}, sum ${Vec.sum vector}; "
    ++ "count ${Count.value (count [5, 6, 7])} ${countOf [1, 2] (count [1, 2])} ${Count.tag (count [])}; "
    ++ "padded ${Padded.size (MkPadded 3 [1])}, twice ${Pair2.value (Twice 9)}; "
    ++ "slot ${Slot.width (MkSlot 4 (FSucc FZero))}"

def main(): {IO} () := IO.print report
