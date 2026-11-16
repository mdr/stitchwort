-- In a match on several values, a tuple pattern in a later column is read
-- against that column's type as it is once the earlier columns are split
-- (docs/proposals/proof-tuples.md §4.2): here `AllSmall items` is only
-- `∧` once `items` is `[item, ..rest]`, so `(first, others)` is
-- `Both first others`.

def AllSmall: List Nat → Prop
  | [] => True
  | [n, ..rest] => n < 10 ∧ AllSmall rest

theorem dropSmall ∀ (items: List Nat) (small: AllSmall items): AllSmall (items.drop 1) := match items, small with
  | [], _ => small
  | [_, ..rest], (_, others) => others

-- The tuple in the first arm: the list, before it, is split first.
theorem headSmall ∀ (items: List Nat) (small: AllSmall items) (nonEmpty: items ≠ []): ∃ (n: Nat) => n < 10 :=
  match items, small with
    | [item, .._], (first, _) => (item, first)
    | [], _ => (nonEmpty byComputing).impossible

-- A column that is `∃` once the first is split, taken apart three deep.
def Bounded: Bool → Nat → Prop
  | True, n => ∃ (k: Nat) => k < 5 ∧ n = k
  | False, _ => True

theorem boundedBelow ∀ (tight: Bool) (n: Nat) (bound: Bounded tight n): n < 5 ∨ tight = False := match tight, bound with
  | True, (_, below, same) => Inl (rewrite same then below)
  | False, _ => Inr byComputing

-- A later column whose type stays data after the split is still a pair.
def Slot: Bool → Type
  | True => (Nat, Nat)
  | False => Nat

def slotSum: (flag: Bool) → Slot flag → Nat
  | True, (a, b) => a + b
  | False, n => n

theorem slotSumPair: slotSum True (2, 3) = 5 := byComputing
