-- Interfaces in generated JS (docs/proposals/interfaces.md §10): a
-- dictionary is a record, so a plain object, passed as an argument to
-- generic code; its laws are proofs, erased. Exports are at concrete types,
-- so no dictionary crosses the boundary.
--
-- run: describeAll [1, 2, 3]
-- run: describeNested [[1], [], [2, 3]]
-- run: smallest [5, 3, 8]
-- run: smallestBy [5, 3, 8]

import Std (Nat, Text)

interface Pretty (a: Type) =
  { pretty: a → Text }

instance Pretty.instNat: Pretty Nat :=
  { pretty = n => if n == 0 then "zero" else "some" }

instance Pretty.instList [auto p: Pretty a]: Pretty (List a) :=
  { pretty = xs => "[" ++ Text.join (xs.map Pretty.pretty) ',' ++ "]" }

-- With a law, which is erased.
interface Ordered (a: Type) = {
  less: a → a → Bool,
  irreflexive: (x: a) → less x x = False
}

theorem lessIrreflexive: (x: Nat) → Nat.leq (x + 1) x = False
  | Zero => rfl
  | Succ k => lessIrreflexive k

instance Ordered.instNat: Ordered Nat :=
  { less = m n => Nat.leq (m + 1) n, irreflexive = lessIrreflexive }

def smallestOf [auto o: Ordered a] (first: a): List a → a
  | Nil => first
  | Cons x xs => if Ordered.less x first then smallestOf x xs else smallestOf first xs

def flipped: Ordered Nat := { less = m n => Nat.leq (n + 1) m, irreflexive = lessIrreflexive }

export def describeAll (xs: List Nat): Text := Pretty.pretty xs

export def describeNested (xs: List (List Nat)): Text := Pretty.pretty xs

export def smallest (xs: List Nat): Nat := smallestOf 1000 xs

export def smallestBy (xs: List Nat): Nat := smallestOf [o := flipped] 0 xs
