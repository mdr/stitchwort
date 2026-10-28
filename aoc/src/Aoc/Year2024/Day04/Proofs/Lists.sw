-- List lemmas the proofs share: a `drop` read by index, and a sum over lists
-- zipped in step as a sum over indices.

namespace Aoc.Year2024.Day04.Proofs
import Std (Bool, Char, DecEq, Decidable, Eq, List, Nat, Option, Void)

-- Index j after dropping k is index j + k before.
theorem getDrop: (xs: List a) → (k: Nat) → (j: Nat) → List.get (List.drop xs k) j = List.get xs (k + j)
  | xs, Zero, j => rfl
  | Nil, Succ k, j => rfl
  | Cons x xs, Succ k, j => getDrop xs k j

-- A letter can't be both `X` and `S`.
theorem notXAndS (ch: Char) (isX: (ch == 'X') = True) (isS: (ch == 'S') = True): Void :=
  let same := DecEq.sound ch 'X' isX
  Bool.falseNotTrue (rewrite same at isS in isS)

theorem decSomeToBool (x: a) (y: a): (d: Decidable (x = y)) → Decidable.toBool (Option.decSome x y d) = Decidable.toBool d
  | Yes p => rfl
  | No r => rfl

-- Optional letters are equal when the letters are.
theorem someEq (x: Char) (y: Char): (Some x == Some y) = (x == y) := decSomeToBool x y (Char.decEq x y)
