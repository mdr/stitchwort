-- `omega` reads a fact whose `≤` comes from `Ord`, at `Nat` and `Int`, as the
-- native comparison: from scope, or given in brackets.

import Std (Nat, Int, List, NonEmptyList)

theorem fromScope ∀ (xs: NonEmptyList Nat) (x: Nat) (m: NonEmptyList.Mem x xs) (k: Nat)
    (h: xs.maximum ≤ k): x ≤ k :=
  let le := NonEmptyList.maximumLe xs x m
  omega

theorem inBrackets ∀ (xs: NonEmptyList Nat) (x: Nat) (m: NonEmptyList.Mem x xs) (k: Nat)
    (h: xs.maximum ≤ k): x ≤ k :=
  omega [NonEmptyList.maximumLe xs x m]

theorem onInt ∀ (xs: NonEmptyList Int) (x: Int) (m: NonEmptyList.Mem x xs) (k: Int)
    (h: xs.maximum ≤ k): x ≤ k :=
  omega [NonEmptyList.maximumLe xs x m]
