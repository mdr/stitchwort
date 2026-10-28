-- Facts about the least of a list of numbers, which std doesn't have.

namespace Aoc.Year2024.Day16.Proofs
import Aoc.Year2024.Day16 (..)
import Std (And, Bool, DecEq, Eq, Exists, List, Map, Nat, Option, Or, Ord, Ordering, Set, Void)

-- `Ord.min` on numbers is at most either, and is one of them.
theorem ordMinBounds (x: Nat) (y: Nat): And (Ord.min x y ≤ x) (And (Ord.min x y ≤ y) (Or (Ord.min x y = x) (Ord.min x y = y))) :=
  match compared: Nat.compare x y with
    | Less => Both (Nat.leRefl x) (Both (Nat.leOfCompare x y (rewrite compared in Ordering.lessNotGreater)) (Inl rfl))
    | Equal => Both (Nat.leRefl x) (Both (Nat.leOfCompare x y (rewrite compared in Ordering.equalNotGreater)) (Inl rfl))
    | Greater =>
      let flipped: Nat.compare y x = Less := rewrite Nat.compareFlip x y, compared in rfl
      Both (Nat.lessLe y x (Nat.lessOfCompare y x flipped)) (Both (Nat.leRefl y) (Inr rfl))

-- Folding `Ord.min` gives at most the start and every member, and is one of
-- them.
theorem foldMinBounds: (xs: List Nat) → (start: Nat) →
    And (xs.foldLeft start Ord.min ≤ start)
      (And ((x: Nat) → x ∈ xs → xs.foldLeft start Ord.min ≤ x) (Or (xs.foldLeft start Ord.min = start) (xs.foldLeft start Ord.min ∈ xs)))
  | Nil, start => Both (Nat.leRefl start) (Both (x none => Void.exfalso none) (Inl rfl))
  | Cons first rest, start =>
    let (Both leStart (Both leFirst either)) := ordMinBounds start first
    let (Both below (Both belowAll isOne)) := foldMinBounds rest (Ord.min start first)
    Both (omega [below, leStart])
      (Both
        (x member =>
          match member with
            | Inl here => rewrite <- here in omega [below, leFirst]
            | Inr later => belowAll x later)
        (match isOne with
          | Inr inRest => Inr (Inr inRest)
          | Inl same =>
            match either with
              | Inl isStart => Inl (Eq.trans same isStart)
              | Inr isFirst => Inr (Inl (Eq.sym (Eq.trans same isFirst)))))

-- The least of a list is at most each member.
theorem minimumLeast: (xs: List Nat) → (least: Nat) → xs.minimum = Some least → (x: Nat) → x ∈ xs → least ≤ x
  | Nil, least, found, x, member => Void.exfalso member
  | Cons first rest, least, found, x, member =>
    let (Both leStart (Both leAll isOne)) := foldMinBounds rest first
    rewrite <- Option.someInjective _ _ found in
      match member with
        | Inl here => rewrite <- here in leStart
        | Inr later => leAll x later

-- The least of a list is on it.
theorem minimumMember: (xs: List Nat) → (least: Nat) → xs.minimum = Some least → least ∈ xs
  | Nil, least, found => Void.exfalso (Option.noneNotSome least found)
  | Cons first rest, least, found =>
    let (Both leStart (Both leAll isOne)) := foldMinBounds rest first
    rewrite <- Option.someInjective _ _ found in
      match isOne with
        | Inl isFirst => Inl (Eq.sym isFirst)
        | Inr inRest => Inr inRest

-- A list with a member has a least.
theorem minimumSome: (xs: List Nat) → (x: Nat) → x ∈ xs → Exists Nat (least => xs.minimum = Some least)
  | Nil, x, member => Void.exfalso member
  | Cons first rest, x, member => Witness (rest.foldLeft first Ord.min) rfl
