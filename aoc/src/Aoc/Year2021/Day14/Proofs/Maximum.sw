-- `List.maximum` of numbers: in the list and at least every member (std
-- has this for `List.minimum` only), and lists with the same members have
-- the same greatest and least.

namespace Aoc.Year2021.Day14.Proofs
import Std (Eq, Exists, List, Nat, Option, Ord, Void)

-- `Ord.max` of two numbers is one of them, and at least the other.
theorem maxCases (x: Nat) (y: Nat): (Ord.max x y = x ∧ y ≤ x) ∨ (Ord.max x y = y ∧ x ≤ y) :=
  cases

theorem foldMaxGeStart: (xs: List Nat) → (start: Nat) → start ≤ List.foldLeft xs start Ord.max
  | Nil, start => omega
  | Cons y ys, start =>
    let later := foldMaxGeStart ys (Ord.max start y)
    match maxCases start y with
      | Inl (Both same _) => omega
      | Inr (Both same _) => omega

theorem foldMaxGeMember: (xs: List Nat) → (start: Nat) → (x: Nat) → x ∈ xs → x ≤ List.foldLeft xs start Ord.max
  | Nil, start, x, member => Void.exfalso member
  | Cons y ys, start, x, Inl same =>
    let later := foldMaxGeStart ys (Ord.max start y)
    match maxCases start y with
      | Inl (Both is _) => omega
      | Inr (Both is _) => omega
  | Cons y ys, start, x, Inr member => foldMaxGeMember ys (Ord.max start y) x member

theorem foldMaxMember: (xs: List Nat) → (start: Nat) → (List.foldLeft xs start Ord.max = start) ∨ (List.foldLeft xs start Ord.max ∈ xs)
  | Nil, start => Inl rfl
  | Cons y ys, start =>
    match foldMaxMember ys (Ord.max start y) with
      | Inr member => Inr (Inr member)
      | Inl same =>
        match maxCases start y with
          | Inl (Both isStart _) => Inl (Eq.trans same isStart)
          | Inr (Both isY _) => Inr (Inl (Eq.sym (Eq.trans same isY)))

-- The greatest number is in the list and at least every member.
theorem maximumSome (xs: List Nat) (most: Nat) (found: List.maximum xs = Some most): (most ∈ xs) ∧ ((x: Nat) → x ∈ xs → x ≤ most) :=
  match xs with
    | Nil => Void.exfalso (Option.noneNotSome most found)
    | Cons y ys =>
      let same := Option.someInjective (List.foldLeft ys y Ord.max) most found
      Both
        (match foldMaxMember ys y with
          | Inl isY => Inl (Eq.sym (Eq.trans (Eq.sym same) isY))
          | Inr member => Inr (rewrite same at member in member))
        (x member =>
          rewrite Eq.sym same in
            match member with
              | Inl isY => rewrite Eq.sym isY in foldMaxGeStart ys y
              | Inr inRest => foldMaxGeMember ys y x inRest)

-- A list with a member has a greatest and a least.
theorem maximumNone [auto ord: Ord a] (xs: List a) (none: List.maximum xs = None) (x: a) (member: x ∈ xs): Void :=
  match xs with
    | Nil => member
    | Cons y ys => Option.someNotNone (List.foldLeft ys y Ord.max) none

theorem minimumNone [auto ord: Ord a] (xs: List a) (none: List.minimum xs = None) (x: a) (member: x ∈ xs): Void :=
  match xs with
    | Nil => member
    | Cons y ys => Option.someNotNone (List.foldLeft ys y Ord.min) none

-- Lists with the same members have the same greatest member...
theorem maximumSame (xs: List Nat) (ys: List Nat) (into: (v: Nat) → v ∈ xs → v ∈ ys) (back: (v: Nat) → v ∈ ys → v ∈ xs): List.maximum xs = List.maximum ys :=
  match mx: List.maximum xs with
    | None =>
      match my: List.maximum ys with
        | None => rfl
        | Some y => Void.exfalso (maximumNone xs mx y (back y (maximumSome ys y my).left))
    | Some x =>
      match my: List.maximum ys with
        | None => Void.exfalso (maximumNone ys my x (into x (maximumSome xs x mx).left))
        | Some y =>
          let (Both xIn xMost) := maximumSome xs x mx
          let (Both yIn yMost) := maximumSome ys y my
          let below := xMost y (back y yIn)
          let above := yMost x (into x xIn)
          Eq.cong Some (omega: x = y)

-- ...and the same least.
theorem minimumSame (xs: List Nat) (ys: List Nat) (into: (v: Nat) → v ∈ xs → v ∈ ys) (back: (v: Nat) → v ∈ ys → v ∈ xs): List.minimum xs = List.minimum ys :=
  match mx: List.minimum xs with
    | None =>
      match my: List.minimum ys with
        | None => rfl
        | Some y => Void.exfalso (minimumNone xs mx y (back y (List.minimumSome ys y my).left))
    | Some x =>
      match my: List.minimum ys with
        | None => Void.exfalso (minimumNone ys my x (into x (List.minimumSome xs x mx).left))
        | Some y =>
          let (Both xIn xLeast) := List.minimumSome xs x mx
          let (Both yIn yLeast) := List.minimumSome ys y my
          let below := xLeast y (back y yIn)
          let above := yLeast x (into x xIn)
          Eq.cong Some (omega: x = y)
