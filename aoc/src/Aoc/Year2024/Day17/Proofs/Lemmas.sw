-- Facts the part 2 proofs need about lists of numbers: what `filter` keeps,
-- and that `List.minimum` is in the list and at most each element.

namespace Aoc.Year2024.Day17.Proofs
import Std (And, Bool, Eq, Exists, List, Nat, Option, Or, Ord, Ordering, Void)

-- `filter` keeps an element that passes.
theorem memFilterIntro (p: a → Bool): (xs: List a) → (x: a) → x ∈ xs → p x = True → x ∈ List.filter xs p
  | Nil, x, member, passes => member
  | Cons y ys, x, Inl same, passes => rewrite Eq.sym same at passes in rewrite List.filterKeep ys p y passes in Inl same
  | Cons y ys, x, Inr member, passes =>
    match kept: p y with
      | True => Inr (memFilterIntro p ys x member passes)
      | False => memFilterIntro p ys x member passes

-- The smaller of two numbers is at most each, and is one of them.
theorem minLeLeft (x: Nat) (y: Nat): Ord.min x y ≤ x :=
  match order: Nat.compare x y with
    | Greater =>
      let flipped: Nat.compare y x = Less := rewrite order at Nat.compareFlip x y
      Nat.leOfCompare y x (greater => Ordering.lessNotGreater (Eq.trans (Eq.sym flipped) greater))
    | Less => Nat.leRefl x
    | Equal => Nat.leRefl x

theorem minLeRight (x: Nat) (y: Nat): Ord.min x y ≤ y :=
  match order: Nat.compare x y with
    | Greater => Nat.leRefl y
    | Less => Nat.leOfCompare x y (greater => Ordering.lessNotGreater (Eq.trans (Eq.sym order) greater))
    | Equal => Nat.leOfCompare x y (greater => Ordering.equalNotGreater (Eq.trans (Eq.sym order) greater))

theorem minEither (x: Nat) (y: Nat): Or (Ord.min x y = x) (Ord.min x y = y) :=
  match order: Nat.compare x y with
    | Greater => Inr rfl
    | Less => Inl rfl
    | Equal => Inl rfl

-- Folding with `Ord.min` gives at most the start and each element, and
-- gives the start or an element.
theorem foldMinLeStart: (xs: List Nat) → (start: Nat) → List.foldLeft xs start Ord.min ≤ start
  | Nil, start => Nat.leRefl start
  | Cons y ys, start =>
    Nat.leTrans (List.foldLeft ys (Ord.min start y) Ord.min) (Ord.min start y) start (foldMinLeStart ys (Ord.min start y)) (minLeLeft start y)

theorem foldMinLeMember: (xs: List Nat) → (start: Nat) → (x: Nat) → x ∈ xs → List.foldLeft xs start Ord.min ≤ x
  | Nil, start, x, member => Void.exfalso member
  | Cons y ys, start, x, Inl same =>
    rewrite Eq.sym same in
      Nat.leTrans (List.foldLeft ys (Ord.min start y) Ord.min) (Ord.min start y) y (foldMinLeStart ys (Ord.min start y)) (minLeRight start y)
  | Cons y ys, start, x, Inr member => foldMinLeMember ys (Ord.min start y) x member

theorem foldMinMember: (xs: List Nat) → (start: Nat) → Or (List.foldLeft xs start Ord.min = start) (List.foldLeft xs start Ord.min ∈ xs)
  | Nil, start => Inl rfl
  | Cons y ys, start =>
    match foldMinMember ys (Ord.min start y) with
      | Inr member => Inr (Inr member)
      | Inl same =>
        match minEither start y with
          | Inl isStart => Inl (Eq.trans same isStart)
          | Inr isY => Inr (Inl (Eq.sym (Eq.trans same isY)))

-- The least element is in the list and at most every element.
theorem minimumSome (xs: List Nat) (least: Nat) (found: List.minimum xs = Some least): And (least ∈ xs) ((x: Nat) → x ∈ xs → least ≤ x) :=
  match xs with
    | Nil => Void.exfalso (Option.noneNotSome least found)
    | Cons y ys =>
      let same := Option.someInjective (List.foldLeft ys y Ord.min) least found
      Both
        (match foldMinMember ys y with
          | Inl isY => Inl (Eq.sym (Eq.trans (Eq.sym same) isY))
          | Inr member => Inr (rewrite same at member))
        (x member =>
          rewrite Eq.sym same in
            match member with
              | Inl isY => rewrite Eq.sym isY in foldMinLeStart ys y
              | Inr inRest => foldMinLeMember ys y x inRest)

-- A list with an element has a least one.
theorem minimumExists: (xs: List Nat) → (x: Nat) → x ∈ xs → ∃ (least: Nat) => List.minimum xs = Some least
  | Nil, x, member => Void.exfalso member
  | Cons y ys, x, member => Witness (List.foldLeft ys y Ord.min) rfl
