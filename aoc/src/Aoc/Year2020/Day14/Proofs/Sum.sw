--| The spec's sum of memory names one number: two lists of distinct
--| addresses that both include every address not holding 0 sum to the same.

namespace Aoc.Year2020.Day14.Proofs
import Aoc.Year2020.Day14 (Spec)
import Std (Bool, DecEq, Eq, List, Nat, Void)

theorem memOfRemoveFirst [auto eq: DecEq a]: (ys: List a) → (x: a) → (y: a) → y ∈ ys.removeFirst x → y ∈ ys
  | [], x, y, member => member
  | [first, ..ys], x, y, member =>
    match e: first == x with
      | True => Inr member
      | False =>
        match member with
          | Inl same => Inl same
          | Inr later => Inr (memOfRemoveFirst ys x y later)

theorem memRemoveFirst [auto eq: DecEq a]: (ys: List a) → (x: a) → (y: a) → y ≠ x → y ∈ ys → y ∈ ys.removeFirst x
  | [], x, y, apart, member => member
  | [first, ..ys], x, y, apart, member =>
    match e: first == x with
      | True =>
        match member with
          | Inl same => Void.exfalso (apart (Eq.trans (Eq.sym same) (DecEq.sound e)))
          | Inr later => later
      | False =>
        match member with
          | Inl same => Inl same
          | Inr later => Inr (memRemoveFirst ys x y apart later)

theorem distinctRemoveFirst [auto eq: DecEq a]: (ys: List a) → (x: a) → ys.Distinct → (ys.removeFirst x).Distinct ∧ x ∉ ys.removeFirst x
  | [], x, distinct => Both Trivial (member => member)
  | [first, ..ys], x, (Both fresh distinct) =>
    match e: first == x with
      | True => Both distinct (rewrite <- DecEq.sound e in fresh)
      | False =>
        match distinctRemoveFirst ys x distinct with
          | Both restDistinct absent =>
            Both (Both (member => fresh (memOfRemoveFirst ys x first member)) restDistinct)
              (member =>
                match member with
                  | Inl same => DecEq.soundFalse first x e same
                  | Inr later => absent later)

--| Two lists of distinct addresses holding the same addresses that don't
--| hold 0 sum to the same.
theorem sumsAgree (memory: Spec.Memory): (xs: List Nat) → (ys: List Nat) → xs.Distinct → ys.Distinct →
    ((address: Nat) → memory address ≠ 0 → address ∈ xs → address ∈ ys) → ((address: Nat) → memory address ≠ 0 → address ∈ ys → address ∈ xs) →
      xs.sumBy memory = ys.sumBy memory
  | [], ys, distinctX, distinctY, there, back =>
    Eq.sym
      (List.sumByZeroIntro ys memory
        (address member =>
          match zero: memory address with
            | 0 => rfl
            | Succ more => Void.exfalso (back address (rewrite zero in Nat.succNotZero more) member)))
  | [x, ..rest], ys, (Both fresh distinctRest), distinctY, there, back =>
    rewrite List.sumByCons rest x memory in
      match zero: memory x with
        | 0 =>
          sumsAgree memory rest ys distinctRest distinctY (address nonzero member => there address nonzero (Inr member))
            (address nonzero member =>
              match back address nonzero member with
                | Inl same => Void.exfalso (nonzero (rewrite <- same in zero))
                | Inr later => later)
        | Succ more =>
          let nonzero: memory x ≠ 0 := rewrite zero in Nat.succNotZero more
          let found := there x nonzero (Inl rfl)
          match distinctRemoveFirst ys x distinctY with
            | Both restDistinct absent =>
              rewrite List.sumByRemoveFirst ys x found memory, zero in
                Eq.cong (total => Succ more + total)
                  (sumsAgree memory rest (ys.removeFirst x) distinctRest restDistinct
                    (address nonzero member =>
                      memRemoveFirst ys x address (same => fresh (rewrite same at member in member)) (there address nonzero (Inr member)))
                    (address nonzero member =>
                      match back address nonzero (memOfRemoveFirst ys x address member) with
                        | Inl same => Void.exfalso (absent (rewrite <- same at member in member))
                        | Inr later => later))

theorem sumOfMemoryUnique (memory: Spec.Memory) (first: Nat) (second: Nat) (isFirst: Spec.SumOfMemory memory first)
    (isSecond: Spec.SumOfMemory memory second): first = second :=
  match isFirst with
    | Witness xs (Both distinctX (Both coversX sumX)) =>
      match isSecond with
        | Witness ys (Both distinctY (Both coversY sumY)) =>
          rewrite sumX, sumY in
            sumsAgree memory xs ys distinctX distinctY (address nonzero member => coversY address nonzero)
              (address nonzero member => coversX address nonzero)
