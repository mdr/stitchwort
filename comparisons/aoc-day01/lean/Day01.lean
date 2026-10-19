/-
Advent of Code 2025, day 1, in Lean 4 (core only, no Mathlib), mirroring
Stitchwort's aoc/src/day01/day01.sw: a dial numbered 0 to `highest` is turned left or
right. Part 1 counts the turns that end on 0; part 2 counts every click that
lands on 0. The theorem `zerosPassedCorrect` says part 2's arithmetic count
equals turning the dial one click at a time, for any dial, start and turns.

  lean Day01.lean            -- check, and print the example's answers
-/

-- Definitions ---------------------------------------------------------------

inductive Turn where
  | left (distance : Nat)
  | right (distance : Nat)

-- "L68" is `left 68`.
-- (Digits by hand: `String.toNat?` doesn't reduce in the kernel, so `decide`
-- couldn't check the example below.)
def natOfDigits : List Char → Option Nat
  | [] => none
  | cs => cs.foldl (fun acc c => acc.bind fun n =>
      if c.isDigit then some (10 * n + (c.toNat - '0'.toNat)) else none) (some 0)

def Turn.parse (t : String) : Option Turn :=
  match t.toList with
  | 'L' :: rest => (natOfDigits rest).map .left
  | 'R' :: rest => (natOfDigits rest).map .right
  | _ => none

-- A turn, one click at a time: `left 3` is three `left 1`s.
def Turn.clicks : Turn → List Turn
  | .left n  => List.replicate n (.left 1)
  | .right n => List.replicate n (.right 1)

-- A dial numbered 0 to `highest`, at `position`.
@[ext] structure Dial (highest : Nat) where
  position : Nat
  inRange : position ≤ highest

namespace Dial

def size (_ : Dial highest) : Nat := highest + 1

-- Any integer, wrapped onto the dial.
def fromInt (highest : Nat) (x : Int) : Dial highest where
  position := (x % (highest + 1 : Nat)).toNat
  inRange := by
    have := Int.emod_nonneg x (b := ((highest + 1 : Nat) : Int)) (by omega)
    have := Int.emod_lt_of_pos x (b := ((highest + 1 : Nat) : Int)) (by omega)
    omega

-- Where a turn leaves the dial.
def move (d : Dial highest) : Turn → Dial highest
  | .left n  => fromInt highest (d.position - n)
  | .right n => fromInt highest (d.position + n)

def isZero (d : Dial highest) : Bool := d.position == 0

-- How many clicks of a turn land on 0.
def zerosDuring (d : Dial highest) : Turn → Nat
  | .right n => (d.position + n) / d.size
  | .left n  => ((d.size - d.position) % d.size + n) / d.size

end Dial

-- Part 1: the positions after each turn that are 0.
def zerosLandedOn (start : Dial highest) (turns : List Turn) : Nat :=
  ((turns.scanl Dial.move start).drop 1).countP Dial.isZero

-- Part 2: for each turn, the clicks onto 0 from where the dial was before it.
def zerosPassed (start : Dial highest) (turns : List Turn) : Nat :=
  (List.zipWith Dial.zerosDuring (turns.scanl Dial.move start) turns).sum

-- The specification of part 2: count the zeros click by click.
def zerosPassedSpec (start : Dial highest) (turns : List Turn) : Nat :=
  zerosLandedOn start (turns.flatMap Turn.clicks)

def dial : Dial 99 := ⟨50, by decide⟩

def solvePart1 (turns : List Turn) : Nat := zerosLandedOn dial turns
def solvePart2 (turns : List Turn) : Nat := zerosPassed dial turns

def example1 : List String := ["L68", "L30", "R48", "L5", "R60", "L55", "L1", "L99", "R14", "L82"]
def parseTurns (lines : List String) : List Turn := lines.filterMap Turn.parse

#eval (solvePart1 (parseTurns example1), solvePart2 (parseTurns example1))  -- (3, 6)
example : (solvePart1 (parseTurns example1), solvePart2 (parseTurns example1)) = (3, 6) := by decide +kernel
example : zerosPassedSpec dial (parseTurns example1) = 6 := by decide +kernel

-- Proofs --------------------------------------------------------------------

namespace Dial
variable {highest : Nat}

-- Arithmetic facts (Nat), each closed by case analysis plus library lemmas.
theorem stepRight (s a n : Nat) (h : a < s) :
    (if (a + 1) % s = 0 then 1 else 0) + ((a + 1) % s + n) / s = (a + (n + 1)) / s := by
  by_cases e : a + 1 = s
  · subst e
    simp [Nat.mod_self, show a + (n + 1) = (a + 1) + n by omega, Nat.add_div_left n (Nat.succ_pos a)]
    omega
  · rw [Nat.mod_eq_of_lt (by omega : a + 1 < s)]
    simp [show a + 1 + n = a + (n + 1) by omega]

theorem stepLeft (h a p n : Nat) (ha : a ≤ h) (hp : p = if a = 0 then h else a - 1) :
    (if p = 0 then 1 else 0) + ((h + 1 - p) % (h + 1) + n) / (h + 1)
      = ((h + 1 - a) % (h + 1) + (n + 1)) / (h + 1) := by
  subst hp
  rcases a with _ | m
  · rcases h with _ | h
    · simp; omega
    · simp [Nat.mod_self, show h + 1 + 1 - (h + 1) = 1 by omega,
        Nat.mod_eq_of_lt (show 1 < h + 1 + 1 by omega)]
      grind
  · simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
    rcases m with _ | m
    · simp [Nat.mod_self, Nat.mod_eq_of_lt (show h < h + 1 by omega),
        show h + (n + 1) = (h + 1) + n by omega, Nat.add_div_left n (Nat.succ_pos h)]
      omega
    · rw [Nat.mod_eq_of_lt (show h + 1 - (m + 1) < h + 1 by omega),
        Nat.mod_eq_of_lt (show h + 1 - (m + 1 + 1) < h + 1 by omega)]
      simp; congr 1; omega

-- Positions after one click.
theorem moveRightOne (d : Dial highest) :
    (d.move (.right 1)).position = (d.position + 1) % (highest + 1) := by
  simp only [move, fromInt]; norm_cast

theorem moveLeftOne (d : Dial highest) :
    (d.move (.left 1)).position = if d.position = 0 then highest else d.position - 1 := by
  have := d.inRange
  simp only [move, fromInt]
  by_cases h : d.position = 0
  · have e : (d.position : Int) - ((1 : Nat) : Int) = (highest : Int) + ((highest + 1 : Nat) : Int) * (-1) := by
      omega
    rw [e, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
    simp [h]
  · rw [Int.emod_eq_of_lt (by omega) (by omega)]; simp [h]

-- `zerosAfter d ts`: the zeros after each of `ts`, from `d`.
def zerosAfter (d : Dial highest) (ts : List Turn) : Nat :=
  ((ts.scanl move d).drop 1).countP isZero

theorem zerosAfterCons (d : Dial highest) (t : Turn) (ts : List Turn) :
    zerosAfter d (t :: ts) = (if (d.move t).position = 0 then 1 else 0) + zerosAfter (d.move t) ts := by
  cases ts <;> simp [zerosAfter, List.scanl_cons, List.countP_cons, isZero] <;> omega

theorem zerosAfterAppend (d : Dial highest) (l₁ l₂ : List Turn) :
    zerosAfter d (l₁ ++ l₂) = zerosAfter d l₁ + zerosAfter (l₁.foldl move d) l₂ := by
  simp [zerosAfter, List.scanl_append, List.tail_append_of_ne_nil, List.countP_append]

-- One whole turn, click by click.
theorem rightAt (d : Dial highest) (n : Nat) :
    ((List.replicate n (Turn.right 1)).foldl move d).position = (d.position + n) % (highest + 1) := by
  induction n generalizing d with
  | zero => simp [Nat.mod_eq_of_lt (Nat.lt_succ_of_le d.inRange)]
  | succ n ih => rw [List.replicate_succ, List.foldl_cons, ih, moveRightOne, Nat.mod_add_mod]; congr 1; omega

theorem leftAt (d : Dial highest) (n : Nat) :
    ((List.replicate n (Turn.left 1)).foldl move d).position = (move d (.left n)).position := by
  induction n generalizing d with
  | zero => simp [move, fromInt]; rw [Int.emod_eq_of_lt (by omega) (by have := d.inRange; omega)]; simp
  | succ n ih =>
    rw [List.replicate_succ, List.foldl_cons, ih]
    simp only [move, fromInt]
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega)), Int.sub_emod, Int.emod_emod,
      ← Int.sub_emod]
    congr 2; omega

theorem rightCount (d : Dial highest) (n : Nat) :
    zerosAfter d (List.replicate n (Turn.right 1)) = (d.position + n) / (highest + 1) := by
  induction n generalizing d with
  | zero => simp [zerosAfter, Nat.div_eq_of_lt (Nat.lt_succ_of_le d.inRange)]
  | succ n ih =>
    rw [List.replicate_succ, zerosAfterCons, ih, moveRightOne]
    exact stepRight _ _ _ (Nat.lt_succ_of_le d.inRange)

theorem leftCount (d : Dial highest) (n : Nat) :
    zerosAfter d (List.replicate n (Turn.left 1)) = d.zerosDuring (.left n) := by
  induction n generalizing d with
  | zero => simp [zerosAfter, zerosDuring, size, Nat.div_eq_of_lt (Nat.mod_lt _ (Nat.succ_pos highest))]
  | succ n ih =>
    rw [List.replicate_succ, zerosAfterCons, ih]
    exact stepLeft _ _ _ _ d.inRange (moveLeftOne d)

theorem turnAt (d : Dial highest) (t : Turn) : t.clicks.foldl move d = d.move t := by
  cases t with
  | left n => ext; exact leftAt d n
  | right n => ext; simp only [Turn.clicks]; rw [rightAt]; simp only [move, fromInt]; norm_cast

theorem turnCount (d : Dial highest) (t : Turn) : zerosAfter d t.clicks = d.zerosDuring t := by
  cases t with
  | left n => exact leftCount d n
  | right n => exact rightCount d n

end Dial

open Dial in
theorem zerosPassedFrom (d : Dial highest) (ts : List Turn) :
    zerosPassed d ts = zerosAfter d (ts.flatMap Turn.clicks) := by
  induction ts generalizing d with
  | nil => rfl
  | cons t ts ih =>
    rw [List.flatMap_cons, zerosAfterAppend, turnCount, turnAt, ← ih]
    simp [zerosPassed, List.scanl_cons]

-- The arithmetic count is the click-by-click count, for any dial, start and turns.
theorem zerosPassedCorrect (start : Dial highest) (turns : List Turn) :
    zerosPassed start turns = zerosPassedSpec start turns :=
  zerosPassedFrom start turns

theorem part2Puzzle (turns : List Turn) : solvePart2 turns = zerosPassedSpec dial turns :=
  zerosPassedCorrect dial turns
