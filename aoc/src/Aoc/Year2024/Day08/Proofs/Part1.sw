-- Part 1: a point in line with `far` and `near`, with `far` twice as far
-- away, is past `near` or a third of the way from `near` to `far`
-- (`twiceAsFarCases`), which are the points `antinodesOf` gives
-- (`antinodesOfCorrect`).

namespace Aoc.Year2024.Day08.Proofs
import Aoc.Year2024.Day08 (..)
import Aoc.Year2024.Day08.Spec (..)
import Std (And, Bool, DecEq, Eq, Int, Iff, Nat, Or, Set, Void)

-- With `u` the direction from the point to `far` and `v` to `near`: in line
-- (`u × v = 0`) with `|u|² = 4|v|²` means `u = 2v` or `u = -2v`. By
-- Lagrange's identity `(u·v)² + (u×v)² = |u|²|v|²`, `u·v` is `±2|v|²`, and
-- then `|u ∓ 2v|²` is 0.
theorem twiceAsFarCases (ur: Int) (uc: Int) (vr: Int) (vc: Int) (cross: ur * vc - uc * vr = 0)
    (distance: ur * ur + uc * uc = 4 * (vr * vr + vc * vc)):
    Or (And (ur = 2 * vr) (uc = 2 * vc)) (And (ur = 0 - 2 * vr) (uc = 0 - 2 * vc)) :=
  let crossSquared: 0 = (ur * vc - uc * vr) * (ur * vc - uc * vr) := rewrite cross in rfl
  let distanceScaled := Eq.cong (x => x * (vr * vr + vc * vc)) distance
  let lagrange: (ur * vr + uc * vc) * (ur * vr + uc * vc) = (2 * (vr * vr + vc * vc)) * (2 * (vr * vr + vc * vc)) :=
    ring [distanceScaled, crossSquared]
  match squaresEq (ur * vr + uc * vc) (2 * (vr * vr + vc * vc)) lagrange with
    | Inl same =>
      let zero := sumSquaresZero (ur - 2 * vr) (uc - 2 * vc) (ring [distance, Eq.cong ((x: Int) => 4 * x) (Eq.sym same)])
      Inl (Both (subEqZero ur (2 * vr) (And.left zero)) (subEqZero uc (2 * vc) (And.right zero)))
    | Inr opposite =>
      let zero := sumSquaresZero (ur + 2 * vr) (uc + 2 * vc) (ring [distance, Eq.cong ((x: Int) => 4 * x) opposite])
      Inr (Both (ring [And.left zero]) (ring [And.right zero]))

-- And back: `u = ±2v` is in line, and twice as far.
theorem twiceAsFarOfCases (ur: Int) (uc: Int) (vr: Int) (vc: Int)
    (choice: Or (And (ur = 2 * vr) (uc = 2 * vc)) (And (ur = 0 - 2 * vr) (uc = 0 - 2 * vc))):
    And (ur * vc - uc * vr = 0) (ur * ur + uc * uc = 4 * (vr * vr + vc * vc)) :=
  match choice with
    | Inl (Both row column) => rewrite row, column in Both (ring) (ring)
    | Inr (Both row column) => rewrite row, column in Both (ring) (ring)

-- The two points `antinodesOf` can give.
def pastPoint (far: Position) (near: Position): Position := { row = near.row + (near.row - far.row), column = near.column + (near.column - far.column) }

def thirdPoint (far: Position) (near: Position): Position :=
  { row = near.row - (near.row - far.row) / 3, column = near.column - (near.column - far.column) / 3 }

-- `antinodesOf`, written out.
theorem antinodesOfUnfold (far: Position) (near: Position):
    antinodesOf far near =
      (if (near.row - far.row) % 3 == 0 && (near.column - far.column) % 3 == 0 then [pastPoint far near, thirdPoint far near]
      else [pastPoint far near]) :=
  rfl

-- Positions with the same row and column are the same.
theorem positionEq: (first: Position) → (second: Position) → first.row = second.row → first.column = second.column → first = second
  | { row, column }, { row = otherRow, column = otherColumn }, rows, columns => rewrite rows, columns in rfl

-- One coordinate at a time, with `far`, `near` and the point at `f`, `n`
-- and `p`. Past `near` is where `far` is twice as far in the same
-- direction...
theorem pastIff (f: Int) (n: Int) (p: Int): Iff (n + (n - f) = p) (f - p = 2 * (n - p)) := {
  forward = e => ring [Eq.sym e],
  backward = h => ring [Eq.sym h]
}

-- ...and a third of the way from `near` to `far` (when that is a whole
-- number) is where it is twice as far in the other direction.
theorem thirdOf (f: Int) (n: Int) (p: Int) (h: f - p = 0 - 2 * (n - p)): And ((n - f) % 3 = 0) (n - (n - f) / 3 = p) := omega

theorem thirdBack (f: Int) (n: Int) (p: Int) (multiple: (n - f) % 3 = 0) (e: n - (n - f) / 3 = p): f - p = 0 - 2 * (n - p) := omega

-- The spec's test, as equations: `u = ±2v`.
theorem specCases (far: Position) (near: Position) (point: Position):
    Iff ((inLine point far near && twiceAsFar point far near) = True)
      (Or (And (far.row - point.row = 2 * (near.row - point.row)) (far.column - point.column = 2 * (near.column - point.column)))
        (And (far.row - point.row = 0 - 2 * (near.row - point.row)) (far.column - point.column = 0 - 2 * (near.column - point.column)))) :=
  let ur := far.row - point.row
  let uc := far.column - point.column
  let vr := near.row - point.row
  let vc := near.column - point.column
  {
    forward = h =>
      twiceAsFarCases ur uc vr vc (DecEq.sound _ _ (Bool.andLeft _ _ h)) (DecEq.sound _ _ (Bool.andRight _ _ h)),
    backward = h =>
      let both := twiceAsFarOfCases ur uc vr vc h
      Bool.andIntro _ _ (rewrite And.left both in DecEq.refl 0) (rewrite And.right both in DecEq.refl (4 * (vr * vr + vc * vc)))
  }

-- The program's two cases, with its test as a variable.
theorem antinodesIff (far: Position) (near: Position) (point: Position) (condition: Bool)
    (multiples: Iff (condition = True) (And ((near.row - far.row) % 3 = 0) ((near.column - far.column) % 3 = 0))):
    Iff (point ∈ (if condition then [pastPoint far near, thirdPoint far near] else [pastPoint far near]))
      ((inLine point far near && twiceAsFar point far near) = True) :=
  let spec := specCases far near point
  let past := (e: pastPoint far near = point) =>
    Both ((pastIff far.row near.row point.row).forward (Eq.cong Position.row e))
      ((pastIff far.column near.column point.column).forward (Eq.cong Position.column e))
  let toPast := (row: far.row - point.row = 2 * (near.row - point.row)) (column: far.column - point.column = 2 * (near.column - point.column)) =>
    positionEq (pastPoint far near) point ((pastIff far.row near.row point.row).backward row)
      ((pastIff far.column near.column point.column).backward column)
  match condition with
    | True =>
      let facts := multiples.forward rfl
      {
        forward = has =>
          match has with
            | Inl e => spec.backward (Inl (past e))
            | Inr (Inl e) =>
              spec.backward
                (Inr
                  (Both (thirdBack far.row near.row point.row (And.left facts) (Eq.cong Position.row e))
                    (thirdBack far.column near.column point.column (And.right facts) (Eq.cong Position.column e))))
            | Inr (Inr none) => Void.exfalso none,
        backward = h =>
          match spec.forward h with
            | Inl (Both row column) => Inl (toPast row column)
            | Inr (Both row column) =>
              Inr
                (Inl
                  (positionEq (thirdPoint far near) point (And.right (thirdOf far.row near.row point.row row))
                    (And.right (thirdOf far.column near.column point.column column))))
      }
    | False => {
      forward = has =>
        match has with
          | Inl e => spec.backward (Inl (past e))
          | Inr none => Void.exfalso none,
      backward = h =>
        match spec.forward h with
          | Inl (Both row column) => Inl (toPast row column)
          | Inr (Both row column) =>
            Void.exfalso
              (Bool.falseNotTrue
                (multiples.backward
                  (Both (And.left (thirdOf far.row near.row point.row row)) (And.left (thirdOf far.column near.column point.column column)))))
    }

theorem antinodesOfCorrect (far: Position) (near: Position) (point: Position):
    Iff (point ∈ antinodesOf far near) ((inLine point far near && twiceAsFar point far near) = True) :=
  rewrite antinodesOfUnfold far near in
  antinodesIff far near point _ {
    forward = c => Both (DecEq.sound _ _ (Bool.andLeft _ _ c)) (DecEq.sound _ _ (Bool.andRight _ _ c)),
    backward = m => Bool.andIntro _ _ (rewrite And.left m in rfl) (rewrite And.right m in rfl)
  }

-- Part 1 counts the puzzle's antinodes, for every city.
theorem part1Correct (city: City): solvePart1 city = part1 city :=
  Eq.cong Set.size
    (locationsCorrect city (((far, near)) => antinodesOf far near) (point far near => inLine point far near && twiceAsFar point far near)
      (first second firstIn secondIn same point inside => antinodesOfCorrect first.position second.position point))
