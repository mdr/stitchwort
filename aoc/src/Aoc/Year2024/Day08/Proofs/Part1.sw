--| Part 1: a point in line with `far` and `near`, with `far` twice as far
--| away, is past `near` or a third of the way from `near` to `far`
--| (`twiceAsFarCases`), which are the points `antinodesOf` gives
--| (`antinodesOfCorrect`).

namespace Aoc.Year2024.Day08.Proofs
import Aoc.Common (Offset, Position)
import Aoc.Common.Proofs (offsetOf, offsetSome)
import Aoc.Year2024.Day08 (..)
import Aoc.Year2024.Day08.Spec (..)
import Std (And, Bool, DecEq, Eq, Int, Iff, List, Nat, Option, Or, Set, Void)

--| With `u` the direction from the point to `far` and `v` to `near`: in line
--| (`u × v = 0`) with `|u|² = 4|v|²` means `u = 2v` or `u = -2v`.
--
-- By Lagrange's identity `(u·v)² + (u×v)² = |u|²|v|²`, `u·v` is `±2|v|²`,
-- and then `|u ∓ 2v|²` is 0.
theorem twiceAsFarCases ∀ (ur uc vr vc: Int)
    (cross: ur * vc - uc * vr = 0)
    (distance: ur * ur + uc * uc = 4 * (vr * vr + vc * vc)):
    ((ur = 2 * vr) ∧ (uc = 2 * vc)) ∨ ((ur = 0 - 2 * vr) ∧ (uc = 0 - 2 * vc)) :=
  let lagrange: (ur * vr + uc * vc) * (ur * vr + uc * vc) = (2 * (vr * vr + vc * vc)) * (2 * (vr * vr + vc * vc)) :=
    ring [(vr * vr + vc * vc) * distance, (ur * vc - uc * vr) * cross]
  match Int.squaresEq (ur * vr + uc * vc) (2 * (vr * vr + vc * vc)) lagrange with
    | Inl same =>
      let zero := Int.sumSquaresZero (ur - 2 * vr) (uc - 2 * vc) (ring [distance, 4 * same])
      Inl (Both (Int.subEqZero ur (2 * vr) (And.left zero)) (Int.subEqZero uc (2 * vc) (And.right zero)))
    | Inr opposite =>
      let zero := Int.sumSquaresZero (ur + 2 * vr) (uc + 2 * vc) (ring [distance, 4 * opposite])
      Inr (Both (ring [And.left zero]) (ring [And.right zero]))

--| And back: `u = ±2v` is in line, and twice as far.
theorem twiceAsFarOfCases ∀ (ur uc vr vc: Int)
    (choice: ((ur = 2 * vr) ∧ (uc = 2 * vc)) ∨ ((ur = 0 - 2 * vr) ∧ (uc = 0 - 2 * vc))):
    (ur * vc - uc * vr = 0) ∧ (ur * ur + uc * uc = 4 * (vr * vr + vc * vc)) :=
  match choice with
    | Inl (Both row column) => rewrite row, column in Both (ring) (ring)
    | Inr (Both row column) => rewrite row, column in Both (ring) (ring)

--| The two steps from `near` that `antinodesOf` can take.
def pastStep (far near: Position): Offset := near.minus far

def thirdStep (far near: Position): Offset := (divideBy (near.minus far) 3).negate

--| `antinodesOf`, written out.
theorem antinodesOfUnfold ∀ (far near: Position):
    antinodesOf far near
      = ((if (near.minus far).rows % 3 == 0 && (near.minus far).columns % 3 == 0 then
            [pastStep far near, thirdStep far near]
          else [pastStep far near]).filterMap near.offset) :=
  rfl

--| One coordinate at a time, with `far`, `near` and the point at `f`, `n`
--| and `p`. Past `near` is where `far` is twice as far in the same
--| direction...
theorem pastIff ∀ (f n p: Int): (p = n + (n - f)) ↔ (f - p = 2 * (n - p)) :=
  { forward = e => ring [e], backward = h => ring [h] }

--| ...and a third of the way from `near` to `far` (when that is a whole
--| number) is where it is twice as far in the other direction.
theorem thirdOf ∀ (f n p: Int) (h: f - p = 0 - 2 * (n - p)): ((n - f) % 3 = 0) ∧ (p = n + (0 - (n - f) / 3)) := omega

theorem thirdBack ∀ (f n p: Int) (multiple: (n - f) % 3 = 0) (e: p = n + (0 - (n - f) / 3)): f - p = 0 - 2 * (n - p) :=
  omega

--| The spec's test, as equations: `u = ±2v`.
theorem specCases ∀ (far near point: Position):
    ((inLine point far near && twiceAsFar point far near) = True)
      ↔ (((far.row.toInt - point.row.toInt = 2 * (near.row.toInt - point.row.toInt))
        ∧ (far.column.toInt - point.column.toInt = 2 * (near.column.toInt - point.column.toInt)))
        ∨ ((far.row.toInt - point.row.toInt = 0 - 2 * (near.row.toInt - point.row.toInt))
          ∧ (far.column.toInt - point.column.toInt = 0 - 2 * (near.column.toInt - point.column.toInt)))) :=
  let ur := far.row.toInt - point.row.toInt
  let uc := far.column.toInt - point.column.toInt
  let vr := near.row.toInt - point.row.toInt
  let vc := near.column.toInt - point.column.toInt
  {
    forward = h =>
      let Both inLineHolds twiceHolds := h
      twiceAsFarCases ur uc vr vc inLineHolds.read twiceHolds.read,
    backward = h =>
      let both := twiceAsFarOfCases ur uc vr vc h
      Both (rewrite And.left both in DecEq.refl 0) (rewrite And.right both in DecEq.refl (4 * (vr * vr + vc * vc)))
  }

--| The step past `near` reaches the points where `far` is twice as far in
--| the same direction...
theorem pastAt ∀ (far near point: Position):
    (near.offset (pastStep far near) = Some point)
      ↔ ((far.row.toInt - point.row.toInt = 2 * (near.row.toInt - point.row.toInt))
        ∧ (far.column.toInt - point.column.toInt = 2 * (near.column.toInt - point.column.toInt))) :=
  {
    forward = landed =>
      let both := offsetSome near (pastStep far near) point landed
      Both
        ((pastIff far.row.toInt near.row.toInt point.row.toInt).forward (And.left both))
        ((pastIff far.column.toInt near.column.toInt point.column.toInt).forward (And.right both)),
    backward = h =>
      offsetOf near
        (pastStep far near)
        point
        ((pastIff far.row.toInt near.row.toInt point.row.toInt).backward (And.left h))
        ((pastIff far.column.toInt near.column.toInt point.column.toInt).backward (And.right h))
  }

--| ...and the step a third of the way back, those where it is twice as far
--| in the other direction, when the third is whole.
theorem thirdAt ∀ (far near point: Position)
    (multiples: ((near.row.toInt - far.row.toInt) % 3 = 0) ∧ ((near.column.toInt - far.column.toInt) % 3 = 0)):
    (near.offset (thirdStep far near) = Some point)
      ↔ ((far.row.toInt - point.row.toInt = 0 - 2 * (near.row.toInt - point.row.toInt))
        ∧ (far.column.toInt - point.column.toInt = 0 - 2 * (near.column.toInt - point.column.toInt))) :=
  {
    forward = landed =>
      let both := offsetSome near (thirdStep far near) point landed
      Both
        (thirdBack far.row.toInt near.row.toInt point.row.toInt (And.left multiples) (And.left both))
        (thirdBack far.column.toInt near.column.toInt point.column.toInt (And.right multiples) (And.right both)),
    backward = h =>
      offsetOf near
        (thirdStep far near)
        point
        (And.right (thirdOf far.row.toInt near.row.toInt point.row.toInt (And.left h)))
        (And.right (thirdOf far.column.toInt near.column.toInt point.column.toInt (And.right h)))
  }

--| Twice as far in the other direction makes the third whole.
theorem thirdWhole ∀ (far near point: Position)
    (h: (far.row.toInt - point.row.toInt = 0 - 2 * (near.row.toInt - point.row.toInt))
      ∧ (far.column.toInt - point.column.toInt = 0 - 2 * (near.column.toInt - point.column.toInt))):
    ((near.row.toInt - far.row.toInt) % 3 = 0) ∧ ((near.column.toInt - far.column.toInt) % 3 = 0) :=
  Both
    (And.left (thirdOf far.row.toInt near.row.toInt point.row.toInt (And.left h)))
    (And.left (thirdOf far.column.toInt near.column.toInt point.column.toInt (And.right h)))

--| The program's two cases, with its test as a variable.
theorem antinodesIff ∀ (far near point: Position) (condition: Bool)
    (multiples: (condition = True)
      ↔ (((near.row.toInt - far.row.toInt) % 3 = 0) ∧ ((near.column.toInt - far.column.toInt) % 3 = 0))):
    (point ∈ (if condition then [pastStep far near, thirdStep far near] else [pastStep far near]).filterMap near.offset)
      ↔ ((inLine point far near && twiceAsFar point far near) = True) :=
  let spec := specCases far near point
  let past := pastAt far near point
  match condition with
    | True =>
      let third := thirdAt far near point (multiples.forward rfl)
      {
        forward = has =>
          match List.memFilterMapElim near.offset point [pastStep far near, thirdStep far near] has with
            | Inl e => spec.backward (Inl (past.forward e))
            | Inr (Inl e) => spec.backward (Inr (third.forward e))
            | Inr (Inr none) => Void.exfalso none,
        backward = h =>
          match spec.forward h with
            | Inl both =>
              List.memFilterMapIntro near.offset
                (pastStep far near)
                point
                [pastStep far near, thirdStep far near]
                (Inl rfl)
                (past.backward both)
            | Inr both =>
              List.memFilterMapIntro near.offset
                (thirdStep far near)
                point
                [pastStep far near, thirdStep far near]
                (Inr (Inl rfl))
                (third.backward both)
      }
    | False => {
      forward = has =>
        match List.memFilterMapElim near.offset point [pastStep far near] has with
          | Inl e => spec.backward (Inl (past.forward e))
          | Inr none => Void.exfalso none,
      backward = h =>
        match spec.forward h with
          | Inl both =>
            List.memFilterMapIntro near.offset
              (pastStep far near)
              point
              [pastStep far near]
              (Inl rfl)
              (past.backward both)
          | Inr both => Void.exfalso (Bool.falseNotTrue (multiples.backward (thirdWhole far near point both)))
    }

theorem antinodesOfCorrect ∀ (far near point: Position):
    (point ∈ antinodesOf far near) ↔ ((inLine point far near && twiceAsFar point far near) = True) :=
  rewrite antinodesOfUnfold far near in
    antinodesIff far near point _ {
      forward = c => Both c.left.read c.right.read,
      backward = m => Both (rewrite And.left m in rfl) (rewrite And.right m in rfl)
    }

--| Part 1 counts the puzzle's antinodes, for every city.
theorem part1Correct ∀ (city: City): solvePart1 city = part1 city :=
  Eq.cong Set.size
    (locationsCorrect city
      (((far, near)) => antinodesOf far near)
      (point far near => inLine point far near && twiceAsFar point far near)
      (first second firstIn secondIn same point inside => antinodesOfCorrect first.position second.position point))
