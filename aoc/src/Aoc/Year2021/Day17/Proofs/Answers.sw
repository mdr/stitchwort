--| Both answers are the puzzle's, over every whole-number velocity, for a
--| target right of the start (`0 < left`) and below it (`top < 0`).

namespace Aoc.Year2021.Day17.Proofs
import Aoc.Common (Coords)
import Aoc.Year2021.Day17 (..)
import Aoc.Year2021.Day17.Spec (..)
import Std (Bool, Eq, Exists, Int, List, Nat, Option, Void)

--| The spec's "within" is the program's `inTarget`.
theorem withinOf ∀ (target: Target) (probe: Probe) (h: inTarget target probe = True): Within target probe := omega

theorem inTargetOf ∀ (target: Target) (probe: Probe) (h: Within target probe): inTarget target probe = True := omega

--| Every velocity that hits is a candidate: it is in the box.
theorem hitsCandidate ∀ (target: Target)
    (right: 0 < target.left)
    (below: target.top < 0)
    (velocity: Velocity) (n: Nat)
    (h: inTarget target (flight n velocity) = True):
    velocity ∈ candidates target :=
  let low := dxAtLeastOne target right velocity n h
  let high := dxAtMostRight target right velocity n h
  let floor := dyAtLeastBottom target below velocity n h
  let late := hitLate target below velocity n h
  let i := Int.toNat (velocity.x - 1)
  let j := Int.toNat (velocity.y - target.bottom)
  let iOf := Int.toIntToNat (velocity.x - 1) (omega)
  let jOf := Int.toIntToNat (velocity.y - target.bottom) (omega)
  let rightOf := Int.toIntToNat target.right (omega)
  let stepsOf := Int.toIntToNat (-2 * target.bottom) (omega)
  let iIn: i ∈ List.range 0 (Int.toNat target.right) :=
    List.memRangeFromIntro i (Int.toNat target.right) 0 (omega) (omega)
  let jIn: j ∈ List.range 0 (steps target) := List.memRangeFromIntro j (steps target) 0 (omega) (omega)
  let same: aimed target i j = velocity := Coords.ext (aimed target i j) velocity (omega) (omega)
  List.memFlatMapIntro
    (i => List.range 0 (steps target) |> .map (aimed target i))
    i
    velocity
    (List.range 0 (Int.toNat target.right))
    iIn
    (rewrite same at (List.memMap (List.range 0 (steps target)) j jIn (aimed target i)))

--| The velocities that hit, over every velocity: the program's list.
theorem hittingCorrect ∀ (target: Target)
    (right: 0 < target.left)
    (below: target.top < 0) (velocity: Velocity):
    Hits target velocity ↔ velocity ∈ hitting target :=
  {
    forward = hits =>
      match hits with
        | Witness n within =>
          let inside: inTarget target (flight n velocity) = True :=
            rewrite flightIsAfter n velocity in inTargetOf target _ within
          let late := hitLate target below velocity n inside
          let stepsOf := Int.toIntToNat (-2 * target.bottom) (omega)
          List.memFilterIntro
            (candidates target)
            (v => hitsWithin target (steps target) (launch v))
            (hitsCandidate target right below velocity n inside)
            (hitsWithinComplete target (steps target) n (launch velocity) (omega) inside),
    backward = member =>
      let both := List.memFilter (candidates target) (v => hitsWithin target (steps target) (launch v)) member
      match hitsWithinSound target (steps target) (launch velocity) both.right with
        | Witness n (Both early inside) => Witness n (rewrite <- flightIsAfter n velocity in withinOf target _ inside)
  }

--| The candidates are distinct, so the hitting velocities are.
theorem candidatesDistinct ∀ (target: Target): List.Distinct (candidates target) :=
  List.distinctFlatMap
    (i => List.range 0 (steps target) |> .map (aimed target i))
    (v => Int.toNat (v.x - 1))
    (List.range 0 (Int.toNat target.right))
    (List.distinctRangeFrom (Int.toNat target.right) 0)
    (i _ =>
      List.distinctMap
        (List.range 0 (steps target))
        (List.distinctRangeFrom (steps target) 0)
        (aimed target i)
        (a b same => omega [Eq.cong (v => v.y) same]))
    (i _ v member =>
      match List.memMapElim (aimed target i) v (List.range 0 (steps target)) member with
        | Witness j (Both _ made) =>
          rewrite <- made in Eq.trans (Eq.cong Int.toNat (omega: i.toInt + 1 - 1 = i.toInt)) (Int.toNatToInt i))

theorem hittingDistinct ∀ (target: Target): List.Distinct (hitting target) :=
  List.distinctFilter (candidates target) (v => hitsWithin target (steps target) (launch v)) (candidatesDistinct target)

--| Part 2: the number of distinct hitting velocities.
theorem part2Correct ∀ (target: Target)
    (right: 0 < target.left)
    (below: target.top < 0):
    HittingCount target (solvePart2 target) :=
  Witness (hitting target) (Both (hittingDistinct target) (Both (hittingCorrect target right below) rfl))

--| Part 1: the highest y position any hitting velocity reaches, if any
--| velocity hits ...
theorem part1Correct ∀ (target: Target)
    (right: 0 < target.left)
    (below: target.top < 0) (height: Nat)
    (found: solvePart1 target = Some height):
    Highest target height.toInt :=
  let most := List.maximumSome (List.map (hitting target) peak) height found
  let reached: ∃ (velocity: Velocity) => Hits target velocity
    ∧ (∃ (n: Nat) => (after n velocity).position.y = height.toInt) :=
    match List.memMapElim peak height (hitting target) most.left with
      | Witness velocity (Both member made) =>
        Witness velocity
          (Both
            ((hittingCorrect target right below velocity).backward member)
            (Witness
              (Int.toNat velocity.y)
              (rewrite <- flightIsAfter (Int.toNat velocity.y) velocity, <- made in peakReached velocity)))
  Both reached (velocity n hits =>
    let member := (hittingCorrect target right below velocity).forward hits
    let below := most.right (peak velocity) (List.memMap (hitting target) velocity member peak)
    rewrite <- flightIsAfter n velocity in omega [peakAbove velocity n])

--| ... and none does when the program finds none.
theorem part1None ∀ (target: Target)
    (right: 0 < target.left)
    (below: target.top < 0)
    (found: solvePart1 target = None) (velocity: Velocity):
    ¬(Hits target velocity) :=
  hits =>
    List.maximumNone
      (List.map (hitting target) peak)
      found
      (peak velocity)
      (List.memMap (hitting target) velocity ((hittingCorrect target right below velocity).forward hits) peak)
