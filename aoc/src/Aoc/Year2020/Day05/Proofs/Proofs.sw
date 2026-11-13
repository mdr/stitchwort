--| Day 5 proved: on any input the parser reads, the program's seat IDs are
--| the puzzle's (Seat.sw, Parse.sw), part 1 is the highest of them, and
--| part 2 is your seat whenever the puzzle's promise of exactly one holds.

namespace Aoc.Year2020.Day05.Proofs
import Aoc.Year2020.Day05 (..)
import Aoc.Year2020.Day05.Spec (..)
import Std (Bool, DecEq, Eq, Exists, Fail, List, Nat, Option, Result, Text, Void)

theorem seatIdsWritten ∀ (lines: List (List Char)) (passes: List Pass) (impossible: List.All2 PassWritten lines passes): seatIds lines = passes.map .seatId :=
  match lines, passes, impossible with
    | [], [], all => rfl
    | [line, ..lines], [pass, ..passes], Both (Both rows (Both columns same)) rest =>
      rewrite same, seatIdSpec pass rows columns, seatIdsWritten lines passes rest in rfl
    | [], [_, .._], impossible => Void.exfalso impossible
    | [_, .._], [], impossible => Void.exfalso impossible

theorem idsWritten ∀ (input: Text) (passes: List Pass) (parsed: Fail.toResult (() => parsePasses input) = Ok passes):
    seatIds (input.lines.map Text.toList) = passes.map .seatId :=
  seatIdsWritten _ passes (parseWritten input passes parsed)

theorem part1Correct ∀ (input: Text) (passes: List Pass) (parsed: Fail.toResult (() => parsePasses input) = Ok passes):
    solvePart1 passes = part1Answer (input.lines.map Text.toList) :=
  Eq.cong List.maximum (Eq.sym (idsWritten input passes parsed))

--| In a sorted list, every member is at least the first.
theorem atLeastFirst ∀ (first: Nat) (rest: List Nat) (sorted: List.Sorted Nat.leq [first, ..rest]) (x: Nat): x ∈ [first, ..rest] → first ≤ x
  | Inl same => rewrite same in Nat.leRefl x
  | Inr later => List.sortedHeadLe Nat.leq (a b c ab bc => Nat.leTrans a b c ab bc) first x rest sorted later

theorem gapSound: ∀ (ids: List Nat) => List.Sorted Nat.leq ids → ∀ (seat: Nat) => gap ids = Some seat → ¬(seat ∈ ids) ∧ (seat + 1) ∈ ids ∧ (seat - 1) ∈ ids
  | [], sorted, seat, found => Void.exfalso (Option.noneNotSome seat found)
  | [only], sorted, seat, found => Void.exfalso (Option.noneNotSome seat found)
  | [low, high, ..rest], Both ordered sortedRest, seat, found =>
    match apart: high == low + 2 with
      | True =>
        let two := apart.read
        let made := Option.someInjective found
        Both
          (member =>
            match member with
              | Inl same => omega
              | Inr (Inl same) => omega
              | Inr (Inr later) => omega [atLeastFirst high rest sortedRest seat (Inr later)])
          (Both (Inr (Inl (omega))) (Inl (omega)))
      | False =>
        match gapSound [high, ..rest] sortedRest seat found with
          | Both missing (Both above below) =>
            let atLeast := atLeastFirst high rest sortedRest (seat - 1) below
            Both
              (member =>
                match member with
                  | Inl same =>
                    match seat with
                      | Zero => missing below
                      | Succ before => omega
                  | Inr later => missing later)
              (Both (Inr above) (Inr below))

theorem gapComplete: ∀ (ids: List Nat) => List.Sorted Nat.leq ids → ∀ (seat: Nat) => ¬(seat ∈ ids) → (seat + 1) ∈ ids → (seat - 1) ∈ ids → ∃ (found: Nat) => gap ids = Some found
  | [], sorted, seat, missing, above, below => Void.exfalso above
  | [only], sorted, seat, missing, Inl up, Inl down => omega
  | [only], sorted, seat, missing, Inl up, Inr nothing => Void.exfalso nothing
  | [only], sorted, seat, missing, Inr nothing, below => Void.exfalso nothing
  | [low, high, ..rest], Both ordered sortedRest, seat, missing, above, below =>
    match apart: high == low + 2 with
      | True => Witness (low + 1) rfl
      | False =>
        let notTwo := apart.read
        let atLeast := atLeastFirst low [high, ..rest] (Both ordered sortedRest) (seat - 1) below
        let aboveRest: (seat + 1) ∈ [high, ..rest] :=
          match above with
            | Inl same => Void.exfalso (omega)
            | Inr later => later
        let belowRest: (seat - 1) ∈ [high, ..rest] :=
          match below with
            | Inl same =>
              let highAtMost := atLeastFirst high rest sortedRest (seat + 1) aboveRest
              let notSeat: high ≠ seat := equal => missing (Inr (Inl equal))
              match seat with
                | Zero => Void.exfalso (missing (Inl same))
                | Succ before => Inl (omega)
            | Inr later => later
        gapComplete [high, ..rest] sortedRest seat (member => missing (Inr member)) aboveRest belowRest

--| "Every seat": no pass names a seat past the 128 × 8.
theorem idsBelow: ∀ (lines: List (List Char)) (passes: List Pass) => List.All2 PassWritten lines passes → ∀ (id: Nat) => id ∈ passes.map .seatId → id < 128 * 8
  | [], [], all, id, member => Void.exfalso member
  | [line, ..lines], [pass, ..passes], Both (Both rows (Both columns same)) rest, id, Inl first =>
    let below: Nat.fromBits (pass.row ++ pass.column) < Nat.pow 2 (pass.row.length + pass.column.length) :=
      rewrite <- List.lengthAppend pass.row pass.column in Nat.fromBitsBelow (pass.row ++ pass.column)
    rewrite <- first in (rewrite rows, columns at below in below)
  | [line, ..lines], [pass, ..passes], Both written rest, id, Inr later => idsBelow lines passes rest id later
  | [], [_, .._], impossible, id, member => Void.exfalso impossible
  | [_, .._], [], impossible, id, member => Void.exfalso impossible

theorem memSort ∀ (ids: List Nat) (id: Nat): id ∈ ids.sort ↔ id ∈ ids := {
  forward = member => List.memPerm (ids.sort) ids (List.sortPerm ids) id member,
  backward = member => List.memPerm ids (ids.sort) (List.permSym (ids.sort) ids (List.sortPerm ids)) id member
}

theorem yourSeatOf ∀ (ids: List Nat) (seat: Nat) (missing: ¬(seat ∈ ids)) (above: (seat + 1) ∈ ids) (below: (seat - 1) ∈ ids): isYourSeat ids seat = True :=
  let notFound: ids.contains seat = False :=
    match found: ids.contains seat with
      | True => Void.exfalso (missing found.read)
      | False => rfl
  rewrite notFound, (List.memContains ids (seat + 1)).backward above, (List.memContains ids (seat - 1)).backward below in rfl

theorem yourSeatMembers ∀ (ids: List Nat) (seat: Nat) (yours: isYourSeat ids seat = True): ¬(seat ∈ ids) ∧ (seat + 1) ∈ ids ∧ (seat - 1) ∈ ids :=
  let Both notFound (Both above below) := yours
  Both
    (member => Bool.falseNotTrue (rewrite <- notFound.read in (List.memContains ids seat).backward member))
    (Both above.read below.read)

theorem candidateIntro ∀ (count: Nat) (ids: List Nat) (seat: Nat) (below: seat + 1 < count) (yours: isYourSeat ids seat = True):
    seat ∈ (List.range 0 count).filter (isYourSeat ids) :=
  List.memFilterIntro (List.range 0 count) (isYourSeat ids) (List.memRangeFromIntro seat count 0 (Nat.zeroLe seat) (omega)) yours

theorem gapYours ∀ (count: Nat) (ids: List Nat) (bound: ∀ (id: Nat) => id ∈ ids → id < count) (seat: Nat) (found: gap ids.sort = Some seat):
    seat ∈ (List.range 0 count).filter (isYourSeat ids) :=
  match gapSound ids.sort (List.sortSortedNat ids) seat found with
    | Both missing (Both above below) =>
      let aboveIds := (memSort ids (seat + 1)).forward above
      candidateIntro count ids seat (bound (seat + 1) aboveIds)
        (yourSeatOf ids seat (member => missing ((memSort ids seat).backward member)) aboveIds ((memSort ids (seat - 1)).forward below))

--| Part 2 finds only a seat that could be yours.
theorem part2Sound ∀ (input: Text) (passes: List Pass) (parsed: Fail.toResult (() => parsePasses input) = Ok passes) (seat: Nat) (found: solvePart2 passes = Some seat):
    seat ∈ part2Answers (input.lines.map Text.toList) :=
  Eq.subst (written => seat ∈ (List.range 0 (128 * 8)).filter (isYourSeat written)) (Eq.sym (idsWritten input passes parsed))
    (gapYours (128 * 8) (passes.map .seatId) (idsBelow (input.lines.map Text.toList) passes (parseWritten input passes parsed)) seat found)

theorem yoursGap ∀ (count: Nat) (ids: List Nat) (seat: Nat) (candidate: seat ∈ (List.range 0 count).filter (isYourSeat ids)): ∃ (found: Nat) => gap ids.sort = Some found :=
  match yourSeatMembers ids seat (And.right (List.memFilter (List.range 0 count) (isYourSeat ids) candidate)) with
    | Both missing (Both above below) =>
      gapComplete ids.sort (List.sortSortedNat ids) seat (member => missing ((memSort ids seat).forward member)) ((memSort ids (seat + 1)).backward above) ((memSort ids (seat - 1)).backward below)

--| Part 2 finds a seat whenever one could be yours.
theorem part2Complete ∀ (input: Text) (passes: List Pass) (parsed: Fail.toResult (() => parsePasses input) = Ok passes) (seat: Nat) (yours: seat ∈ part2Answers (input.lines.map Text.toList)):
    ∃ (found: Nat) => solvePart2 passes = Some found :=
  yoursGap (128 * 8) (passes.map .seatId) seat
    (Eq.subst (written => seat ∈ (List.range 0 (128 * 8)).filter (isYourSeat written)) (idsWritten input passes parsed) yours)

theorem onlyAnswer ∀ (answers: List Nat) (seat: Nat) (result: Option Nat) (only: answers = [seat])
    (sound: ∀ (found: Nat) => result = Some found → found ∈ answers) (complete: seat ∈ answers → ∃ (found: Nat) => result = Some found): result = Some seat :=
  match complete (rewrite only in Inl rfl) with
    | Witness found made =>
      let member := sound found made
      rewrite only at member in
        match member with
          | Inl same => rewrite made, same in rfl
          | Inr nothing => Void.exfalso nothing

--| "Your seat should be the only missing boarding pass in your list": when
--| exactly one seat could be yours, part 2 is that seat.
theorem part2Correct ∀ (input: Text) (passes: List Pass) (parsed: Fail.toResult (() => parsePasses input) = Ok passes) (seat: Nat) (only: part2Answers (input.lines.map Text.toList) = [seat]):
    solvePart2 passes = Some seat :=
  onlyAnswer _ seat _ only (part2Sound input passes parsed) (part2Complete input passes parsed seat)
