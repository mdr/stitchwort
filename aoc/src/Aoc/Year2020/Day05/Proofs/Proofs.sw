--| Day 5 proved: on any input the parser reads, the program's seat IDs are
--| the puzzle's (Seat.sw, Parse.sw), part 1 is the highest of them, and
--| part 2 is your seat whenever the puzzle's promise of exactly one holds.

namespace Aoc.Year2020.Day05.Proofs
import Aoc.Year2020.Day05 (..)
import Aoc.Year2020.Day05.Spec (..)
import Std (Bool, DecEq, Eq, Exists, Fail, List, Nat, Option, Result, Text, Void)

theorem seatIdsWritten ∀ (lines: List (List Char)) (passes: List Pass)
    (impossible: List.All2 PassWritten lines passes):
    seatIds lines = passes.map .seatId :=
  match lines, passes, impossible with
    | [], [], all => byComputing
    | [line, ..lines], [pass, ..passes], Both (Both rows (Both columns same)) rest =>
      rewrite same, seatIdSpec pass rows columns, seatIdsWritten lines passes rest
    | [], [_, .._], impossible => impossible.impossible
    | [_, .._], [], impossible => impossible.impossible

theorem idsWritten ∀ (input: Text) (passes: List Pass)
    (parsed: Fail.toResult (() => parsePasses input) = Ok passes):
    seatIds (input.lines.map Text.toList) = passes.map .seatId :=
  seatIdsWritten _ passes (parseWritten input passes parsed)

theorem part1Correct ∀ (input: Text) (passes: List Pass)
    (parsed: Fail.toResult (() => parsePasses input) = Ok passes):
    solvePart1 passes = part1Answer (input.lines.map Text.toList) :=
  Eq.cong List.maximum (idsWritten input passes parsed).flipped

--| In a sorted list, every member is at least the first.
theorem atLeastFirst ∀ (first: Nat) (rest: List Nat)
    (sorted: List.Sorted Nat.leq [first, ..rest]) (x: Nat):
    x ∈ [first, ..rest] → first ≤ x
  | Inl same => rewrite same then Nat.leRefl x
  | Inr later => List.sortedHeadLe Nat.leq (a b c ab bc => Nat.leTrans a b c ab bc) first x rest sorted later

theorem gapSound: ∀ (ids: List Nat) => List.Sorted Nat.leq ids
      → ∀ (seat: Nat) => gap ids = Some seat → ¬(seat ∈ ids) ∧ (seat + 1) ∈ ids ∧ (seat - 1) ∈ ids
  | [], sorted, seat, found => (Option.noneNotSome seat found).impossible
  | [only], sorted, seat, found => (Option.noneNotSome seat found).impossible
  | [low, high, ..rest], Both ordered sortedRest, seat, found =>
    match apart: high == low + 2 with
      | True =>
        let two := apart
        let made := Option.someInjective found
        Both
          (member =>
            match member with
              | Inl same => arithmetic
              | Inr (Inl same) => arithmetic
              | Inr (Inr later) => arithmetic [atLeastFirst high rest sortedRest seat (Inr later)])
          (Both (Inr (Inl (arithmetic))) (Inl (arithmetic)))
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
                      | Succ before => arithmetic
                  | Inr later => missing later)
              (Both (Inr above) (Inr below))

theorem gapComplete: ∀ (ids: List Nat) => List.Sorted Nat.leq ids
      → ∀ (seat: Nat) => ¬(seat ∈ ids) → (seat + 1) ∈ ids → (seat - 1) ∈ ids → ∃ (found: Nat) => gap ids = Some found
  | [], sorted, seat, missing, above, below => above.impossible
  | [only], sorted, seat, missing, Inl up, Inl down => arithmetic
  | [only], sorted, seat, missing, Inl up, Inr nothing => nothing.impossible
  | [only], sorted, seat, missing, Inr nothing, below => nothing.impossible
  | [low, high, ..rest], Both ordered sortedRest, seat, missing, above, below =>
    match apart: high == low + 2 with
      | True => Witness (low + 1) byComputing
      | False =>
        let notTwo := apart
        let atLeast := atLeastFirst low [high, ..rest] (Both ordered sortedRest) (seat - 1) below
        let aboveRest: (seat + 1) ∈ [high, ..rest] := match above with
          | Inl same => Void.impossible arithmetic
          | Inr later => later
        let belowRest: (seat - 1) ∈ [high, ..rest] := match below with
          | Inl same =>
            let highAtMost := atLeastFirst high rest sortedRest (seat + 1) aboveRest
            let notSeat: high ≠ seat := equal => missing (Inr (Inl equal))
            match seat with
              | Zero => Void.impossible (missing (Inl same))
              | Succ before => Inl (arithmetic)
          | Inr later => later
        gapComplete [high, ..rest] sortedRest seat (member => missing (Inr member)) aboveRest belowRest

--| "Every seat": no pass names a seat past the 128 × 8.
theorem idsBelow: ∀ (lines: List (List Char)) (passes: List Pass) => List.All2 PassWritten lines passes
      → ∀ (id: Nat) => id ∈ passes.map .seatId → id < 128 * 8
  | [], [], all, id, member => member.impossible
  | [line, ..lines], [pass, ..passes], Both (Both rows (Both columns same)) rest, id, Inl first =>
    let below: Nat.fromBits (pass.row ++ pass.column) < Nat.pow 2 (pass.row.length + pass.column.length) :=
      rewrite <- List.lengthAppend pass.row pass.column then Nat.fromBitsBelow (pass.row ++ pass.column)
    rewrite <- first then (rewrite rows, columns at below then below)
  | [line, ..lines], [pass, ..passes], Both written rest, id, Inr later => idsBelow lines passes rest id later
  | [], [_, .._], impossible, id, member => impossible.impossible
  | [_, .._], [], impossible, id, member => impossible.impossible

theorem memSort ∀ (ids: List Nat) (id: Nat): id ∈ ids.sort ↔ id ∈ ids := {
  forward = member => List.memPerm (ids.sort) ids (List.sortPerm ids) id member,
  backward = member => List.memPerm ids (ids.sort) (List.permSym (ids.sort) ids (List.sortPerm ids)) id member
}

theorem yourSeatOf ∀ (ids: List Nat) (seat: Nat)
    (missing: ¬(seat ∈ ids))
    (above: (seat + 1) ∈ ids)
    (below: (seat - 1) ∈ ids):
    isYourSeat ids seat = True :=
  let notFound: ids.contains seat = False := match found: ids.contains seat with
    | True => (missing found.read).impossible
    | False => byComputing
  rewrite notFound, (List.memContains ids (seat + 1)).backward above, (List.memContains ids (seat - 1)).backward below

theorem yourSeatMembers ∀ (ids: List Nat) (seat: Nat)
    (yours: isYourSeat ids seat = True):
    ¬(seat ∈ ids) ∧ (seat + 1) ∈ ids ∧ (seat - 1) ∈ ids :=
  let Both notFound (Both above below) := yours
  Both (member => Bool.falseNotTrue (rewrite <- notFound.read then member)) (Both above.read below.read)

theorem candidateIntro ∀ (count: Nat) (ids: List Nat) (seat: Nat)
    (below: seat + 1 < count)
    (yours: isYourSeat ids seat = True):
    seat ∈ (List.range 0 count).filter (isYourSeat ids) :=
  List.memFilterIntro
    (List.range 0 count)
    (isYourSeat ids)
    (List.memRangeFromIntro seat count 0 (Nat.zeroLe seat) (arithmetic))
    yours

theorem gapYours ∀ (count: Nat) (ids: List Nat)
    (bound: ∀ (id: Nat) => id ∈ ids → id < count) (seat: Nat)
    (found: gap ids.sort = Some seat):
    seat ∈ (List.range 0 count).filter (isYourSeat ids) :=
  match gapSound ids.sort (List.sortSortedNat ids) seat found with
    | Both missing (Both above below) =>
      let aboveIds := (memSort ids (seat + 1)).forward above
      candidateIntro count ids seat
        (bound (seat + 1) aboveIds)
        (yourSeatOf ids seat
          (member => missing ((memSort ids seat).backward member))
          aboveIds
          ((memSort ids (seat - 1)).forward below))

--| Part 2 finds only a seat that could be yours.
theorem part2Sound ∀ (input: Text) (passes: List Pass)
    (parsed: Fail.toResult (() => parsePasses input) = Ok passes) (seat: Nat)
    (found: solvePart2 passes = Some seat):
    seat ∈ part2Answers (input.lines.map Text.toList) :=
  Eq.subst
    (written => seat ∈ (List.range 0 (128 * 8)).filter (isYourSeat written))
    (idsWritten input passes parsed).flipped
    (gapYours
      (128 * 8)
      (passes.map .seatId)
      (idsBelow (input.lines.map Text.toList) passes (parseWritten input passes parsed))
      seat
      found)

theorem yoursGap ∀ (count: Nat) (ids: List Nat) (seat: Nat)
    (candidate: seat ∈ (List.range 0 count).filter (isYourSeat ids)):
    ∃ (found: Nat) => gap ids.sort = Some found :=
  match yourSeatMembers ids seat (And.right (List.memFilter (List.range 0 count) (isYourSeat ids) candidate)) with
    | Both missing (Both above below) =>
      gapComplete ids.sort
        (List.sortSortedNat ids)
        seat
        (member => missing ((memSort ids seat).forward member))
        ((memSort ids (seat + 1)).backward above)
        ((memSort ids (seat - 1)).backward below)

--| Part 2 finds a seat whenever one could be yours.
theorem part2Complete ∀ (input: Text) (passes: List Pass)
    (parsed: Fail.toResult (() => parsePasses input) = Ok passes) (seat: Nat)
    (yours: seat ∈ part2Answers (input.lines.map Text.toList)):
    ∃ (found: Nat) => solvePart2 passes = Some found :=
  yoursGap
    (128 * 8)
    (passes.map .seatId)
    seat
    (Eq.subst
      (written => seat ∈ (List.range 0 (128 * 8)).filter (isYourSeat written))
      (idsWritten input passes parsed)
      yours)

theorem onlyAnswer ∀ (answers: List Nat) (seat: Nat) (result: Option Nat)
    (only: answers = [seat])
    (sound: ∀ (found: Nat) => result = Some found → found ∈ answers)
    (complete: seat ∈ answers → ∃ (found: Nat) => result = Some found):
    result = Some seat :=
  match complete (rewrite only then Inl byComputing) with
    | Witness found made =>
      let member := sound found made
      rewrite only at member then
        match member with
          | Inl same => rewrite made, same
          | Inr nothing => nothing.impossible

--| "Your seat should be the only missing boarding pass in your list": when
--| exactly one seat could be yours, part 2 is that seat.
theorem part2Correct ∀ (input: Text) (passes: List Pass)
    (parsed: Fail.toResult (() => parsePasses input) = Ok passes) (seat: Nat)
    (only: part2Answers (input.lines.map Text.toList) = [seat]):
    solvePart2 passes = Some seat :=
  onlyAnswer _ seat _ only (part2Sound input passes parsed) (part2Complete input passes parsed seat)
