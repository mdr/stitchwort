-- Part 2: with fewer bytes fallen every path still works
-- (`hasPathFewer`), so the exit can't become reachable again once it isn't.
-- The binary search ends at a count that blocks right after one that
-- doesn't (`firstBlockedCorrect`), so its byte is the first to block
-- (`part2Some`), and finding none means no byte is (`part2None`).

namespace Aoc.Year2024.Day18.Proofs
import Aoc.Year2024.Day18 (..)
import Aoc.Year2024.Day18.Spec (..)
import Std (And, Bool, Decidable, Eq, Exists, List, Nat, Option, Void)

-- More bytes fallen, fewer paths: a path with `more` fallen is one with
-- `fewer`.
theorem hasPathFewer (size: Nat) (bytes: List Position) (fewer: Nat) (more: Nat) (le: fewer ≤ more) (has: HasPath size bytes more):
    HasPath size bytes fewer :=
  Exists.elim has (steps path =>
    Witness steps
      (Both (safeFewer size bytes fewer more le start (And.left path))
        (walkFewer size bytes fewer more le start steps ({ x = size - 1, y = size - 1 }: Position) (And.right path))))

-- One step of the binary search: another halving while the bounds are
-- two or more apart...
theorem firstBlockedSplit (blocked: Nat → Bool) (low: Nat) (high: Nat) (apart: Nat.leq (Succ (Succ low)) high = True):
    firstBlocked blocked low high
      = (if blocked ((low + high) / 2) then firstBlocked blocked low ((low + high) / 2)
        else firstBlocked blocked ((low + high) / 2) high) :=
  rewrite firstBlocked.unfold blocked low high in
    Decidable.elimEq _ _ _ _ (isApart => rfl) (notApart => Void.exfalso (notApart apart))

-- ...and the upper bound once they're adjacent.
theorem firstBlockedDone (blocked: Nat → Bool) (low: Nat) (high: Nat) (close: Nat.leq (Succ (Succ low)) high = False):
    firstBlocked blocked low high = high :=
  rewrite firstBlocked.unfold blocked low high in
    Decidable.elimEq _ _ _ _ (isApart => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym close) isApart))) (notApart => rfl)

-- From a count that doesn't block to a later one that does, the search
-- finds a count that blocks right after one that doesn't.
theorem firstBlockedCorrect (blocked: Nat → Bool) (low: Nat) (high: Nat) (lowOpen: blocked low = False) (highBlocked: blocked high = True)
    (ordered: low < high):
    And (low < firstBlocked blocked low high)
      (And (firstBlocked blocked low high ≤ high) (And (blocked (firstBlocked blocked low high) = True) (blocked (firstBlocked blocked low high - 1) = False)))
    decreasing high - low :=
  match apart: Nat.leq (Succ (Succ low)) high with
    | True =>
      let middle := (low + high) / 2
      rewrite firstBlockedSplit blocked low high apart in
        match cut: blocked middle with
          | True =>
            let (Both after (Both within rest)) := firstBlockedCorrect blocked low middle lowOpen cut (omega [apart])
              [decreasing := omega [apart]]
            Both after (Both (omega [within, apart]) rest)
          | False =>
            let (Both after (Both within rest)) := firstBlockedCorrect blocked middle high cut highBlocked (omega [apart])
              [decreasing := omega [apart]]
            Both (omega [after, apart]) (Both within rest)
    | False =>
      let previous: high - 1 = low := omega [ordered, apart]
      rewrite firstBlockedDone blocked low high apart in Both ordered (Both (Nat.leRefl high) (Both highBlocked (rewrite previous in lowOpen)))

-- What part 2 answers: nothing when the exit is cut off before any byte
-- falls...
theorem part2Closed (size: Nat) (bytes: List Position) (startClosed: reachable size bytes 0 = False): solvePart2 size bytes = None :=
  rewrite startClosed in rfl

-- ...or still reachable once all have...
theorem part2Open (size: Nat) (bytes: List Position) (startOpen: reachable size bytes 0 = True) (stillOpen: reachable size bytes bytes.length = True):
    solvePart2 size bytes = None :=
  rewrite startOpen, stillOpen in rfl

-- ...and otherwise the byte the search finds.
theorem part2Search (size: Nat) (bytes: List Position) (startOpen: reachable size bytes 0 = True)
    (allBlocked: reachable size bytes bytes.length = False):
    solvePart2 size bytes = bytes.get (firstBlocked (fallen => !reachable size bytes fallen) 0 bytes.length - 1) :=
  rewrite startOpen, allBlocked in rfl

-- Part 2's byte, for each way the exit is reachable at the ends.
theorem part2SomeCases (size: Nat) (bytes: List Position) (byte: Position) (answer: solvePart2 size bytes = Some byte):
    (atStart: Bool) → reachable size bytes 0 = atStart → (atEnd: Bool) → reachable size bytes bytes.length = atEnd →
      IsFirstBlocking size bytes byte
  | False, startClosed, atEnd, endReachable =>
    Void.exfalso (Option.noneNotSome byte (Eq.trans (Eq.sym (part2Closed size bytes startClosed)) answer))
  | True, startOpen, True, stillOpen => Void.exfalso (Option.noneNotSome byte (Eq.trans (Eq.sym (part2Open size bytes startOpen stillOpen)) answer))
  | True, startOpen, False, allBlocked =>
    let blocked := (fallen: Nat) => !reachable size bytes fallen
    let differ: Not (0 = bytes.length) := same => Bool.falseNotTrue (Eq.trans (Eq.sym allBlocked) (rewrite <- same in startOpen))
    let found := Eq.trans (Eq.sym (part2Search size bytes startOpen allBlocked)) answer
    let (Both after (Both within (Both cut open))) :=
      firstBlockedCorrect blocked 0 bytes.length (Eq.cong Bool.not startOpen) (Eq.cong Bool.not allBlocked) (omega [differ])
    let index := firstBlocked blocked 0 bytes.length - 1
    let next: index + 1 = firstBlocked blocked 0 bytes.length := omega [after]
    Witness index
      (Both found
        (Both
          (has =>
            let stillOpen := reachableComplete size bytes (index + 1) has
            Bool.falseNotTrue (Eq.trans (Eq.sym (Bool.notTrue _ (rewrite <- next at cut in cut))) stillOpen))
          (earlier le => hasPathFewer size bytes earlier index le (reachableSound size bytes index (Bool.notFalse _ open)))))

-- When part 2 finds a byte, it is the first whose fall leaves no path.
theorem part2Some (size: Nat) (bytes: List Position) (byte: Position) (answer: solvePart2 size bytes = Some byte):
    IsFirstBlocking size bytes byte :=
  part2SomeCases size bytes byte answer (reachable size bytes 0) rfl (reachable size bytes bytes.length) rfl

-- No first blocking byte, for each way the exit is reachable at the ends.
theorem part2NoneCases (size: Nat) (bytes: List Position) (answer: solvePart2 size bytes = None) (byte: Position) (index: Nat)
    (got: bytes.get index = Some byte) (blockedAfter: Not (HasPath size bytes (index + 1)))
    (openBefore: (earlier: Nat) → earlier ≤ index → HasPath size bytes earlier):
    (atStart: Bool) → reachable size bytes 0 = atStart → (atEnd: Bool) → reachable size bytes bytes.length = atEnd → Void
  | False, startClosed, atEnd, endReachable =>
    Bool.falseNotTrue (Eq.trans (Eq.sym startClosed) (reachableComplete size bytes 0 (openBefore 0 (omega))))
  | True, startOpen, True, stillOpen =>
    let inside: index < bytes.length := Eq.trans (Eq.sym (List.isSomeGet bytes index)) (rewrite got in rfl)
    blockedAfter (hasPathFewer size bytes (index + 1) bytes.length (omega [inside]) (reachableSound size bytes bytes.length stillOpen))
  | True, startOpen, False, allBlocked =>
    let inside: index < bytes.length := Eq.trans (Eq.sym (List.isSomeGet bytes index)) (rewrite got in rfl)
    let blocked := (fallen: Nat) => !reachable size bytes fallen
    let (Both after (Both within rest)) :=
      firstBlockedCorrect blocked 0 bytes.length (Eq.cong Bool.not startOpen) (Eq.cong Bool.not allBlocked) (omega [inside])
    let found := firstBlocked blocked 0 bytes.length - 1
    let missing := Eq.trans (Eq.sym (part2Search size bytes startOpen allBlocked)) answer
    let present: found < bytes.length := omega [after, within]
    Bool.falseNotTrue (Eq.trans (Eq.sym (Eq.trans (Eq.sym (List.isSomeGet bytes found)) (Eq.cong Option.isSome missing))) present)

-- When part 2 finds no byte, no byte is the first whose fall leaves no
-- path.
theorem part2None (size: Nat) (bytes: List Position) (answer: solvePart2 size bytes = None) (byte: Position)
    (first: IsFirstBlocking size bytes byte): Void :=
  Exists.elim first (index parts =>
    let (Both got (Both blockedAfter openBefore)) := parts
    part2NoneCases size bytes answer byte index got blockedAfter openBefore (reachable size bytes 0) rfl (reachable size bytes bytes.length) rfl)
