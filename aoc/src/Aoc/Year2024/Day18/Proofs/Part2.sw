-- Part 2: with fewer bytes fallen every path still works
-- (`hasPathFewer`), so the exit can't become reachable again once it isn't.
-- std's binary search, `Nat.partitionPoint`, ends at a count that blocks
-- right after one that doesn't (`Nat.partitionPointBounds`), so its byte is
-- the first to block (`part2Some`); and as reachability only gets lost,
-- every count before it is open and every one after blocked
-- (`Nat.partitionPointSpec`), so finding none means no byte is
-- (`part2None`).

namespace Aoc.Year2024.Day18.Proofs
import Aoc.Year2024.Day18 (..)
import Aoc.Year2024.Day18.Spec (..)
import Std (And, Bool, Eq, Exists, List, Nat, Option, Void)

-- More bytes fallen, fewer paths: a path with `more` fallen is one with
-- `fewer`.
theorem hasPathFewer (size: Nat) (bytes: List Position) (fewer: Nat) (more: Nat) (le: fewer ≤ more) (has: HasPath size bytes more):
    HasPath size bytes fewer :=
  Exists.elim has (steps path =>
    Witness steps
      (Both (safeFewer size bytes fewer more le Position.start (And.left path))
        (walkFewer size bytes fewer more le Position.start steps ({ x = size - 1, y = size - 1 }: Position) (And.right path))))

-- The exit reachable with more bytes fallen is reachable with fewer.
theorem reachableFewer (size: Nat) (bytes: List Position) (fewer: Nat) (more: Nat) (le: fewer ≤ more) (open: reachable size bytes more = True):
    reachable size bytes fewer = True :=
  reachableComplete size bytes fewer (hasPathFewer size bytes fewer more le (reachableSound size bytes more open))

-- An index with no byte is past the end.
theorem pastEnd (bytes: List Position) (index: Nat) (missing: bytes.get index = None) (inside: index < bytes.length): Void :=
  Bool.falseNotTrue (Eq.trans (Eq.sym (Eq.trans (Eq.sym (List.isSomeGet bytes index)) (Eq.cong Option.isSome missing))) inside)

-- Part 2's byte, for each count the search can end at.
theorem part2SomeCases (size: Nat) (bytes: List Position) (byte: Position) (answer: solvePart2 size bytes = Some byte):
    (found: Nat) → Nat.partitionPoint 0 (bytes.length + 1) (reachable size bytes) = found → IsFirstBlocking size bytes byte
  | Zero, ended => Void.exfalso (Option.noneNotSome byte (rewrite ended at answer in answer))
  | Succ index, ended =>
    let got: bytes.get index = Some byte := rewrite ended at answer in answer
    let inside: index < bytes.length := Eq.trans (Eq.sym (List.isSomeGet bytes index)) (rewrite got in rfl)
    let (Both above (Both below (Both before after))) := Nat.partitionPointBounds 0 (bytes.length + 1) (reachable size bytes) (Nat.zeroLe (bytes.length + 1))
    let opened: reachable size bytes index = True :=
      match rewrite ended at before in before with
        | Inl zero => Void.exfalso (omega [zero])
        | Inr holds => holds
    let same: index + 1 = Succ index := omega
    let blocked: reachable size bytes (Succ index) = False :=
      match rewrite ended at after in after with
        | Inl high => Void.exfalso (omega [high, inside])
        | Inr fails => fails
    Witness index
      (Both got
        (Both (has => Bool.falseNotTrue (Eq.trans (Eq.sym blocked) (reachableComplete size bytes (Succ index) (rewrite <- same in has))))
          (earlier le => hasPathFewer size bytes earlier index le (reachableSound size bytes index opened))))

-- When part 2 finds a byte, it is the first whose fall leaves no path.
theorem part2Some (size: Nat) (bytes: List Position) (byte: Position) (answer: solvePart2 size bytes = Some byte):
    IsFirstBlocking size bytes byte :=
  part2SomeCases size bytes byte answer (Nat.partitionPoint 0 (bytes.length + 1) (reachable size bytes)) rfl

-- No first blocking byte, for each count the search can end at.
theorem part2NoneCases (size: Nat) (bytes: List Position) (answer: solvePart2 size bytes = None) (byte: Position) (index: Nat)
    (got: bytes.get index = Some byte) (blockedAfter: Not (HasPath size bytes (index + 1)))
    (openBefore: (earlier: Nat) → earlier ≤ index → HasPath size bytes earlier):
    (found: Nat) → Nat.partitionPoint 0 (bytes.length + 1) (reachable size bytes) = found → Void
  | found, ended =>
    let inside: index < bytes.length := Eq.trans (Eq.sym (List.isSomeGet bytes index)) (rewrite got in rfl)
    let (Both holdsBefore failsAfter) :=
      Nat.partitionPointSpec 0 (bytes.length + 1) (reachable size bytes) (Nat.zeroLe (bytes.length + 1)) (smaller larger le open =>
        reachableFewer size bytes smaller larger le open)
    match found with
      | Zero =>
        let startBlocked := failsAfter 0 (rewrite ended in Nat.leRefl 0) (omega)
        Bool.falseNotTrue (Eq.trans (Eq.sym startBlocked) (reachableComplete size bytes 0 (openBefore 0 (Nat.zeroLe index))))
      | Succ last =>
        let missing: bytes.get last = None := rewrite ended at answer in answer
        let past: Not (last < bytes.length) := pastEnd bytes last missing
        let stillOpen := holdsBefore (index + 1) (Nat.zeroLe (index + 1)) (rewrite ended in omega [past, inside])
        blockedAfter (reachableSound size bytes (index + 1) stillOpen)

-- When part 2 finds no byte, no byte is the first whose fall leaves no
-- path.
theorem part2None (size: Nat) (bytes: List Position) (answer: solvePart2 size bytes = None) (byte: Position)
    (first: IsFirstBlocking size bytes byte): Void :=
  Exists.elim first (index parts =>
    let (Both got (Both blockedAfter openBefore)) := parts
    part2NoneCases size bytes answer byte index got blockedAfter openBefore (Nat.partitionPoint 0 (bytes.length + 1) (reachable size bytes)) rfl)
