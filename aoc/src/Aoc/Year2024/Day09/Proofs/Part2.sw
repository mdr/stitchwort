-- Part 2 proved in part, for every disk map: each file is moved once, keeps
-- its number and length, and moves only leftwards, so the disk holds the
-- same file blocks. Not proved: that a file lands on free blocks, that the
-- span it lands in is the leftmost that fits, and so that part 2 is the
-- spec's `part2`; the tests check that on small disks.

namespace Aoc.Year2024.Day09.Proofs
import Aoc.Year2024.Day09 (..)
import Aoc.Year2024.Day09.Spec (..)
import Std (Eq, List, Nat, Option, Void)

-- The disk map's files where they start.
def filesOf (diskMap: List Nat): List File := (layoutFrom 0 0 diskMap).fst

-- What a move keeps: the file's number and length.
def File.idAndLength (file: File): (Nat, Nat) := (file.id, file.span.length)

-- A file's blocks.
def File.blocks (file: File): List Nat := List.replicate file.span.length file.id

-- `after` is `before`, moved left or not at all.
def MovedLeft (before: File) (after: File): Prop :=
  after.id = before.id ∧ after.span.length = before.span.length ∧ after.span.start ≤ before.span.start

-- The span found starts before `before`.
theorem fitBefore (free: FreeSpace) (length: Nat) (before: Nat) (span: Span) (fit: free.leftmostFit length before = Some span): span.start < before :=
  And.right (Option.filterEqSome _ ((found: Span) => found.start < before) span fit)

-- A move keeps the file's number and length, and goes left if anywhere.
theorem moveFileLeft (free: FreeSpace) (file: File): MovedLeft file (free.moveFile file).snd :=
  match fit: free.leftmostFit file.span.length file.span.start with
    | None => Both rfl (Both rfl (Nat.leRefl file.span.start))
    | Some span =>
      let earlier := fitBefore free file.span.length file.span.start span fit
      Both rfl (Both rfl (omega))

theorem moveFileKeeps (free: FreeSpace) (file: File): (free.moveFile file).snd.idAndLength = file.idAndLength :=
  match fit: free.leftmostFit file.span.length file.span.start with
    | None => rfl
    | Some span => rfl

-- What holds of each element and its image holds along the zip.
theorem allZipWith (holds: a → c → Prop) (g: a → b → c) (each: (x: a) → (y: b) → holds x (g x y)):
    (xs: List a) → (ys: List b) → List.All (pair => holds pair.fst pair.snd) (List.zip xs (List.zipWith xs ys g))
  | Nil, ys => Trivial
  | Cons x rest, Nil => Trivial
  | Cons x rest, Cons y others => Both (each x y) (allZipWith holds g each rest others)

-- The files are moved once each, highest number first, and keep their
-- numbers and lengths.
theorem eachFileOnce (diskMap: List Nat): (compactFiles diskMap).map .idAndLength = (filesOf diskMap).reverse.map .idAndLength :=
  let layout := layoutFrom 0 0 diskMap
  let initial := FreeSpace.of (joinTouching layout.snd)
  rewrite List.mapAccumLeftList layout.fst.reverse initial FreeSpace.moveFile in
    List.mapZipWithScanLeft File.idAndLength File.idAndLength (file free => (FreeSpace.moveFile free file).snd) (file free => moveFileKeeps free file)
      layout.fst.reverse initial (free file => (FreeSpace.moveFile free file).fst)

-- Each file moves left or stays.
theorem filesMoveLeft (diskMap: List Nat):
    List.All (pair => MovedLeft pair.fst pair.snd) (List.zip (filesOf diskMap).reverse (compactFiles diskMap)) :=
  let layout := layoutFrom 0 0 diskMap
  let initial := FreeSpace.of (joinTouching layout.snd)
  rewrite List.mapAccumLeftList layout.fst.reverse initial FreeSpace.moveFile in
    allZipWith MovedLeft (file free => (FreeSpace.moveFile free file).snd) (file free => moveFileLeft free file) layout.fst.reverse
      (List.scanLeft layout.fst.reverse initial (free file => (free.moveFile file).fst))

theorem moveFileBlocks (free: FreeSpace) (file: File): (free.moveFile file).snd.blocks = file.blocks :=
  match fit: free.leftmostFit file.span.length file.span.start with
    | None => rfl
    | Some span => rfl

-- The moved files have the blocks the files had, highest number first.
theorem movedBlocks (diskMap: List Nat): (compactFiles diskMap).flatMap .blocks = (filesOf diskMap).reverse.flatMap .blocks :=
  let layout := layoutFrom 0 0 diskMap
  let initial := FreeSpace.of (joinTouching layout.snd)
  rewrite List.mapAccumLeftList layout.fst.reverse initial FreeSpace.moveFile in
    Eq.cong List.concat
      (List.mapZipWithScanLeft File.blocks File.blocks (file free => (FreeSpace.moveFile free file).snd) (file free => moveFileBlocks free file)
        layout.fst.reverse initial (free file => (FreeSpace.moveFile free file).fst))

theorem fileBlocksReplicate: (n: Nat) → (id: Nat) → fileBlocks (List.replicate n (Some id)) = List.replicate n id
  | Zero, id => rfl
  | Succ n, id => Eq.cong (Cons id) (fileBlocksReplicate n id)

theorem fileBlocksReplicateFree: (n: Nat) → fileBlocks (List.replicate n None) = Nil
  | Zero => rfl
  | Succ n => fileBlocksReplicateFree n

-- The files' blocks are the disk's file blocks.
theorem layoutBlocks: (id: Nat) → (position: Nat) → (diskMap: List Nat) →
    (layoutFrom id position diskMap).fst.flatMap .blocks = fileBlocks (blocksFrom id diskMap)
  | id, position, Nil => rfl
  | id, position, Cons fileLength Nil => rewrite fileBlocksReplicate fileLength id in List.appendNil (List.replicate fileLength id)
  | id, position, Cons fileLength (Cons freeLength rest) =>
    rewrite List.filterMapAppend (List.replicate fileLength (Some id)) (List.replicate freeLength None ++ blocksFrom (Succ id) rest) (block => block),
      List.filterMapAppend (List.replicate freeLength None) (blocksFrom (Succ id) rest) (block => block),
      fileBlocksReplicate fileLength id, fileBlocksReplicateFree freeLength
      in Eq.cong (List.append (List.replicate fileLength id)) (layoutBlocks (Succ id) (position + fileLength + freeLength) rest)

-- Part 2 keeps the file blocks: after the moves, the disk holds the same
-- file blocks as before, in some order.
theorem part2KeepsBlocks (diskMap: List Nat): List.Perm ((compactFiles diskMap).flatMap .blocks) (fileBlocks (blocks diskMap)) :=
  rewrite movedBlocks diskMap, <- layoutBlocks 0 0 diskMap in List.permFlatMapReverse File.blocks (filesOf diskMap)

-- One block's part of the program's checksum.
def blockChecksum (pair: (Nat, Option Nat)): Nat := pair.snd.map (id => pair.fst * id) |> .getOrElse 0

-- Free blocks add nothing to the checksum; they shift what follows.
theorem checksumSkipFree (rest: List (Option Nat)): (free: Nat) → (from: Nat) →
    (List.withIndexFrom from (List.replicate free None ++ rest)).sumBy blockChecksum = (List.withIndexFrom (free + from) rest).sumBy blockChecksum
  | Zero, from => rfl
  | Succ free, from =>
    rewrite List.sumByCons (List.withIndexFrom (Succ from) (List.replicate free None ++ rest)) (MkPair from None) blockChecksum,
      checksumSkipFree rest free (Succ from), (omega: free + Succ from = Succ free + from) in rfl

-- A file's blocks add their positions times its number.
theorem checksumFileRun (id: Nat): (length: Nat) → (from: Nat) →
    (List.withIndexFrom from (List.replicate length (Some id))).sumBy blockChecksum = (List.rangeFrom length from).sumBy (position => position * id)
  | Zero, from => rfl
  | Succ length, from =>
    rewrite List.sumByCons (List.withIndexFrom (Succ from) (List.replicate length (Some id))) (MkPair from (Some id)) blockChecksum,
      List.sumByCons (List.rangeFrom length (Succ from)) from (position => position * id), checksumFileRun id length (Succ from) in rfl

-- A file's part of the checksum is the puzzle's checksum of a disk with just
-- that file, where it is.
theorem fileChecksumCorrect (file: File):
    file.checksum = filesystemChecksum (List.replicate file.span.start None ++ List.replicate file.span.length (Some file.id)) :=
  rewrite <- checksumCorrect (List.replicate file.span.start None ++ List.replicate file.span.length (Some file.id)) in
    Eq.sym (Eq.trans (checksumSkipFree (List.replicate file.span.length (Some file.id)) file.span.start 0)
      (rewrite Nat.addZero file.span.start in checksumFileRun file.id file.span.length file.span.start))
