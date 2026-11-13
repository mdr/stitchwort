--| Part 2 proved in part, for every disk map: each file is moved once, keeps
--| its number and length, and moves only leftwards, so the disk holds the
--| same file blocks. Not proved: that a file lands on free blocks, that the
--| span it lands in is the leftmost that fits, and so that part 2 is the
--| spec's `part2`; the tests check that on small disks.

namespace Aoc.Year2024.Day09.Proofs
import Aoc.Year2024.Day09 (..)
import Aoc.Year2024.Day09.Spec (..)
import Std (Eq, List, Nat, Option, Void)

--| The disk map's files where they start.
def filesOf (diskMap: DiskMap): List File := (layoutFrom 0 0 diskMap.lengths).fst

--| What a move keeps: the file's number and length.
def File.idAndLength (file: File): (Nat, Nat) := (file.id, file.span.length)

--| A file's blocks.
def File.blocks (file: File): List Nat := List.replicate file.span.length file.id

--| `after` is `before`, moved left or not at all.
def MovedLeft (before: File) (after: File): Prop :=
  after.id = before.id ∧ after.span.length = before.span.length ∧ after.span.start ≤ before.span.start

--| The span found starts before `before`.
theorem fitBefore (free: FreeSpace) (length: Nat) (before: Nat) (span: Span) (fit: free.leftmostFit length before = Some span): span.start < before :=
  And.right (Option.filterEqSome _ ((found: Span) => found.start < before) fit)

--| A move keeps the file's number and length, and goes left if anywhere.
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

--| The files are moved once each, highest number first, and keep their
--| numbers and lengths.
theorem eachFileOnce (diskMap: DiskMap): (compactFiles diskMap).map .idAndLength = (filesOf diskMap).reverse.map .idAndLength :=
  let layout := layoutFrom 0 0 diskMap.lengths
  let initial := FreeSpace.of (joinTouching layout.snd)
  rewrite List.mapAccumLeftList layout.fst.reverse initial FreeSpace.moveFile in
    List.mapZipWithScanLeft File.idAndLength File.idAndLength (file free => (free.moveFile file).snd) (file free => moveFileKeeps free file)
      layout.fst.reverse initial (free file => (free.moveFile file).fst)

--| Each file moves left or stays.
theorem filesMoveLeft (diskMap: DiskMap):
    List.All (pair => MovedLeft pair.fst pair.snd) (List.zip (filesOf diskMap).reverse (compactFiles diskMap)) :=
  let layout := layoutFrom 0 0 diskMap.lengths
  let initial := FreeSpace.of (joinTouching layout.snd)
  rewrite List.mapAccumLeftList layout.fst.reverse initial FreeSpace.moveFile in
    List.allZipWithSelf MovedLeft (file free => (free.moveFile file).snd) (file free => moveFileLeft free file) layout.fst.reverse
      (List.scanLeft layout.fst.reverse initial (free file => (free.moveFile file).fst))

theorem moveFileBlocks (free: FreeSpace) (file: File): (free.moveFile file).snd.blocks = file.blocks :=
  match fit: free.leftmostFit file.span.length file.span.start with
    | None => rfl
    | Some span => rfl

--| The moved files have the blocks the files had, highest number first.
theorem movedBlocks (diskMap: DiskMap): (compactFiles diskMap).flatMap .blocks = (filesOf diskMap).reverse.flatMap .blocks :=
  let layout := layoutFrom 0 0 diskMap.lengths
  let initial := FreeSpace.of (joinTouching layout.snd)
  rewrite List.mapAccumLeftList layout.fst.reverse initial FreeSpace.moveFile in
    Eq.trans (List.flatMapEqConcatMap File.blocks _)
      (Eq.trans
        (Eq.cong List.concat
          (List.mapZipWithScanLeft File.blocks File.blocks (file free => (free.moveFile file).snd) (file free => moveFileBlocks free file)
            layout.fst.reverse initial (free file => (free.moveFile file).fst)))
        (Eq.sym (List.flatMapEqConcatMap File.blocks _)))

theorem fileBlocksReplicate (n id: Nat): fileBlocks (List.replicate n (FileBlock id)) = List.replicate n id :=
  match n with
    | Zero => rfl
    | Succ n => Eq.cong (Cons id) (fileBlocksReplicate n id)

theorem fileBlocksReplicateFree (n: Nat): fileBlocks (List.replicate n Free) = [] := match n with
  | Zero => rfl
  | Succ n => fileBlocksReplicateFree n

--| The files' blocks are the disk's file blocks.
theorem layoutBlocks (id position: Nat) (diskMap: List Nat):
    (layoutFrom id position diskMap).fst.flatMap .blocks = fileBlocks (blocksFrom id diskMap) := match diskMap with
      | [] => rfl
      | [fileLength] => rewrite fileBlocksReplicate fileLength id in List.appendNil (List.replicate fileLength id)
      | [fileLength, freeLength, ..rest] =>
        rewrite List.filterMapAppend (List.replicate fileLength (FileBlock id)) (List.replicate freeLength Free ++ blocksFrom (Succ id) rest) Block.id,
          List.filterMapAppend (List.replicate freeLength Free) (blocksFrom (Succ id) rest) Block.id,
          fileBlocksReplicate fileLength id, fileBlocksReplicateFree freeLength
          in Eq.cong (List.append (List.replicate fileLength id)) (layoutBlocks (Succ id) (position + fileLength + freeLength) rest)

--| Part 2 keeps the file blocks: after the moves, the disk holds the same
--| file blocks as before, in some order.
theorem part2KeepsBlocks (diskMap: DiskMap): List.Perm ((compactFiles diskMap).flatMap .blocks) (fileBlocks diskMap.blocks.blocks) :=
  rewrite movedBlocks diskMap, <- layoutBlocks 0 0 diskMap.lengths in List.permFlatMapReverse File.blocks (filesOf diskMap)

--| One block's part of the program's checksum.
def blockChecksum (pair: (Nat, Block)): Nat := pair.fst * pair.snd.idOr 0

--| A free block adds nothing to the checksum.
theorem blockChecksumFree (position: Nat): blockChecksum (MkPair position Free) = 0 := Nat.mulZero position

--| Free blocks add nothing to the checksum; they shift what follows.
theorem checksumSkipFree (rest: List Block) (free from: Nat):
    (List.withIndexFrom from (List.replicate free Free ++ rest)).sumBy blockChecksum = (List.withIndexFrom (free + from) rest).sumBy blockChecksum :=
  match free with
    | Zero => rfl
    | Succ free =>
      rewrite List.sumByCons (List.withIndexFrom (Succ from) (List.replicate free Free ++ rest)) (MkPair from Free) blockChecksum,
        blockChecksumFree from, checksumSkipFree rest free (Succ from), (omega: free + Succ from = Succ free + from) in rfl

--| A file's blocks add their positions times its number.
theorem checksumFileRun (id: Nat) (length from: Nat):
    (List.withIndexFrom from (List.replicate length (FileBlock id))).sumBy blockChecksum = (List.rangeFrom length from).sumBy (position => position * id) :=
  match length with
    | Zero => rfl
    | Succ length =>
      rewrite List.sumByCons (List.withIndexFrom (Succ from) (List.replicate length (FileBlock id))) (MkPair from (FileBlock id)) blockChecksum,
        List.sumByCons (List.rangeFrom length (Succ from)) from (position => position * id), checksumFileRun id length (Succ from) in rfl

--| A file's part of the checksum is the puzzle's checksum of a disk with just
--| that file, where it is.
theorem fileChecksumCorrect (file: File):
    file.checksum = filesystemChecksum { blocks = List.replicate file.span.start Free ++ List.replicate file.span.length (FileBlock file.id) } :=
  rewrite <- checksumCorrect { blocks = List.replicate file.span.start Free ++ List.replicate file.span.length (FileBlock file.id) } in
    Eq.trans (fileChecksumSpec file)
      (Eq.trans
        (Eq.sym (Eq.trans (checksumSkipFree (List.replicate file.span.length (FileBlock file.id)) file.span.start 0)
          (rewrite Nat.addZero file.span.start in checksumFileRun file.id file.span.length file.span.start)))
        (Eq.sym (checksumSum { blocks = List.replicate file.span.start Free ++ List.replicate file.span.length (FileBlock file.id) })))
