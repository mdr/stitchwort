--| Advent of Code 2024, day 9: a disk map, one line of digits that alternate
--| between the length of a file and the length of the free space after it
--| ("12345" is a one-block file, two free blocks, a three-block file, four
--| free blocks, a five-block file). The files are numbered 0, 1, 2, ... in
--| order. Part 1 moves file blocks one at a time from the end of the disk into
--| the leftmost free block; part 2 moves whole files, highest number first,
--| into the leftmost free span to their left that fits. Each part's answer is
--| the checksum: the sum of each block's position times its file's number.
--|
--|   $ cd aoc && stitchwort run Aoc.Year2024.Day09.main < inputs/2024/day09.txt
--|
--| The proofs are in `Aoc.Year2024.Day09.Proofs` (Proofs/) and the tests in
--| `Aoc.Year2024.Day09.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2024.Day09
import Std (Fail, IO, List, Map, Nat, Option, Parse, Set, Text)
import Std.Parse (digit, many1)

def main(): {IO, Fail} () :=
  let diskMap := parseDiskMap IO.readAll()
  IO.print "Part 1: ${solvePart1 diskMap}"
  IO.print "Part 2: ${solvePart2 diskMap}"

--| The disk map: a file's length, the free space after it, the next file's
--| length, and so on, ending with either.
type DiskMap = { lengths: List Nat }

--| One block of the disk: free space, or a block of file number `id`.
type Block = | Free | FileBlock (id: Nat)

--| The file number of a file block.
def Block.id: Block → Option Nat
  | Free => None
  | FileBlock id => Some id

--| The file number of a file block, or `free` for free space.
def Block.idOr (block: Block) (free: Nat): Nat := block.id.getOrElse free

def Block.isFree: Block → Bool
  | Free => True
  | FileBlock id => False

def Block.isFile (block: Block): Bool := !block.isFree

--| The disk: its blocks, left to right.
type Disk = { blocks: List Block }

--| The disk map's digits.
def diskMapLine(): {Parse} List Nat := many1 (() => digit().toNat) |> .toList

--| One line of digits.
def parseDiskMap (input: Text): {Fail} DiskMap := { lengths = Parse.all input diskMapLine }

--| The blocks of the disk map's files from number `id` on, left to right.
def blocksFrom (id: Nat): List Nat → List Block
  | [] => []
  | [fileLength] => List.replicate fileLength (FileBlock id)
  | [fileLength, freeLength, ..rest] =>
    List.replicate fileLength (FileBlock id) ++ List.replicate freeLength Free ++ blocksFrom (Succ id) rest

--| The disk: "00...111...2...333.44.5555.6666.777.888899".
def DiskMap.blocks (diskMap: DiskMap): Disk := { blocks = blocksFrom 0 diskMap.lengths }

--| The file numbers of the file blocks, left to right.
def fileBlocks (blocks: List Block): List Nat := blocks.filterMap .id

--| Part 1's compaction, front to back: of the first `count` blocks, a file
--| block stays and a free one takes the next block of `moving`; the rest are
--| free.
def fillFront: (blocks: List Block) → (moving: List Nat) → (count: Nat) → List Block
  | blocks, moving, Zero => List.replicate blocks.length Free
  | [], moving, Succ count => []
  | [FileBlock id, ..rest], moving, Succ count => [FileBlock id, ..fillFront rest moving count]
  | [Free, ..rest], [], Succ count => [Free, ..fillFront rest [] count]
  | [Free, ..rest], [id, ..moving], Succ count => [FileBlock id, ..fillFront rest moving count]

--| The blocks after part 1: as many blocks as there are file blocks keep
--| their files at the front, and the gaps among them take the last file
--| blocks, last first.
def compactBlocks (blocks: List Block): List Block :=
  let files := fileBlocks blocks
  fillFront blocks files.reverse files.length

def Disk.compact (disk: Disk): Disk := { blocks = compactBlocks disk.blocks }

--| One block of the checksum, counting positions as it goes: the checksum so
--| far and the block's position, then the checksum with this block's part
--| added and the next position.
def Disk.checksumStep (running: (Nat, Nat)) (block: Block): (Nat, Nat) :=
  (running.fst + running.snd * block.idOr 0, running.snd + 1)

--| Each file block's position times its file number, added up.
def Disk.checksum (disk: Disk): Nat := (disk.blocks.foldLeft (0, 0) Disk.checksumStep).fst

def solvePart1 (diskMap: DiskMap): Nat := diskMap.blocks.compact.checksum

--| A run of blocks: a file's or a free span's.
type Span = { start: Nat, length: Nat }

type File = { id: Nat, span: Span }

--| The files and the free spans of the disk map, from file `id` at block
--| `position` on.
def layoutFrom (id position: Nat): List Nat → (List File, List Span)
  | [] => ([], [])
  | [fileLength] => ([{ id, span = { start = position, length = fileLength } }], [])
  | [fileLength, freeLength, ..rest] =>
    let later := layoutFrom (Succ id) (position + fileLength + freeLength) rest
    (
      [{ id, span = { start = position, length = fileLength } }, ..later.fst],
      [{ start = position + fileLength, length = freeLength }, ..later.snd]
    )

--| Free spans that touch, either side of a file of length 0, joined into one.
def joinTouching (spans: List Span): List Span := spans.foldRight [] (earlier joined =>
  match joined with
    | [next, ..rest] =>
      if earlier.start + earlier.length == next.start then
        [{ start = earlier.start, length = earlier.length + next.length }, ..rest]
      else [earlier, ..joined]
    | [] => [earlier])

--| The free spans' starts, by length. Spans of length 0 are left out.
def FreeSpace: Type := Map Nat (Set Nat)

def FreeSpace.add (free: FreeSpace) (span: Span): FreeSpace :=
  if span.length == 0 then free else free.insertIn span.length span.start

def FreeSpace.remove (free: FreeSpace) (span: Span): FreeSpace := free.removeIn span.length span.start

def FreeSpace.of (spans: List Span): FreeSpace := spans.foldLeft Map.empty FreeSpace.add

--| The leftmost free span at least `length` long that starts before `before`.
def FreeSpace.leftmostFit (free: FreeSpace) (length before: Nat): Option Span :=
  free.toList
    |> .filterMap (entry =>
      if length <= entry.fst then entry.snd.min |> .map (start => ({ start, length = entry.fst }: Span)) else None)
    |> .minBy .start
    |> .filter (.start < before)

--| Moves `file` into the leftmost free span to its left that fits, if there
--| is one: it takes the span's first blocks, and the rest of the span stays
--| free. The space the file leaves is to the right of every file still to
--| move, so it isn't added.
def FreeSpace.moveFile (free: FreeSpace) (file: File): (FreeSpace, File) :=
  match free.leftmostFit file.span.length file.span.start with
    | None => (free, file)
    | Some span =>
      let rest: Span := { start = span.start + file.span.length, length = span.length - file.span.length }
      (free.remove span |> .add rest, { file | span = { file.span | start = span.start } })

--| Every file moved once, highest number first.
def compactFiles (diskMap: DiskMap): List File :=
  let layout := layoutFrom (id := 0) (position := 0) diskMap.lengths
  layout.fst.reverse.mapAccumLeft (FreeSpace.of (joinTouching layout.snd)) FreeSpace.moveFile |> .snd

--| A file's part of the checksum: its blocks' positions times its number
--| (the positions add up by Gauss's rule).
def File.checksum (file: File): Nat :=
  let length := file.span.length
  file.id * (length * file.span.start + length * (length - 1) / 2)

def solvePart2 (diskMap: DiskMap): Nat := compactFiles diskMap |> .sumBy .checksum
