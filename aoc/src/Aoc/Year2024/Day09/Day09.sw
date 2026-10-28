-- Advent of Code 2024, day 9: a disk map, one line of digits that alternate
-- between the length of a file and the length of the free space after it
-- ("12345" is a one-block file, two free blocks, a three-block file, four
-- free blocks, a five-block file). The files are numbered 0, 1, 2, ... in
-- order. Part 1 moves file blocks one at a time from the end of the disk into
-- the leftmost free block; part 2 moves whole files, highest number first,
-- into the leftmost free span to their left that fits. Each part's answer is
-- the checksum: the sum of each block's position times its file's number.
--
--   $ cd aoc && stitchwort run Aoc.Year2024.Day09.main < inputs/2024/day09.txt
--
-- The proofs are in `Aoc.Year2024.Day09.Proofs` (Proofs/) and the tests in
-- `Aoc.Year2024.Day09.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2024.Day09
import Std (Fail, IO, List, Map, Nat, Option, Parse, Set, Text)
import Std.Parse (digit, many1)

def main(): {IO, Fail} () :=
  let diskMap := parseDiskMap IO.readAll()
  IO.print "Part 1: ${solvePart1 diskMap}"
  IO.print "Part 2: ${solvePart2 diskMap}"

-- The disk map's digits: a file's length, the free space after it, the next
-- file's length, and so on, ending with either.
def diskMapLine(): {Parse} (List Nat) := many1 (() => digit().toNat)

-- One line of digits.
def parseDiskMap (input: Text): {Fail} (List Nat) := Parse.all input diskMapLine

-- A block holds `Some id`, a block of file `id`, or `None`, free space.
-- The blocks of the disk map's files from number `id` on, left to right.
def blocksFrom (id: Nat): List Nat → List (Option Nat)
  | Nil => Nil
  | Cons fileLength Nil => List.replicate fileLength (Some id)
  | Cons fileLength (Cons freeLength rest) =>
    List.replicate fileLength (Some id) ++ List.replicate freeLength None ++ blocksFrom (Succ id) rest

-- The disk's blocks: "00...111...2...333.44.5555.6666.777.888899".
def blocks (diskMap: List Nat): List (Option Nat) := blocksFrom 0 diskMap

-- The file numbers of the file blocks, left to right.
def fileBlocks (blocks: List (Option Nat)): List Nat := blocks.filterMap (block => block)

-- Part 1's compaction, front to back: of the first `count` blocks, a file
-- block stays and a free one takes the next block of `moving`; the rest are
-- free.
def fillFront: (blocks: List (Option Nat)) → (moving: List Nat) → (count: Nat) → List (Option Nat)
  | blocks, moving, Zero => List.replicate blocks.length None
  | Nil, moving, Succ count => Nil
  | Cons (Some id) rest, moving, Succ count => Cons (Some id) (fillFront rest moving count)
  | Cons None rest, Nil, Succ count => Cons None (fillFront rest Nil count)
  | Cons None rest, Cons id moving, Succ count => Cons (Some id) (fillFront rest moving count)

-- The disk after part 1: as many blocks as there are file blocks keep their
-- files at the front, and the gaps among them take the last file blocks,
-- last first.
def compactBlocks (blocks: List (Option Nat)): List (Option Nat) :=
  let files := fileBlocks blocks
  fillFront blocks files.reverse files.length

-- Each file block's position times its file number, added up.
def checksum (blocks: List (Option Nat)): Nat :=
  blocks.withIndex |> .sumBy (pair => pair.snd.map (id => pair.fst * id) |> .getOrElse 0)

def solvePart1 (diskMap: List Nat): Nat := blocks diskMap |> compactBlocks |> checksum

-- A run of blocks: a file's or a free span's.
type Span = { start: Nat, length: Nat }

type File = { id: Nat, span: Span }

-- The files and the free spans of the disk map, from file `id` at block
-- `position` on.
def layoutFrom (id: Nat) (position: Nat): List Nat → (List File, List Span)
  | Nil => (Nil, Nil)
  | Cons fileLength Nil => ([{ id, span = { start = position, length = fileLength } }], Nil)
  | Cons fileLength (Cons freeLength rest) =>
    let later := layoutFrom (Succ id) (position + fileLength + freeLength) rest
    (
      Cons ({ id, span = { start = position, length = fileLength } }) later.fst,
      Cons ({ start = position + fileLength, length = freeLength }) later.snd
    )

-- Free spans that touch, either side of a file of length 0, joined into one.
def joinTouching (spans: List Span): List Span :=
  spans.foldRight Nil (earlier joined =>
    match joined with
      | Cons next rest =>
        if earlier.start + earlier.length == next.start then Cons ({ start = earlier.start, length = earlier.length + next.length }) rest
        else Cons earlier joined
      | Nil => [earlier])

-- The free spans' starts, by length. Spans of length 0 are left out.
def FreeSpace: Type := Map Nat (Set Nat)

def FreeSpace.add (free: FreeSpace) (span: Span): FreeSpace :=
  if span.length == 0 then free
  else free.alter span.length (starts => starts.getOrElse Set.empty |> .insert span.start |> Some)

def FreeSpace.remove (free: FreeSpace) (span: Span): FreeSpace := free.adjust span.length (starts => starts.remove span.start)

def FreeSpace.of (spans: List Span): FreeSpace := spans.foldLeft Map.empty FreeSpace.add

-- The leftmost free span at least `length` long that starts before `before`.
def FreeSpace.leftmostFit (free: FreeSpace) (length: Nat) (before: Nat): Option Span :=
  free.toList
    |> .filterMap (entry => if length <= entry.fst then entry.snd.min |> .map (start => ({ start, length = entry.fst }: Span)) else None)
    |> .minBy (span => span.start)
    |> .filter (span => span.start < before)

-- Moves `file` into the leftmost free span to its left that fits, if there
-- is one: it takes the span's first blocks, and the rest of the span stays
-- free. The space the file leaves is to the right of every file still to
-- move, so it isn't added.
def moveFile (free: FreeSpace) (file: File): (FreeSpace, File) :=
  match free.leftmostFit file.span.length file.span.start with
    | None => (free, file)
    | Some span =>
      let rest: Span := { start = span.start + file.span.length, length = span.length - file.span.length }
      (free.remove span |> .add rest, { file | span = { file.span | start = span.start } })

-- Every file moved once, highest number first.
def compactFiles (diskMap: List Nat): List File :=
  let layout := layoutFrom 0 0 diskMap
  layout.fst.reverse.mapAccumLeft (FreeSpace.of (joinTouching layout.snd)) moveFile |> .snd

-- A file's part of the checksum.
def fileChecksum (file: File): Nat := List.range file.span.length |> .sumBy (offset => (file.span.start + offset) * file.id)

def solvePart2 (diskMap: List Nat): Nat := compactFiles diskMap |> .sumBy fileChecksum
