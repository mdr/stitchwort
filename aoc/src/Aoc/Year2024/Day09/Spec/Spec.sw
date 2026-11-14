--| Day 9 as the puzzle states it, block by block. The disk's blocks are the
--| program's `DiskMap.blocks`: "the digits alternate between indicating the
--| length of a file and the length of free space", and each file has "an ID
--| number based on the order of the files as they appear", from 0. The proofs
--| (Proofs/) show part 1 computes `part1`, for every disk map.

namespace Aoc.Year2024.Day09.Spec
import Aoc.Year2024.Day09 (..)
import Std (List, Nat, Option)

--| "To calculate the checksum, add up the result of multiplying each of these
--| blocks' position with the file ID number it contains. The leftmost block is
--| in position 0. If a block contains free space, skip it instead."
def filesystemChecksum (disk: Disk): Nat :=
  disk.blocks.withIndex |> .filterMap (pair => pair.snd.id.map (id => pair.fst * id)) |> .sum

--| The file of the last file block, if there is a file block.
def lastFile: List Block → Option Nat
  | [] => None
  | [block, ..rest] => (lastFile rest).orElse block.id

--| The blocks with the last file block made free.
def freeLastFileBlock: List Block → List Block
  | [] => []
  | [block, ..rest] => if (lastFile rest).isSome then [block, ..freeLastFileBlock rest] else [Free, ..rest]

--| Part 1's one move: "move file blocks one at a time from the end of the
--| disk to the leftmost free space block". Past the file blocks at the front,
--| the leftmost free block takes the last file block, if there is one after
--| it.
def moveLastBlock: List Block → List Block
  | [] => []
  | [FileBlock id, ..rest] => [FileBlock id, ..moveLastBlock rest]
  | [Free, ..rest] =>
    match lastFile rest with
      | Some id => [FileBlock id, ..freeLastFileBlock rest]
      | None => [Free, ..rest]

--| A gap between file blocks: a free block with a file block after it.
def hasGap: List Block → Bool
  | [] => False
  | [FileBlock id, ..rest] => hasGap rest
  | [Free, ..rest] => rest.any .isFile

--| "Until there are no gaps remaining between file blocks", for at most
--| `moves` moves. The proofs show the disk's length is enough moves.
def compactOneAtATime: (moves: Nat) → List Block → List Block
  | Zero, blocks => blocks
  | Succ moves, blocks => if hasGap blocks then compactOneAtATime moves (moveLastBlock blocks) else blocks

def part1 (diskMap: DiskMap): Nat :=
  let blocks := diskMap.blocks.blocks
  filesystemChecksum { blocks = compactOneAtATime blocks.length blocks }

--| The first position of file `id`'s blocks.
def Disk.fileStart (disk: Disk) (id: Nat): Option Nat := disk.blocks.findIndex (block => block == FileBlock id)

--| Whether the `length` blocks from `start` are all free.
def Disk.freeAt (disk: Disk) (start length: Nat): Bool := disk.blocks.drop start |> .take length |> .all .isFree

--| Part 2's one move: "attempt to move whole files to the leftmost span of
--| free space blocks that could fit the file". "If there is no span of free
--| space to the left of a file that is large enough to fit the file, the file
--| does not move."
def Disk.moveWholeFile (disk: Disk) (id: Nat): Disk := match disk.fileStart id with
  | None => disk
  | Some start =>
    let length := disk.blocks.count (block => block == FileBlock id)
    let fits := List.range 0 start |> .find (target => target + length <= start && disk.freeAt target length)
    match fits with
      | None => disk
      | Some target => {
        blocks = disk.blocks.mapWithIndex (position block =>
          if target <= position < target + length then FileBlock id else if block == FileBlock id then Free else block)
      }

--| "Attempt to move each file exactly once in order of decreasing file ID
--| number starting with the file with the highest file ID number."
def Disk.compactWholeFiles (disk: Disk) (diskMap: DiskMap): Disk :=
  let fileCount := (diskMap.lengths.length + 1) / 2
  List.range 0 fileCount |> .reverse |> .foldLeft disk Disk.moveWholeFile

def part2 (diskMap: DiskMap): Nat := diskMap.blocks.compactWholeFiles diskMap |> filesystemChecksum
