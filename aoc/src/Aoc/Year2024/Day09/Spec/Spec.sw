-- Day 9 as the puzzle states it, block by block. The disk's blocks are the
-- program's `blocks`: "the digits alternate between indicating the length of
-- a file and the length of free space", and each file has "an ID number
-- based on the order of the files as they appear", from 0. The proofs
-- (Proofs/) show part 1 computes `part1`, for every disk map.

namespace Aoc.Year2024.Day09.Spec
import Aoc.Year2024.Day09 (..)
import Std (List, Nat, Option)

-- "To calculate the checksum, add up the result of multiplying each of these
-- blocks' position with the file ID number it contains. The leftmost block is
-- in position 0. If a block contains free space, skip it instead."
def filesystemChecksum (blocks: List (Option Nat)): Nat :=
  blocks.withIndex |> .filterMap (pair => pair.snd.map (id => pair.fst * id)) |> .sum

-- The last file block's file, and the blocks with that block made free.
-- `None` when there is no file block.
def takeLastFileBlock: List (Option Nat) → Option (Nat, List (Option Nat))
  | Nil => None
  | Cons block rest =>
    match takeLastFileBlock rest with
      | Some (id, freed) => Some (id, Cons block freed)
      | None =>
        match block with
          | Some id => Some (id, Cons None rest)
          | None => None

-- Part 1's one move: "move file blocks one at a time from the end of the
-- disk to the leftmost free space block". Past the file blocks at the front,
-- the leftmost free block takes the last file block, if there is one after
-- it.
def moveLastBlock: List (Option Nat) → List (Option Nat)
  | Nil => Nil
  | Cons (Some id) rest => Cons (Some id) (moveLastBlock rest)
  | Cons None rest =>
    match takeLastFileBlock rest with
      | Some (id, freed) => Cons (Some id) freed
      | None => Cons None rest

-- A gap between file blocks: a free block with a file block after it.
def hasGap: List (Option Nat) → Bool
  | Nil => False
  | Cons (Some id) rest => hasGap rest
  | Cons None rest => rest.any (block => block.isSome)

-- "Until there are no gaps remaining between file blocks", for at most
-- `moves` moves. The proofs show the disk's length is enough moves.
def compactOneAtATime: (moves: Nat) → List (Option Nat) → List (Option Nat)
  | Zero, blocks => blocks
  | Succ moves, blocks => if hasGap blocks then compactOneAtATime moves (moveLastBlock blocks) else blocks

def part1 (diskMap: List Nat): Nat :=
  let disk := blocks diskMap
  compactOneAtATime disk.length disk |> filesystemChecksum

-- The first position of file `id`'s blocks.
def fileStart (blocks: List (Option Nat)) (id: Nat): Option Nat := blocks.findIndex (block => block == Some id)

-- Whether the `length` blocks from `start` are all free.
def freeAt (blocks: List (Option Nat)) (start: Nat) (length: Nat): Bool :=
  blocks.drop start |> .take length |> .all (block => block == None)

-- Part 2's one move: "attempt to move whole files to the leftmost span of
-- free space blocks that could fit the file". "If there is no span of free
-- space to the left of a file that is large enough to fit the file, the file
-- does not move."
def moveWholeFile (blocks: List (Option Nat)) (id: Nat): List (Option Nat) :=
  match fileStart blocks id with
    | None => blocks
    | Some start =>
      let length := blocks.count (block => block == Some id)
      let fits := List.range start |> .find (target => target + length <= start && freeAt blocks target length)
      match fits with
        | None => blocks
        | Some target =>
          blocks.mapWithIndex (position block =>
            if target <= position && position < target + length then Some id
            else if block == Some id then None
            else block)

-- "Attempt to move each file exactly once in order of decreasing file ID
-- number starting with the file with the highest file ID number."
def compactWholeFiles (diskMap: List Nat) (blocks: List (Option Nat)): List (Option Nat) :=
  let fileCount := (diskMap.length + 1) / 2
  List.range fileCount |> .reverse |> .foldLeft blocks moveWholeFile

def part2 (diskMap: List Nat): Nat := compactWholeFiles diskMap (blocks diskMap) |> filesystemChecksum
