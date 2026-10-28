-- Part 1 proved, for every disk map: the program's front-to-back fill is
-- the puzzle's moves, one block at a time, until there are no gaps, and the
-- disk's length is enough moves.

namespace Aoc.Year2024.Day09.Proofs
import Aoc.Year2024.Day09 (..)
import Aoc.Year2024.Day09.Spec (..)
import Std (Eq, List, Nat, Option, Void)

-- How many file blocks there are.
def fileCount (blocks: List (Option Nat)): Nat := (fileBlocks blocks).length

-- Freeing the last file block keeps the disk's length.
theorem lengthFreeLast: (blocks: List (Option Nat)) → (freeLastFileBlock blocks).length = blocks.length
  | Nil => rfl
  | Cons block rest =>
    match later: lastFile rest with
      | Some id => Eq.cong Succ (lengthFreeLast rest)
      | None => rfl

-- No last file: every block is free.
theorem noLastFile: (blocks: List (Option Nat)) → lastFile blocks = None → blocks = List.replicate blocks.length None
  | Nil, none => rfl
  | Cons block rest, none =>
    match later: lastFile rest with
      | Some id => Void.exfalso (Option.someNotNone id none)
      | None =>
        match block with
          | Some id => Void.exfalso (Option.someNotNone id none)
          | None => Eq.cong (Cons None) (noLastFile rest later)

-- No last file: no file blocks.
theorem noFileBlocks: (blocks: List (Option Nat)) → lastFile blocks = None → fileBlocks blocks = Nil
  | Nil, none => rfl
  | Cons block rest, none =>
    match later: lastFile rest with
      | Some id => Void.exfalso (Option.someNotNone id none)
      | None =>
        match block with
          | Some id => Void.exfalso (Option.someNotNone id none)
          | None => noFileBlocks rest later

-- The last file block is the last of the file blocks; freeing it leaves the
-- others.
theorem fileBlocksFreeLast: (blocks: List (Option Nat)) → (id: Nat) → lastFile blocks = Some id →
    fileBlocks blocks = (fileBlocks (freeLastFileBlock blocks)).append [id]
  | Nil, id, found => Void.exfalso (Option.noneNotSome id found)
  | Cons block rest, id, found =>
    match later: lastFile rest with
      | Some laterId =>
        rewrite fileBlocksFreeLast rest laterId later, Option.someInjective laterId id found in
          match block with
            | Some here => rfl
            | None => rfl
      | None =>
        match block with
          | Some here => rewrite noFileBlocks rest later, Option.someInjective here id found in rfl
          | None => Void.exfalso (Option.noneNotSome id found)

-- Some block is a file block exactly when there is a last file.
theorem anyFileBlock: (blocks: List (Option Nat)) → blocks.any (block => block.isSome) = (lastFile blocks).isSome
  | Nil => rfl
  | Cons block rest =>
    rewrite anyFileBlock rest in
      match later: lastFile rest with
        | Some id =>
          match block with
            | Some here => rfl
            | None => rfl
        | None =>
          match block with
            | Some here => rfl
            | None => rfl

-- More blocks to move than `fillFront` uses change nothing.
theorem fillFrontAppend: (blocks: List (Option Nat)) → (moving: List Nat) → (extra: List Nat) → (count: Nat) → count ≤ moving.length →
    fillFront blocks (moving.append extra) count = fillFront blocks moving count
  | blocks, moving, extra, Zero, enough => rfl
  | Nil, moving, extra, Succ count, enough => rfl
  | Cons (Some id) rest, moving, extra, Succ count, enough => Eq.cong (Cons (Some id)) (fillFrontAppend rest moving extra count (omega))
  | Cons None rest, Nil, extra, Succ count, enough => Void.exfalso (omega)
  | Cons None rest, Cons id moving, extra, Succ count, enough =>
    Eq.cong (Cons (Some id)) (fillFrontAppend rest moving extra count (omega))

-- `fillFront` doesn't look past the first `count` blocks: freeing the last
-- file block changes nothing when there are `count` file blocks before it.
theorem fillFrontFreeLast: (blocks: List (Option Nat)) → (moving: List Nat) → (count: Nat) → count ≤ fileCount (freeLastFileBlock blocks) →
    fillFront blocks moving count = fillFront (freeLastFileBlock blocks) moving count
  | blocks, moving, Zero, bound => rewrite lengthFreeLast blocks in rfl
  | Nil, moving, Succ count, bound => rfl
  | Cons block rest, moving, Succ count, bound =>
    match later: lastFile rest with
      | Some id =>
        match block with
          | Some here => Eq.cong (Cons (Some here)) (fillFrontFreeLast rest moving count (omega))
          | None =>
            match moving with
              | Nil => Eq.cong (Cons None) (fillFrontFreeLast rest Nil count (omega))
              | Cons next others => Eq.cong (Cons (Some next)) (fillFrontFreeLast rest others count (omega))
      | None => Void.exfalso (rewrite noFileBlocks rest later at bound in omega)

-- A file block at the front stays there.
theorem compactFile (id: Nat) (rest: List (Option Nat)): compactBlocks (Cons (Some id) rest) = Cons (Some id) (compactBlocks rest) :=
  rewrite List.reverseCons id (fileBlocks rest) in
    Eq.cong (Cons (Some id))
      (fillFrontAppend rest (fileBlocks rest).reverse [id] (fileBlocks rest).length (rewrite List.lengthReverse (fileBlocks rest) in omega))

-- A free block at the front takes the last file block.
theorem compactGap (rest: List (Option Nat)) (id: Nat) (found: lastFile rest = Some id):
    compactBlocks (Cons None rest) = Cons (Some id) (compactBlocks (freeLastFileBlock rest)) :=
  let others := fileBlocks (freeLastFileBlock rest)
  rewrite fileBlocksFreeLast rest id found, List.reverseSnoc others id, List.lengthSnoc others id in
    Eq.cong (Cons (Some id)) (fillFrontFreeLast rest others.reverse others.length (Nat.leRefl others.length))

-- Free blocks with no file block after them stay free.
theorem compactFree (rest: List (Option Nat)) (none: lastFile rest = None): compactBlocks (Cons None rest) = Cons None rest :=
  rewrite noFileBlocks rest none in Eq.cong (Cons None) (Eq.sym (noLastFile rest none))

-- Moves past a file block at the front happen behind it.
theorem stepsPastFile (id: Nat) (rest: List (Option Nat)): (moves: Nat) →
    compactOneAtATime moves (Cons (Some id) rest) = Cons (Some id) (compactOneAtATime moves rest)
  | Zero => rfl
  | Succ moves =>
    match gap: hasGap rest with
      | True => stepsPastFile id (moveLastBlock rest) moves
      | False => rfl

-- With at least as many moves as blocks, the moves end where the program's
-- fill does.
theorem stepsFill (moves: Nat) (blocks: List (Option Nat)) (enough: blocks.length ≤ moves):
    compactOneAtATime moves blocks = compactBlocks blocks
    decreasing blocks.length
:=
  match blocks with
    | Nil =>
      match moves with
        | Zero => rfl
        | Succ fewer => rfl
    | Cons (Some id) rest =>
      rewrite stepsPastFile id rest moves, compactFile id rest in
        Eq.cong (Cons (Some id)) (stepsFill moves rest (omega))
    | Cons None rest =>
      match moves with
        | Zero => Void.exfalso (omega)
        | Succ fewer =>
          match later: lastFile rest with
            | Some id =>
              let freedLength := lengthFreeLast rest
              rewrite anyFileBlock rest, later, stepsPastFile id (freeLastFileBlock rest) fewer, compactGap rest id later
                in Eq.cong (Cons (Some id)) (stepsFill fewer (freeLastFileBlock rest) (omega))
            | None => rewrite anyFileBlock rest, later, compactFree rest later in rfl

-- The fill leaves no gaps.
theorem fillNoGaps (blocks: List (Option Nat)): hasGap (compactBlocks blocks) = False
    decreasing blocks.length
:=
  match blocks with
    | Nil => rfl
    | Cons (Some id) rest => Eq.trans (Eq.cong hasGap (compactFile id rest)) (fillNoGaps rest)
    | Cons None rest =>
      match later: lastFile rest with
        | Some id =>
          let freedLength := lengthFreeLast rest
          rewrite compactGap rest id later in fillNoGaps (freeLastFileBlock rest)
        | None => rewrite compactFree rest later, anyFileBlock rest, later in rfl

-- The program's checksum is the puzzle's.
theorem checksumCorrect (blocks: List (Option Nat)): checksum blocks = filesystemChecksum blocks :=
  Eq.sym (List.sumFilterMap (pair => pair.snd.map (id => pair.fst * id)) blocks.withIndex)

-- Part 1 is the puzzle's moves, one block at a time, then the checksum.
theorem part1Correct (diskMap: List Nat): solvePart1 diskMap = part1 diskMap :=
  let disk := blocks diskMap
  rewrite stepsFill disk.length disk (Nat.leRefl disk.length) in checksumCorrect (compactBlocks disk)

-- The disk's length is enough moves: none are left to make.
theorem part1NoGapsLeft (diskMap: List Nat): hasGap (compactOneAtATime (blocks diskMap).length (blocks diskMap)) = False :=
  let disk := blocks diskMap
  rewrite stepsFill disk.length disk (Nat.leRefl disk.length) in fillNoGaps disk
