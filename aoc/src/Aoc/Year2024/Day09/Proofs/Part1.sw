--| Part 1 proved, for every disk map: the program's front-to-back fill is
--| the puzzle's moves, one block at a time, until there are no gaps, and the
--| disk's length is enough moves.

namespace Aoc.Year2024.Day09.Proofs
import Aoc.Year2024.Day09 (..)
import Aoc.Year2024.Day09.Spec (..)
import Std (Eq, List, Nat, Option, Void)

--| How many file blocks there are.
def fileCount (blocks: List Block): Nat := (fileBlocks blocks).length

--| Freeing the last file block keeps the disk's length.
theorem lengthFreeLast ∀ (blocks: List Block): (freeLastFileBlock blocks).length = blocks.length := match blocks with
  | [] => byComputing
  | [block, ..rest] =>
    match later: lastFile rest with
      | Some id => Eq.cong Succ (lengthFreeLast rest)
      | None => byComputing

--| No last file: every block is free.
theorem noLastFile ∀ (blocks: List Block) (none: lastFile blocks = None): blocks = List.replicate blocks.length Free :=
  match blocks with
    | [] => byComputing
    | [block, ..rest] =>
      match later: lastFile rest with
        | None =>
          match block with
            | Free => Eq.cong (Cons Free) (noLastFile rest later)

--| No last file: no file blocks.
theorem noFileBlocks ∀ (blocks: List Block) (none: lastFile blocks = None): fileBlocks blocks = [] := match blocks with
  | [] => byComputing
  | [block, ..rest] =>
    match later: lastFile rest with
      | None =>
        match block with
          | Free => noFileBlocks rest later

--| The last file block is the last of the file blocks; freeing it leaves the
--| others.
theorem fileBlocksFreeLast ∀ (blocks: List Block) (id: Nat)
    (found: lastFile blocks = Some id):
    fileBlocks blocks = (fileBlocks (freeLastFileBlock blocks)).append [id] :=
  match blocks with
    | [block, ..rest] =>
      match later: lastFile rest with
        | Some laterId =>
          rewrite fileBlocksFreeLast rest laterId later, Option.someInjective found then
            match block with
              | FileBlock _ | Free => byComputing
        | None =>
          match block with
            | FileBlock here => rewrite noFileBlocks rest later, Option.someInjective found

--| Some block is a file block exactly when there is a last file.
theorem anyFileBlock ∀ (blocks: List Block): blocks.any (block => block.isFile) = (lastFile blocks).isSome :=
  match blocks with
    | [] => byComputing
    | [block, ..rest] =>
      rewrite anyFileBlock rest then
        match later: lastFile rest with
          | Some _ | None =>
            match block with
              | FileBlock _ | Free => byComputing

--| More blocks to move than `fillFront` uses change nothing.
theorem fillFrontAppend ∀ (blocks: List Block) (moving extra: List Nat) (count: Nat)
    (enough: count ≤ moving.length):
    fillFront blocks (moving.append extra) count = fillFront blocks moving count :=
  match blocks, moving, count with
    | blocks, moving, Zero => byComputing
    | [], moving, Succ count => byComputing
    | [FileBlock id, ..rest], moving, Succ count =>
      Eq.cong (Cons (FileBlock id)) (fillFrontAppend rest moving extra count (arithmetic))
    | [Free, ..rest], [id, ..moving], Succ count =>
      Eq.cong (Cons (FileBlock id)) (fillFrontAppend rest moving extra count (arithmetic))

--| `fillFront` doesn't look past the first `count` blocks: freeing the last
--| file block changes nothing when there are `count` file blocks before it.
theorem fillFrontFreeLast ∀ (blocks: List Block) (moving: List Nat) (count: Nat)
    (bound: count ≤ fileCount (freeLastFileBlock blocks)):
    fillFront blocks moving count = fillFront (freeLastFileBlock blocks) moving count :=
  match blocks, count with
    | blocks, Zero => rewrite lengthFreeLast blocks
    | [block, ..rest], Succ count =>
      match later: lastFile rest with
        | Some id =>
          match block with
            | FileBlock here => Eq.cong (Cons (FileBlock here)) (fillFrontFreeLast rest moving count (arithmetic))
            | Free =>
              match moving with
                | [] => Eq.cong (Cons Free) (fillFrontFreeLast rest [] count (arithmetic))
                | [next, ..others] => Eq.cong (Cons (FileBlock next)) (fillFrontFreeLast rest others count (arithmetic))
        | None => Void.impossible (rewrite noFileBlocks rest later at bound then arithmetic)

--| A file block at the front stays there.
theorem compactFile ∀ (id: Nat) (rest: List Block):
    compactBlocks [FileBlock id, ..rest] = [FileBlock id, ..compactBlocks rest] :=
  rewrite List.reverseCons id (fileBlocks rest) then
    Eq.cong
      (Cons (FileBlock id))
      (fillFrontAppend rest
        (fileBlocks rest).reverse
        [id]
        (fileBlocks rest).length
        (rewrite List.lengthReverse (fileBlocks rest) then arithmetic))

--| A free block at the front takes the last file block.
theorem compactGap ∀ (rest: List Block) (id: Nat)
    (found: lastFile rest = Some id):
    compactBlocks [Free, ..rest] = [FileBlock id, ..compactBlocks (freeLastFileBlock rest)] :=
  let others := fileBlocks (freeLastFileBlock rest)
  rewrite fileBlocksFreeLast rest id found, List.reverseSnoc others id, List.lengthSnoc others id then
    Eq.cong (Cons (FileBlock id)) (fillFrontFreeLast rest others.reverse others.length (Nat.leRefl others.length))

--| Free blocks with no file block after them stay free.
theorem compactFree ∀ (rest: List Block) (none: lastFile rest = None): compactBlocks [Free, ..rest] = [Free, ..rest] :=
  rewrite noFileBlocks rest none then Eq.cong (Cons Free) (noLastFile rest none).flipped

--| Moves past a file block at the front happen behind it.
theorem stepsPastFile ∀ (id: Nat) (rest: List Block) (moves: Nat):
    compactOneAtATime moves [FileBlock id, ..rest] = [FileBlock id, ..compactOneAtATime moves rest] :=
  match moves with
    | Zero => byComputing
    | Succ moves =>
      match gap: hasGap rest with
        | True => stepsPastFile id (moveLastBlock rest) moves
        | False => byComputing

--| With at least as many moves as blocks, the moves end where the program's
--| fill does.
theorem stepsFill ∀ (moves: Nat) (blocks: List Block)
    (enough: blocks.length ≤ moves):
    compactOneAtATime moves blocks = compactBlocks blocks
    decreasing blocks.length
:=
  match blocks with
    | [] =>
      match moves with
        | Zero | Succ _ => byComputing
    | [FileBlock id, ..rest] =>
      rewrite stepsPastFile id rest moves, compactFile id rest then
        Eq.cong (Cons (FileBlock id)) (stepsFill moves rest (arithmetic))
    | [Free, ..rest] =>
      match moves with
        | Succ fewer =>
          match later: lastFile rest with
            | Some id =>
              let freedLength := lengthFreeLast rest
              rewrite anyFileBlock rest,
                  later,
                  stepsPastFile id (freeLastFileBlock rest) fewer,
                  compactGap rest id later then
                Eq.cong (Cons (FileBlock id)) (stepsFill fewer (freeLastFileBlock rest) (arithmetic))
            | None => rewrite anyFileBlock rest, later, compactFree rest later

--| The fill leaves no gaps.
theorem fillNoGaps ∀ (blocks: List Block): hasGap (compactBlocks blocks) = False
    decreasing blocks.length
:=
  match blocks with
    | [] => byComputing
    | [FileBlock id, ..rest] => Eq.trans (Eq.cong hasGap (compactFile id rest)) (fillNoGaps rest)
    | [Free, ..rest] =>
      match later: lastFile rest with
        | Some id =>
          let freedLength := lengthFreeLast rest
          rewrite compactGap rest id later then fillNoGaps (freeLastFileBlock rest)
        | None => rewrite compactFree rest later, anyFileBlock rest, later

--| A block's part of the checksum, as the program and as the puzzle say it.
theorem blockChecksumCorrect ∀ (position: Nat) (block: Block):
    position * block.idOr 0 = (block.id.map (id => position * id)).getOrElse 0 :=
  match block with
    | Free => Nat.mulZero position
    | FileBlock id => byComputing

--| The checksum's running pair after some blocks, from any starting total and position.
theorem checksumFold ∀ (blocks: List Block) (total position: Nat):
    blocks.foldLeft (total, position) Disk.checksumStep
      = (
        total + (List.withIndexFrom position blocks).sumBy (pair => pair.fst * pair.snd.idOr 0),
        position + blocks.length
      ) :=
  match blocks with
    | [] => byComputing
    | [block, ..rest] =>
      rewrite checksumFold rest (total + position * block.idOr 0) (Succ position),
          List.sumByCons (List.withIndexFrom (Succ position) rest) (position, block) (pair =>
            pair.fst * pair.snd.idOr 0) then
        let sums: total
          + position * block.idOr 0
          + (List.withIndexFrom (Succ position) rest).sumBy (pair => pair.fst * pair.snd.idOr 0)
          = total
            + (position * block.idOr 0
              + (List.withIndexFrom (Succ position) rest).sumBy (pair => pair.fst * pair.snd.idOr 0)) :=
          algebra
        let lengths: Succ position + rest.length = position + Succ rest.length := algebra
        Eq.cong2 MkPair sums lengths

--| The checksum counted as the program does is the sum over the indexed blocks.
theorem checksumSum ∀ (disk: Disk): disk.checksum = disk.blocks.withIndex.sumBy (pair => pair.fst * pair.snd.idOr 0) :=
  rewrite checksumFold disk.blocks 0 0 then algebra

--| The program's checksum is the puzzle's.
theorem checksumCorrect ∀ (disk: Disk): disk.checksum = filesystemChecksum disk := calc disk.checksum
  _ = disk.blocks.withIndex.sumBy (pair => pair.fst * pair.snd.idOr 0) := checksumSum disk
  _ = disk.blocks.withIndex.sumBy (pair => Option.getOrElse (Option.map pair.snd.id (id => pair.fst * id)) 0) :=
    List.sumByCongMem disk.blocks.withIndex
      (pair => pair.fst * pair.snd.idOr 0)
      (pair => Option.getOrElse (Option.map pair.snd.id (id => pair.fst * id)) 0)
      (pair member => blockChecksumCorrect pair.fst pair.snd)
  _ = filesystemChecksum disk :=
    Eq.flipped (List.sumFilterMap (pair => pair.snd.id.map (id => pair.fst * id)) disk.blocks.withIndex)

--| Part 1 is the puzzle's moves, one block at a time, then the checksum.
theorem part1Correct ∀ (diskMap: DiskMap): solvePart1 diskMap = part1 diskMap :=
  let blocks := diskMap.blocks.blocks
  rewrite stepsFill blocks.length blocks (Nat.leRefl blocks.length) then
    checksumCorrect { blocks = compactBlocks blocks }

--| The disk's length is enough moves: none are left to make.
theorem part1NoGapsLeft ∀ (diskMap: DiskMap):
    hasGap (compactOneAtATime diskMap.blocks.blocks.length diskMap.blocks.blocks) = False :=
  let blocks := diskMap.blocks.blocks
  rewrite stepsFill blocks.length blocks (Nat.leRefl blocks.length) then fillNoGaps blocks
