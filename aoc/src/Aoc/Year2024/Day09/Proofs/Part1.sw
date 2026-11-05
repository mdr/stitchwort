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
theorem lengthFreeLast: (blocks: List Block) → (freeLastFileBlock blocks).length = blocks.length
  | [] => rfl
  | [block, ..rest] =>
    match later: lastFile rest with
      | Some id => Eq.cong Succ (lengthFreeLast rest)
      | None => rfl

--| No last file: every block is free.
theorem noLastFile: (blocks: List Block) → lastFile blocks = None → blocks = List.replicate blocks.length Free
  | [], none => rfl
  | [block, ..rest], none =>
    match later: lastFile rest with
      | Some id => Void.exfalso (Option.someNotNone id none)
      | None =>
        match block with
          | FileBlock id => Void.exfalso (Option.someNotNone id none)
          | Free => Eq.cong (Cons Free) (noLastFile rest later)

--| No last file: no file blocks.
theorem noFileBlocks: (blocks: List Block) → lastFile blocks = None → fileBlocks blocks = []
  | [], none => rfl
  | [block, ..rest], none =>
    match later: lastFile rest with
      | Some id => Void.exfalso (Option.someNotNone id none)
      | None =>
        match block with
          | FileBlock id => Void.exfalso (Option.someNotNone id none)
          | Free => noFileBlocks rest later

--| The last file block is the last of the file blocks; freeing it leaves the
--| others.
theorem fileBlocksFreeLast: (blocks: List Block) → (id: Nat) → lastFile blocks = Some id →
    fileBlocks blocks = (fileBlocks (freeLastFileBlock blocks)).append [id]
  | [], id, found => Void.exfalso (Option.noneNotSome id found)
  | [block, ..rest], id, found =>
    match later: lastFile rest with
      | Some laterId =>
        rewrite fileBlocksFreeLast rest laterId later, Option.someInjective found in
          match block with
            | FileBlock here => rfl
            | Free => rfl
      | None =>
        match block with
          | FileBlock here => rewrite noFileBlocks rest later, Option.someInjective found in rfl
          | Free => Void.exfalso (Option.noneNotSome id found)

--| Some block is a file block exactly when there is a last file.
theorem anyFileBlock: (blocks: List Block) → blocks.any (block => block.isFile) = (lastFile blocks).isSome
  | [] => rfl
  | [block, ..rest] =>
    rewrite anyFileBlock rest in
      match later: lastFile rest with
        | Some id =>
          match block with
            | FileBlock here => rfl
            | Free => rfl
        | None =>
          match block with
            | FileBlock here => rfl
            | Free => rfl

--| More blocks to move than `fillFront` uses change nothing.
theorem fillFrontAppend: (blocks: List Block) → (moving: List Nat) → (extra: List Nat) → (count: Nat) → count ≤ moving.length →
    fillFront blocks (moving.append extra) count = fillFront blocks moving count
  | blocks, moving, extra, Zero, enough => rfl
  | [], moving, extra, Succ count, enough => rfl
  | [FileBlock id, ..rest], moving, extra, Succ count, enough => Eq.cong (Cons (FileBlock id)) (fillFrontAppend rest moving extra count (omega))
  | [Free, ..rest], [], extra, Succ count, enough => Void.exfalso (omega)
  | [Free, ..rest], [id, ..moving], extra, Succ count, enough =>
    Eq.cong (Cons (FileBlock id)) (fillFrontAppend rest moving extra count (omega))

--| `fillFront` doesn't look past the first `count` blocks: freeing the last
--| file block changes nothing when there are `count` file blocks before it.
theorem fillFrontFreeLast: (blocks: List Block) → (moving: List Nat) → (count: Nat) → count ≤ fileCount (freeLastFileBlock blocks) →
    fillFront blocks moving count = fillFront (freeLastFileBlock blocks) moving count
  | blocks, moving, Zero, bound => rewrite lengthFreeLast blocks in rfl
  | [], moving, Succ count, bound => rfl
  | [block, ..rest], moving, Succ count, bound =>
    match later: lastFile rest with
      | Some id =>
        match block with
          | FileBlock here => Eq.cong (Cons (FileBlock here)) (fillFrontFreeLast rest moving count (omega))
          | Free =>
            match moving with
              | [] => Eq.cong (Cons Free) (fillFrontFreeLast rest [] count (omega))
              | [next, ..others] => Eq.cong (Cons (FileBlock next)) (fillFrontFreeLast rest others count (omega))
      | None => Void.exfalso (rewrite noFileBlocks rest later at bound in omega)

--| A file block at the front stays there.
theorem compactFile (id: Nat) (rest: List Block): compactBlocks [FileBlock id, ..rest] = [FileBlock id, ..compactBlocks rest] :=
  rewrite List.reverseCons id (fileBlocks rest) in
    Eq.cong (Cons (FileBlock id))
      (fillFrontAppend rest (fileBlocks rest).reverse [id] (fileBlocks rest).length (rewrite List.lengthReverse (fileBlocks rest) in omega))

--| A free block at the front takes the last file block.
theorem compactGap (rest: List Block) (id: Nat) (found: lastFile rest = Some id):
    compactBlocks [Free, ..rest] = [FileBlock id, ..compactBlocks (freeLastFileBlock rest)] :=
  let others := fileBlocks (freeLastFileBlock rest)
  rewrite fileBlocksFreeLast rest id found, List.reverseSnoc others id, List.lengthSnoc others id in
    Eq.cong (Cons (FileBlock id)) (fillFrontFreeLast rest others.reverse others.length (Nat.leRefl others.length))

--| Free blocks with no file block after them stay free.
theorem compactFree (rest: List Block) (none: lastFile rest = None): compactBlocks [Free, ..rest] = [Free, ..rest] :=
  rewrite noFileBlocks rest none in Eq.cong (Cons Free) (Eq.sym (noLastFile rest none))

--| Moves past a file block at the front happen behind it.
theorem stepsPastFile (id: Nat) (rest: List Block): (moves: Nat) →
    compactOneAtATime moves [FileBlock id, ..rest] = [FileBlock id, ..compactOneAtATime moves rest]
  | Zero => rfl
  | Succ moves =>
    match gap: hasGap rest with
      | True => stepsPastFile id (moveLastBlock rest) moves
      | False => rfl

--| With at least as many moves as blocks, the moves end where the program's
--| fill does.
theorem stepsFill (moves: Nat) (blocks: List Block) (enough: blocks.length ≤ moves):
    compactOneAtATime moves blocks = compactBlocks blocks
    decreasing blocks.length
:=
  match blocks with
    | [] =>
      match moves with
        | Zero => rfl
        | Succ fewer => rfl
    | [FileBlock id, ..rest] =>
      rewrite stepsPastFile id rest moves, compactFile id rest in
        Eq.cong (Cons (FileBlock id)) (stepsFill moves rest (omega))
    | [Free, ..rest] =>
      match moves with
        | Zero => Void.exfalso (omega)
        | Succ fewer =>
          match later: lastFile rest with
            | Some id =>
              let freedLength := lengthFreeLast rest
              rewrite anyFileBlock rest, later, stepsPastFile id (freeLastFileBlock rest) fewer, compactGap rest id later
                in Eq.cong (Cons (FileBlock id)) (stepsFill fewer (freeLastFileBlock rest) (omega))
            | None => rewrite anyFileBlock rest, later, compactFree rest later in rfl

--| The fill leaves no gaps.
theorem fillNoGaps (blocks: List Block): hasGap (compactBlocks blocks) = False
    decreasing blocks.length
:=
  match blocks with
    | [] => rfl
    | [FileBlock id, ..rest] => Eq.trans (Eq.cong hasGap (compactFile id rest)) (fillNoGaps rest)
    | [Free, ..rest] =>
      match later: lastFile rest with
        | Some id =>
          let freedLength := lengthFreeLast rest
          rewrite compactGap rest id later in fillNoGaps (freeLastFileBlock rest)
        | None => rewrite compactFree rest later, anyFileBlock rest, later in rfl

--| A block's part of the checksum, as the program and as the puzzle say it.
theorem blockChecksumCorrect (position: Nat): (block: Block) → position * block.idOr 0 = (block.id.map (id => position * id)).getOrElse 0
  | Free => Nat.mulZero position
  | FileBlock id => rfl

--| The program's checksum is the puzzle's.
theorem checksumCorrect (disk: Disk): disk.checksum = filesystemChecksum disk :=
  Eq.trans
    (List.sumByCongMem disk.blocks.withIndex (pair => pair.fst * pair.snd.idOr 0) (pair => Option.getOrElse (Option.map pair.snd.id (id => pair.fst * id)) 0)
      (pair member => blockChecksumCorrect pair.fst pair.snd))
    (Eq.sym (List.sumFilterMap (pair => pair.snd.id.map (id => pair.fst * id)) disk.blocks.withIndex))

--| Part 1 is the puzzle's moves, one block at a time, then the checksum.
theorem part1Correct (diskMap: DiskMap): solvePart1 diskMap = part1 diskMap :=
  let blocks := diskMap.blocks.blocks
  rewrite stepsFill blocks.length blocks (Nat.leRefl blocks.length) in checksumCorrect { blocks = compactBlocks blocks }

--| The disk's length is enough moves: none are left to make.
theorem part1NoGapsLeft (diskMap: DiskMap): hasGap (compactOneAtATime diskMap.blocks.blocks.length diskMap.blocks.blocks) = False :=
  let blocks := diskMap.blocks.blocks
  rewrite stepsFill blocks.length blocks (Nat.leRefl blocks.length) in fillNoGaps blocks
