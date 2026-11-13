--| Day 9 part 2's files drawn as a disk: `drawFiles size files` has each
--| file's blocks where its span says, and the checksum of that drawing is
--| the files' checksums added up. This joins the program's spans to the
--| spec's blocks.

namespace Aoc.Year2024.Day09.Proofs
import Aoc.Year2024.Day09 (..)
import Aoc.Year2024.Day09.Spec (..)
import Std (Bool, Eq, List, Nat, Option, Void)

def Span.end (span: Span): Nat := span.start + span.length

def Span.covers (span: Span) (position: Nat): Bool := span.start <= position && position < span.end

--| The block at `position`; free past the end.
def Disk.at (disk: Disk) (position: Nat): Block := disk.blocks.getOr position Free

--| `size` blocks with each file's blocks where its span says. Meant for files whose spans don't overlap.
def drawFiles (size: Nat) (files: List File): Disk :=
  { blocks = List.range 0 size |> .map (position =>
    files.find (file => file.span.covers position) |> .map (file => FileBlock file.id) |> .getOrElse Free) }

--| `span` is a whole gap: not empty, all free, with the disk's start or a file block
--| before it and a file block after it.
def Disk.Gap (disk: Disk) (span: Span): Prop :=
  0 < span.length
    ∧ (∀ (position: Nat) => span.covers position = True → disk.at position = Free)
    ∧ (span.start = 0 ∨ (disk.at (span.start - 1)).isFile = True)
    ∧ (disk.at span.end).isFile = True

--| The files' relation in `Apart`, which says their spans share no block.
def File.Beside (file: File) (other: File): Prop := file.span.end ≤ other.span.start ∨ other.span.end ≤ file.span.start

--| The files have different numbers, none shares a block with another, and all lie within `size` blocks.
def Apart (size: Nat) (files: List File): Prop :=
  List.Distinct (files.map .id)
    ∧ List.Pairwise File.Beside files
    ∧ List.All (file => file.span.end ≤ size) files

--| A span covers the positions from its start up to its end.
theorem Span.coversIff ∀ (span: Span) (position: Nat): (span.covers position = True) ↔ (span.start ≤ position ∧ position < span.end) := {
  forward = held => cases,
  backward = within => cases
}

--| The file's number if it covers `position`, else 0.
def File.numberAt (file: File) (position: Nat): Nat := if file.span.covers position then file.id else 0

--| Below `size`, the block at `position` is the first covering file's, or free.
theorem drawFilesAt ∀ (size: Nat) (files: List File) (position: Nat) (below: position < size):
    (drawFiles size files).at position
      = (files.find (file => file.span.covers position) |> .map (file => FileBlock file.id) |> .getOrElse Free) :=
  rewrite Nat.addZero position in
    List.getOrMapRange (position => files.find (file => file.span.covers position) |> .map (file => FileBlock file.id) |> .getOrElse Free) Free size 0 position below

--| Past `size`, the disk is free.
theorem drawFilesPast ∀ (size: Nat) (files: List File) (position: Nat) (past: size ≤ position): (drawFiles size files).at position = Free :=
  List.getOrPast (drawFiles size files).blocks position Free (rewrite List.lengthMap (List.range 0 size) _, List.lengthRange 0 size in past)

--| A file beside a covering file doesn't cover.
theorem besideNotCovers ∀ (file: File) (other: File) (position: Nat) (beside: file.Beside other) (covered: file.span.covers position = True):
    other.span.covers position = False := match e: other.span.covers position with
      | True => Void.exfalso (omega [(Span.coversIff file.span position).forward covered, (Span.coversIff other.span position).forward e, beside])
      | False => rfl

theorem besideNumber ∀ (file: File) (other: File) (position: Nat) (beside: file.Beside other) (covered: file.span.covers position = True):
    other.numberAt position = 0 :=
  rewrite besideNotCovers file other position beside covered in rfl

--| In files with no shared block, the file covering `position` is the one found.
theorem findCovering ∀ (position: Nat): ∀ (files: List File) => List.Pairwise File.Beside files → ∀ (file: File) => file ∈ files → file.span.covers position = True →
    files.find (other => other.span.covers position) = Some file
  | [], pairwise, file, member, covered => Void.exfalso member
  | [first, ..rest], Both others pairwise, file, member, covered =>
    match e: first.span.covers position with
      | True =>
        match member with
          | Inl same => rewrite <- same in rfl
          | Inr later =>
            Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym (besideNotCovers first file position (List.allMem (File.Beside first) file rest others later) e)) covered))
      | False =>
        match member with
          | Inl same => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym e) (rewrite same in covered)))
          | Inr later => findCovering position rest pairwise file later covered

--| The number at `position` of the covering file, or 0, is the sum over files.
theorem drawnNumber ∀ (position: Nat) (files: List File) (h: List.Pairwise File.Beside files):
    (files.find (file => file.span.covers position) |> .map (file => FileBlock file.id) |> .getOrElse Free).idOr 0 = files.sumBy (file => file.numberAt position) :=
  match files, h with
    | [], pairwise => rfl
    | [first, ..rest], Both others pairwise =>
      match e: first.span.covers position with
        | True =>
          let others := List.sumByZeroIntro rest (file => file.numberAt position)
            (other member => besideNumber first other position (List.allMem (File.Beside first) other rest others member) e)
          Eq.sym (Eq.trans (List.sumByFrom rest first.id (file => file.numberAt position)) (rewrite others in Nat.addZero first.id))
        | False => Eq.trans (drawnNumber position rest pairwise) (Eq.sym (List.sumByFrom rest 0 (file => file.numberAt position)))

--| A span doesn't cover a position at or past its end.
theorem notCoversPast ∀ (span: Span) (position: Nat) (past: span.end ≤ position): span.covers position = False :=
  match e: span.covers position with
    | True => Void.exfalso (omega [(Span.coversIff span position).forward e])
    | False => rfl

--| In files that are `Apart`, the block at a covered position is the covering file's.
theorem drawFilesFile ∀ (size: Nat) (files: List File) (position: Nat) (apart: Apart size files) (file: File) (member: file ∈ files)
    (covered: file.span.covers position = True): (drawFiles size files).at position = FileBlock file.id :=
  match apart with
    | Both distinct (Both pairwise within) =>
      let fits := List.allMem (other => other.span.end ≤ size) file files within member
      let below: position < size := omega [(Span.coversIff file.span position).forward covered, fits]
      rewrite drawFilesAt size files position below, findCovering position files pairwise file member covered in rfl

--| Where no file covers, the block is free.
theorem drawFilesFree ∀ (size: Nat) (files: List File) (position: Nat) (none: ∀ (file: File) => file ∈ files → file.span.covers position = False):
    (drawFiles size files).at position = Free := match e: Nat.leq (Succ position) size with
      | True => rewrite drawFilesAt size files position e, List.findNoneOfMem (file => file.span.covers position) files none in rfl
      | False => drawFilesPast size files position (omega)

--| Each position's file number (0 if free) is the sum of the files' numbers there.
theorem drawFilesIdOr ∀ (size: Nat) (files: List File) (apart: Apart size files) (position: Nat):
    ((drawFiles size files).at position).idOr 0 = files.sumBy (file => file.numberAt position) := match apart with
      | Both distinct (Both pairwise within) =>
        match e: Nat.leq (Succ position) size with
          | True => rewrite drawFilesAt size files position e in drawnNumber position files pairwise
          | False =>
            let none := List.sumByZeroIntro files (file => file.numberAt position) (file member =>
              rewrite notCoversPast file.span position (omega [List.allMem (other => other.span.end ≤ size) file files within member]) in rfl)
            rewrite drawFilesPast size files position (omega), none in rfl

--| A span doesn't cover a position before its start.
theorem notCoversBefore ∀ (span: Span) (position: Nat) (before: position < span.start): span.covers position = False :=
  match e: span.covers position with
    | True => Void.exfalso (omega [(Span.coversIff span position).forward e])
    | False => rfl

--| A file's part of the checksum is its number times its blocks' positions added up.
theorem fileChecksumSpec ∀ (file: File): file.checksum = List.sumBy (List.rangeFrom file.span.length file.span.start) (* file.id) :=
  calc file.checksum
    _ = file.id * (file.span.length * file.span.start + file.span.length * (file.span.length - 1) / 2) := rfl
    _ = file.id * List.sum (List.rangeFrom file.span.length file.span.start) := rewrite List.sumRangeFrom file.span.length file.span.start in rfl
    _ = List.sumBy (List.rangeFrom file.span.length file.span.start) (x => file.id * x) := Eq.sym (List.sumByMulLeft _ file.id (x => x))
    _ = List.sumBy (List.rangeFrom file.span.length file.span.start) (* file.id) := List.sumByCong _ _ _ (x => Nat.mulComm file.id x)

--| A file's part of the checksum is the sum, over the disk's positions, of the position times the file's number there.
theorem fileChecksumRange ∀ (file: File) (size: Nat) (within: file.span.end ≤ size):
    (List.range 0 size).sumBy (position => position * file.numberAt position) = file.checksum :=
  let term := (position: Nat) => position * file.numberAt position
  let endIs: file.span.end = file.span.length + file.span.start := omega
  calc (List.range 0 size).sumBy term
    _ = (List.range 0 (file.span.length + file.span.start)).sumBy term :=
      List.sumByRangeExtend term (file.span.length + file.span.start) size (omega)
        (j beyond => rewrite notCoversPast file.span j (omega) in Nat.mulZero j)
    _ = (List.range 0 file.span.length).sumBy (i => term (file.span.start + i)) :=
      List.sumByRangeSkipZeros file.span.start term (i => term (file.span.start + i)) file.span.length
        (i early => rewrite notCoversBefore file.span i early in Nat.mulZero i) (i => rfl)
    _ = (List.range 0 file.span.length).sumBy (i => (file.span.start + i) * file.id) :=
      List.sumByCongRange _ _ 0 file.span.length (i low high =>
        rewrite (Span.coversIff file.span (file.span.start + i)).backward (Both (omega) (omega)) in rfl)
    _ = file.checksum := Eq.trans (Eq.sym (List.sumByRangeOffset (position => position * file.id) file.span.start file.span.length)) (Eq.sym (fileChecksumSpec file))

--| The program's checksum of a drawing, as a sum over the positions.
theorem drawFilesChecksum ∀ (size: Nat) (files: List File):
    (drawFiles size files).checksum = (List.range 0 size).sumBy (position => position * ((drawFiles size files).at position).idOr 0) :=
  let disk := drawFiles size files
  let length: disk.blocks.length = size := Eq.trans (List.lengthMap (List.range 0 size) _) (List.lengthRange 0 size)
  let term := (pair: (Nat, Block)) => pair.fst * pair.snd.idOr 0
  calc disk.checksum
    _ = (List.map (List.range 0 disk.blocks.length) (i => (i, disk.blocks.getOr i Free))).sumBy term :=
      Eq.trans (checksumSum disk) (Eq.cong (.sumBy term) (List.withIndexRange disk.blocks Free))
    _ = (List.range 0 disk.blocks.length).sumBy (i => i * (disk.at i).idOr 0) :=
      List.sumByMap (List.range 0 disk.blocks.length) term (i => (i, disk.blocks.getOr i Free))
    _ = (List.range 0 size).sumBy (i => i * (disk.at i).idOr 0) := rewrite length in rfl

--| The drawing's checksum, as the puzzle states it, is the files' checksums added up.
theorem drawFilesChecksumCorrect ∀ (size: Nat) (files: List File) (apart: Apart size files):
    filesystemChecksum (drawFiles size files) = files.sumBy .checksum := match apart with
      | Both distinct (Both pairwise within) =>
        calc filesystemChecksum (drawFiles size files)
          _ = (drawFiles size files).checksum := Eq.sym (checksumCorrect (drawFiles size files))
          _ = (List.range 0 size).sumBy (position => position * ((drawFiles size files).at position).idOr 0) := drawFilesChecksum size files
          _ = (List.range 0 size).sumBy (position => files.sumBy (file => position * file.numberAt position)) :=
            List.sumByCongMem _ _ _ (position member =>
              Eq.trans (Eq.cong (n => position * n) (drawFilesIdOr size files (Both distinct (Both pairwise within)) position))
                (Eq.sym (List.sumByMulLeft files position (file => file.numberAt position))))
          _ = files.sumBy (file => (List.range 0 size).sumBy (position => position * file.numberAt position)) :=
            List.sumBySwap files (List.range 0 size) (position file => position * file.numberAt position)
          _ = files.sumBy .checksum :=
            List.sumByCongMem files _ _ (file member => fileChecksumRange file size (List.allMem (other => other.span.end ≤ size) file files within member))
