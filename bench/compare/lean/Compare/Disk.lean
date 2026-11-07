import Std.Data.TreeMap
import Std.Data.TreeSet
open Std

def parseDiskMap (input : String) : Array Nat :=
  input.trimAscii.toString.toList.toArray.map fun c => c.toNat - '0'.toNat

/-- Part 1: the blocks, file ids at the front filled from the back. The block
at position `i` is `some id` for a file and `none` for free space. -/
def blocks (lengths : Array Nat) : Array (Option Nat) := Id.run do
  let mut blocks := #[]
  for index in [0:lengths.size] do
    let block := if index % 2 == 0 then some (index / 2) else none
    for _ in [0:lengths[index]!] do
      blocks := blocks.push block
  return blocks

/-- The checksum after moving file blocks from the end into the free blocks
at the front: the first as-many-as-there-are-files positions are filled, the
rest left free. -/
def solvePart1 (lengths : Array Nat) : Nat := Id.run do
  let disk := blocks lengths
  let files := disk.filterMap id
  let mut moving := files.size
  let mut total := 0
  for index in [0:files.size] do
    match disk[index]! with
    | some id => total := total + index * id
    | none =>
      moving := moving - 1
      total := total + index * files[moving]!
  return total

structure Span where
  start : Nat
  length : Nat

structure File where
  id : Nat
  span : Span

/-- Free spans by length, each length's starts in order. -/
abbrev FreeSpace := TreeMap Nat (TreeSet Nat)

def FreeSpace.add (free : FreeSpace) (span : Span) : FreeSpace :=
  if span.length == 0 then free
  else free.insert span.length ((free.getD span.length TreeSet.empty).insert span.start)

def FreeSpace.remove (free : FreeSpace) (span : Span) : FreeSpace :=
  let starts := (free.getD span.length TreeSet.empty).erase span.start
  if starts.isEmpty then free.erase span.length else free.insert span.length starts

/-- The free span, from the leftmost start among those long enough, that
starts before `before`. -/
def FreeSpace.leftmostFit (free : FreeSpace) (length before : Nat) : Option Span :=
  let best := free.foldl (init := (none : Option Span)) fun best spanLength starts =>
    if length <= spanLength then
      match starts.min? with
      | some start =>
        match best with
        | some current => if start < current.start then some { start, length := spanLength } else best
        | none => some { start, length := spanLength }
      | none => best
    else best
  best.filter (·.start < before)

def solvePart2 (lengths : Array Nat) : Nat := Id.run do
  -- Layout: files and the free spans between them, touching spans joined.
  let mut files : Array File := #[]
  let mut spans : Array Span := #[]
  let mut position := 0
  for index in [0:lengths.size] do
    if index % 2 == 0 then
      files := files.push { id := index / 2, span := { start := position, length := lengths[index]! } }
    else
      let span : Span := { start := position, length := lengths[index]! }
      match spans.back? with
      | some last =>
        if last.start + last.length == span.start then
          spans := spans.pop.push { start := last.start, length := last.length + span.length }
        else spans := spans.push span
      | none => spans := spans.push span
    position := position + lengths[index]!
  let mut free : FreeSpace := spans.foldl FreeSpace.add TreeMap.empty
  let mut total := 0
  for file in files.reverse do
    let mut start := file.span.start
    match free.leftmostFit file.span.length file.span.start with
    | none => pure ()
    | some span =>
      free := (free.remove span).add { start := span.start + file.span.length, length := span.length - file.span.length }
      start := span.start
    for offset in [0:file.span.length] do
      total := total + (start + offset) * file.id
  return total

def main : IO Unit := do
  let stdin ← IO.getStdin
  let lengths := parseDiskMap (← stdin.readToEnd)
  IO.println s!"Part 1: {solvePart1 lengths}"
  IO.println s!"Part 2: {solvePart2 lengths}"
