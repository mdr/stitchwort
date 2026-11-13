--| The parser keeps the puzzle's promise: it works out each display's
--| wiring and fails unless that wiring decodes the display, so the answers
--| hold of every input `parseEntries` reads, with no hypothesis.
-- (D2108)

namespace Aoc.Year2021.Day08.Proofs
import Aoc.Year2021.Day08 (..)
import Aoc.Year2021.Day08.Spec (..)
import Std (Bool, DecEq, Eq, Exists, Fail, List, Nat, Option, Result, Void)

--| Part 1 from the input text: if `parseEntries` reads `input` as
--| `entries`, part 1's answer is the puzzle's.
theorem part1FromInput (input: Text) (entries: List Entry) (parsed: Fail.toResult (() => parseEntries input) = Ok entries):
    Part1Answer entries (solvePart1 entries) :=
  let decodes := parsedDecode input entries parsed
  Witness (entry => entry.wiring.at) (Both decodes (part1Correct entries (entry => entry.wiring.at) decodes))

--| Part 2 from the input text.
theorem part2FromInput (input: Text) (entries: List Entry) (parsed: Fail.toResult (() => parseEntries input) = Ok entries):
    Part2Answer entries (solvePart2 entries) :=
  let decodes := parsedDecode input entries parsed
  Witness (entry => entry.wiring.at) (Both decodes (part2Correct entries (entry => entry.wiring.at) decodes))

--| Every display `parseEntries` reads is decoded by its own wiring.
theorem parsedDecode (input: Text) (entries: List Entry) (parsed: Fail.toResult (() => parseEntries input) = Ok entries)
    (entry: Entry) (m: entry ∈ entries): Decodes entry.wiring.at entry :=
  wiredDecodes entry ((checkedWired _ entries parsed).read entry m)

--| Whatever reads the entries, `checkWired` passes on only wired ones.
theorem checkedWired (read: () → {Fail} List Entry) (entries: List Entry) (parsed: Fail.toResult (() => checkWired (read ())) = Ok entries):
    entries.all Entry.wired = True :=
  let split := rewrite Fail.toResultThen read checkWired at parsed
  Result.flatMapEqOk (Fail.toResult read) (x => Fail.toResult (() => checkWired x)) entries split
    (u _ checked => checkWiredOk u entries checked)

--| `checkWired` passes its entries on unchanged, and only if each is wired.
theorem checkWiredOk (entries: List Entry) (checked: List Entry) (h: Fail.toResult (() => checkWired entries) = Ok checked):
    checked.all Entry.wired = True := match e: firstUnwired entries with
      | Some (index, _) => Void.exfalso (Result.errNotOk h)
      | None =>
        rewrite <- Result.okInjective h in
          List.findNotNoneAll entries Entry.wired (List.findWithIndexFromNone (entry => not entry.wired) 0 entries e)

--| An entry that passes the program's check is decoded by its wiring.
theorem wiredDecodes (entry: Entry) (ok: entry.wired = True): Decodes entry.wiring.at entry :=
  let wiring := entry.wiring.at
  let patterns := entry.patterns
  let decode := decodeDigit patterns
  let sortedWires := (segments.map wiring).sort == segments
  let sortedDigits := (patterns.map decode).sort == List.range 0 10
  let allShow := (patterns ++ entry.outputs).all (showsRead entry.wiring patterns)
  let Both first (Both second third) := ok
  let wiresSorted := List.sortPerm (segments.map wiring)
  let wired: IsWiring wiring :=
    List.permSym segments (segments.map wiring) (rewrite first.read at wiresSorted in wiresSorted)
  let digitsSorted := List.sortPerm (patterns.map decode)
  let digitsOnce: List.Perm (patterns.map decode) digits :=
    List.permSym digits (patterns.map decode) (rewrite second.read at digitsSorted in digitsSorted)
  let showsDecoded := (pattern: Pattern) (m: pattern ∈ patterns ++ entry.outputs) =>
    readShown entry pattern wired (third.read pattern m)
  let patternsShown: patterns.map (shown wiring) = (patterns.map decode).map Some :=
    Eq.trans
      (List.mapCongMem patterns (shown wiring) (pattern => Some (decode pattern))
        (pattern m => showsDecoded pattern (List.memAppendLeft pattern patterns entry.outputs m)))
      (Eq.sym (List.mapMap patterns Some decode))
  let outputsShown: entry.outputs.all (output => (shown wiring output).isSome) = True :=
    Eq.trans
      (List.allCongMem entry.outputs (output => (shown wiring output).isSome) (output => True)
        (output m => rewrite showsDecoded output (List.memAppendRight output patterns entry.outputs m) in rfl))
      (List.allTrue entry.outputs (output => True) (output => rfl))
  Both wired (Both (rewrite patternsShown in List.permMap (patterns.map decode) digits digitsOnce Some) outputsShown)

--| A pattern that passes the program's check shows the digit read from it.
theorem readShown (entry: Entry) (pattern: Pattern) (wired: IsWiring entry.wiring.at)
    (ok: showsRead entry.wiring entry.patterns pattern = True): shown entry.wiring.at pattern = Some (decodeDigit entry.patterns pattern) :=
  let digit := decodeDigit entry.patterns pattern
  let matches := (wire: Segment) => pattern.has wire == (digitPattern digit).has (entry.wiring.at wire)
  let Both below each := ok
  let shows: Shows entry.wiring.at pattern digit = True :=
    Eq.trans
      (List.allCong segments (wire => pattern.has wire == (digitSegments digit).contains (entry.wiring.at wire)) matches
        (wire => rewrite displayDrawn digit below (entry.wiring.at wire) in rfl))
      each
  shownOf entry.wiring.at wired pattern digit below shows
