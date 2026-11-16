--| The program's seat ID is the puzzle's: halving the rows and columns
--| letter by letter ends at the row and column the letters spell in binary,
--| and row × 8 + column is the whole pass read as one 10-bit number.

namespace Aoc.Year2020.Day05.Proofs
import Aoc.Year2020.Day05 (..)
import Aoc.Year2020.Day05.Spec (..)
import Std (Bool, Char, DecEq, Eq, List, Nat, Option, Void)

--| How a pass writes a bit: `upper` for 1.
def letter (lower upper: Char) (bit: Bool): Char := if bit then upper else lower

--| Halving a region of 2^n rows by n letters leaves the row they spell.
theorem narrowBits ∀ (lower upper: Char)
    (differ: (upper == lower) = False)
    (bits: List Bool) (first last: Nat)
    (size: last + 1 = first + Nat.pow 2 bits.length):
    (narrow lower upper { first, last } (bits.map (letter lower upper))).flatMap Region.only
      = Some (first + Nat.fromBits bits) :=
  match bits with
    | [] =>
      match same: first == last with
        | True => byComputing
        | False => Void.impossible (same.read (arithmetic))
    | [True, ..rest] =>
      rewrite differ, DecEq.refl upper then
        Eq.trans
          (narrowBits lower upper differ rest (first + (last + 1 - first) / 2) last (arithmetic))
          (Eq.cong Some (arithmetic [Nat.fromBitsCons True rest]))
    | [False, ..rest] =>
      rewrite DecEq.refl lower then
        Eq.trans
          (narrowBits lower upper differ rest first
            (first + (last + 1 - first) / 2 - 1)
            (arithmetic [Nat.powSuccPos 1 rest.length]))
          (Eq.cong Some (arithmetic [Nat.fromBitsCons False rest]))

--| A pass's letters.
def written (pass: Pass): List Char := pass.row.map (letter 'F' 'B') ++ pass.column.map (letter 'L' 'R')

theorem seatIdSpec ∀ (pass: Pass)
    (rows: pass.row.length = 7)
    (columns: pass.column.length = 3):
    (seat (written pass)).map Seat.id = Some pass.seatId :=
  let rowLetters: (pass.row.map (letter 'F' 'B')).length = 7 :=
    rewrite List.lengthMap pass.row (letter 'F' 'B') then rows
  let columnLetters: (pass.column.map (letter 'L' 'R')).length = 3 :=
    rewrite List.lengthMap pass.column (letter 'L' 'R') then columns
  rewrite List.lengthAppend (pass.row.map (letter 'F' 'B')) (pass.column.map (letter 'L' 'R')),
      rowLetters,
      columnLetters then
    rewrite List.takeAppendLength _ (pass.column.map (letter 'L' 'R')) 7 rowLetters,
        List.dropAppendLength _ (pass.column.map (letter 'L' 'R')) 7 rowLetters then
      rewrite narrowBits 'F' 'B' byComputing pass.row 0 127 (rewrite rows then byComputing),
          narrowBits 'L' 'R' byComputing pass.column 0 7 (rewrite columns then byComputing) then
        rewrite Nat.fromBitsAppend pass.row pass.column, columns then byComputing
