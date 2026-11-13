--| The program's seat ID is the puzzle's: halving the rows and columns
--| letter by letter ends at the row and column the letters spell in binary,
--| and row × 8 + column is the whole pass read as one 10-bit number.

namespace Aoc.Year2020.Day05.Proofs
import Aoc.Year2020.Day05 (..)
import Aoc.Year2020.Day05.Spec (..)
import Std (Bool, Char, DecEq, Eq, List, Nat, Option, Void)

--| How a pass writes a bit: `upper` for 1.
def letter (lower: Char) (upper: Char) (bit: Bool): Char := if bit then upper else lower

--| Halving a region of 2^n rows by n letters leaves the row they spell.
theorem narrowBits ∀ (lower: Char) (upper: Char) (differ: (upper == lower) = False)
    (bits: List Bool) (first last: Nat) (size: last + 1 = first + Nat.pow 2 bits.length):
    (narrow lower upper { first, last } (bits.map (letter lower upper))).flatMap Region.only = Some (first + Nat.fromBits bits) :=
  match bits with
    | [] =>
      match same: first == last with
        | True => rfl
        | False => Void.exfalso (same.read (omega))
    | [True, ..rest] =>
      rewrite differ, DecEq.refl upper in
        Eq.trans (narrowBits lower upper differ rest (first + (last + 1 - first) / 2) last (omega))
          (Eq.cong Some (omega [Nat.fromBitsCons True rest]))
    | [False, ..rest] =>
      rewrite DecEq.refl lower in
        Eq.trans (narrowBits lower upper differ rest first (first + (last + 1 - first) / 2 - 1) (omega [Nat.powSuccPos 1 rest.length]))
          (Eq.cong Some (omega [Nat.fromBitsCons False rest]))

--| A pass's letters.
def written (pass: Pass): List Char := pass.row.map (letter 'F' 'B') ++ pass.column.map (letter 'L' 'R')

theorem seatIdSpec ∀ (pass: Pass) (rows: pass.row.length = 7) (columns: pass.column.length = 3):
    (seat (written pass)).map Seat.id = Some pass.seatId :=
  let rowLetters: (pass.row.map (letter 'F' 'B')).length = 7 := rewrite List.lengthMap pass.row (letter 'F' 'B') in rows
  let columnLetters: (pass.column.map (letter 'L' 'R')).length = 3 := rewrite List.lengthMap pass.column (letter 'L' 'R') in columns
  rewrite List.lengthAppend (pass.row.map (letter 'F' 'B')) (pass.column.map (letter 'L' 'R')), rowLetters, columnLetters in
    rewrite List.takeAppendLength _ (pass.column.map (letter 'L' 'R')) 7 rowLetters, List.dropAppendLength _ (pass.column.map (letter 'L' 'R')) 7 rowLetters in
      rewrite narrowBits 'F' 'B' rfl pass.row 0 127 (rewrite rows in rfl), narrowBits 'L' 'R' rfl pass.column 0 7 (rewrite columns in rfl) in
        rewrite Nat.fromBitsAppend pass.row pass.column, columns in rfl
