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
theorem narrowBits (lower: Char) (upper: Char) (differ: (upper == lower) = False):
    (bits: List Bool) → (first: Nat) → (last: Nat) → last + 1 = first + Nat.pow 2 bits.length →
      (narrow lower upper { first, last } (bits.map (letter lower upper))).flatMap Region.only = Some (first + Nat.fromBits bits)
  | [], first, last, size =>
    match same: first == last with
      | True => rfl
      | False => Void.exfalso (DecEq.soundFalse first last same (omega))
  | [True, ..rest], first, last, size =>
    rewrite differ, DecEq.refl upper in
      Eq.trans (narrowBits lower upper differ rest (first + (last + 1 - first) / 2) last (omega))
        (Eq.cong Some (omega [Nat.fromBitsCons True rest]))
  | [False, ..rest], first, last, size =>
    rewrite DecEq.refl lower in
      Eq.trans (narrowBits lower upper differ rest first (first + (last + 1 - first) / 2 - 1) (omega [Nat.powSuccPos 1 rest.length]))
        (Eq.cong Some (omega [Nat.fromBitsCons False rest]))

--| A pass's letters, from its row's bits and its column's.
def written (row: List Bool) (column: List Bool): List Char := row.map (letter 'F' 'B') ++ column.map (letter 'L' 'R')

theorem fromBitsAppend (high: List Bool) (low: List Bool): Nat.fromBits (high ++ low) = Nat.fromBits high * Nat.pow 2 low.length + Nat.fromBits low :=
  Eq.trans (List.foldLeftAppend high 0 low (acc bit => acc * 2 + Bool.toNat bit)) (Nat.fromBitsFrom (Nat.fromBits high) low)

theorem seatIdSpec (row: List Bool) (column: List Bool) (rows: row.length = 7) (columns: column.length = 3):
    (seat (written row column)).map Seat.id = Some (seatId (row ++ column)) :=
  let rowLetters: (row.map (letter 'F' 'B')).length = 7 := rewrite List.lengthMap row (letter 'F' 'B') in rows
  let columnLetters: (column.map (letter 'L' 'R')).length = 3 := rewrite List.lengthMap column (letter 'L' 'R') in columns
  rewrite List.lengthAppend (row.map (letter 'F' 'B')) (column.map (letter 'L' 'R')), rowLetters, columnLetters in
    rewrite List.takeAppendLength _ (column.map (letter 'L' 'R')) 7 rowLetters, List.dropAppendLength _ (column.map (letter 'L' 'R')) 7 rowLetters in
      rewrite narrowBits 'F' 'B' rfl row 0 127 (rewrite rows in rfl), narrowBits 'L' 'R' rfl column 0 7 (rewrite columns in rfl) in
        rewrite fromBitsAppend row column, columns in rfl
