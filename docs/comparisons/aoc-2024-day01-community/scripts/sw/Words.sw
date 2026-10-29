-- The parse most community solutions use: split the text on white space,
-- read every word as a number, take them two at a time and transpose into
-- the two columns. No line or column in errors; a bad word is dropped.
namespace Scratch.Words
import Std (IO, List, Map, Nat, Text)

def main(): {IO} () :=
  let columns := IO.readAll().words.filterMap Text.toNat |> .chunksOf 2 |> .transpose
  let left := columns.headOr []
  let right := columns.drop 1 |> .headOr []
  IO.print "Part 1: ${left.sort |> .zipWith right.sort Nat.absDiff |> .sum}"
  let counts := Map.counts right
  IO.print "Part 2: ${left.sumBy (id => id * counts.getOr id 0)}"
