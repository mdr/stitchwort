-- Tests that fail on purpose, to show what `stitchwort test` says.
import Std (List, Nat, Text)

def parse (line: Text): List Nat := line.split ',' |> .filterMap Text.toNat

def isSorted: List Nat → Bool
  | Cons a (Cons b rest) => a ≤ b ∧ isSorted (Cons b rest)
  | _ => True

test "parses the example" := parse "1,2,4" == [1, 2, 3]
test "both parts" := parse "7" == [7] ∧ List.length (parse "1,x") == 2
test "sorted" := isSorted (parse "3,1,2")
test "all small" := List.all (parse "1,2,3") (n => n < 3)
