-- Advent of Code 2025 day 2 style check: does an ID repeat a block of
-- k characters? Cut the text into k-character chunks, drop the repeats, and
-- see whether one chunk is left. A length that k doesn't divide fails the
-- check before that (the last chunk would be short).
import Std (List, Text, Nat)

def repeatsWith (text: Text) (k: Nat): Bool :=
  k != 0 && text.length % k == 0 && (text.chunksOf k |> .distinct |> .length) == 1

-- Some shorter block length makes the ID a repeat (the whole ID doesn't count).
def repeatsAny (text: Text): Bool := List.any (List.range text.length) (k => repeatsWith text k)

test "1212 repeats a block of two" := repeatsWith "1212" 2
test "1212 is not a block of three" := !(repeatsWith "1212" 3)
test "block length zero never repeats" := !(repeatsWith "1212" 0)
test "111 repeats a block of one" := repeatsWith "111" 1
test "12341234 repeats a block of four" := repeatsWith "12341234" 4
test "123123123 is found" := repeatsAny "123123123"
test "1213 repeats nothing" := !(repeatsAny "1213")
test "a repeat is its block, repeated" := repeatsWith ("ab".repeat 3) 2
