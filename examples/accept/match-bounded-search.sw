-- A `match` on a search bounded by a literal (SW-982, AoC 2021 day 11).
-- To find where the scrutinee occurs in the goal and the hypotheses, the
-- `match` compares normal forms. The normal form of `answer xs` is the
-- search unfolded through all its steps, each an `if` stuck on the unknown
-- `xs`, so reading it all back took time and space growing with the bound
-- (`E-RESOURCE`, "a value was too large to write out", at 10,000). It's read back
-- only as far as the largest term it could occur in, here the type `Nat`,
-- so checking takes the same time whatever the bound. (A `match` on several
-- expressions still reads each back in full, to see whether one is part of
-- another.)
-- crates/driver/tests/resources.rs checks a smaller bound under a small size
-- limit.

import Std (List, Nat, Option)

def search (xs: List Nat) (number: Nat): Nat → Option Nat
  | 0 => None
  | Succ more => if xs.all (x => x == 0) then Some number else search (xs.map (x => x - 1)) (Succ number) more

def answer (xs: List Nat): Option Nat := search xs 1 1000000000

def describe (xs: List Nat): Nat := match answer xs with
  | Some n => n
  | None => 0

test "a bounded search" := describe [3, 1, 2] == 4
