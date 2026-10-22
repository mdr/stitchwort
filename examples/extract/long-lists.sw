-- Standard list functions that build a list (map, filter, filterMap, append,
-- merge sort, range) run in a loop in the generated JS, so they handle
-- 100,000 elements without running out of Node's default stack.
--
-- The functions return small values, so the check is on the list they build
-- (its length, its sum, whether it's sorted), not on the encoding of it.
--
-- run: mapSum 100000
-- run: filterCount 100000
-- run: filterMapSum 100000
-- run: appendCount 100000
-- run: sortedFirst 100000
-- run: sortIsSorted 100000
-- run: mapSum 5
-- run: sortIsSorted 5
import Std (Bool, List, Nat, Option)

def sum (xs: List Nat): Nat := List.foldLeft (a x => a + x) 0 xs

def count (xs: List Nat): Nat := List.foldLeft (a x => a + 1) 0 xs

-- Scrambled numbers below 100003.
def scrambled (n: Nat): List Nat := List.map (i => (i * 7919) % 100003) (List.range n)

export def mapSum (n: Nat): Nat := sum (List.map (x => x + 1) (List.range n))

export def filterCount (n: Nat): Nat := count (List.filter (x => x % 3 == 0) (List.range n))

export def filterMapSum (n: Nat): Nat :=
  sum (List.filterMap (x => if x % 2 == 0 then Some (x / 2) else None) (List.range n))

export def appendCount (n: Nat): Nat := count (List.append (List.range n) (List.range n))

def firstPlusLast: List Nat -> Nat
  | Nil       => 0
  | Cons x xs => x + List.foldLeft (a y => y) 0 xs

export def sortedFirst (n: Nat): Nat := firstPlusLast (List.sort (scrambled n))

def ascending (prev: Nat): List Nat -> Bool
  | Nil       => True
  | Cons x xs => if Nat.leq prev x then ascending x xs else False

export def sortIsSorted (n: Nat): Bool := ascending 0 (List.sort (scrambled n))
