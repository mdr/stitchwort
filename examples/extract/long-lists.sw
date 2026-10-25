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
-- run: sameNats 5
-- run: sameItems 5
-- run: lastDiffers 5
-- run: shorter 5
-- run: lastDiffers 0
import Std (Bool, List, Nat, Option, Text)

def sum (xs: List Nat): Nat := List.foldLeft xs 0 (a x => a + x)

def count (xs: List Nat): Nat := List.foldLeft xs 0 (a x => a + 1)

-- Scrambled numbers below 100003.
def scrambled (n: Nat): List Nat := List.map (List.range n) (i => (i * 7919) % 100003)

export def mapSum (n: Nat): Nat := sum (List.map (List.range n) (x => x + 1))

export def filterCount (n: Nat): Nat := count (List.filter (List.range n) (x => x % 3 == 0))

export def filterMapSum (n: Nat): Nat :=
  sum (List.filterMap (List.range n) (x => if x % 2 == 0 then Some (x / 2) else None))

export def appendCount (n: Nat): Nat := count (List.append (List.range n) (List.range n))

def firstPlusLast: List Nat -> Nat
  | Nil => 0
  | Cons x xs => x + List.foldLeft xs 0 (a y => y)

export def sortedFirst (n: Nat): Nat := firstPlusLast (List.sort (scrambled n))

def ascending (prev: Nat): List Nat -> Bool
  | Nil => True
  | Cons x xs => if Nat.leq prev x then ascending x xs else False

export def sortIsSorted (n: Nat): Bool := ascending 0 (List.sort (scrambled n))

-- List equality, and the `==` derived for a record holding a list, is a loop
-- too: it stops at the first difference and doesn't use a frame per element.
type Item = { id: Nat, name: Text }

def items (n: Nat): List Item := (List.range n).map (i => { id = i, name = "x" })

export def sameNats (n: Nat): Bool := List.range n == List.range n

export def sameItems (n: Nat): Bool := items n == items n

-- Equal but for the last element, and equal but for the length.
export def lastDiffers (n: Nat): Bool :=
  List.range n == (List.range n).map (i => if i + 1 == n then n + 7 else i)

export def shorter (n: Nat): Bool := List.range n == List.range (n + 1)
