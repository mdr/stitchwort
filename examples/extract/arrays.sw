-- Arrays (std/Array/Array.sw) in the generated JS, which runs their list
-- definitions until JS has a native array (docs/proposals/arrays.md §4.3):
-- the same answers, at list speed.
--
-- run: fillSum 50
-- run: fillSum 0
-- run: sharedSum 20
-- run: pushPop 30
-- run: lookups 10
import Std (Array, List, Nat, Option)

--| Sets each index to twice itself, then sums them.
export def fillSum (n: Nat): Nat :=
  let filled := (List.range 0 n).foldLeft (Array.replicate (count := n) 0) (array i => array.set i (i * 2))
  filled.foldLeft 0 (+)

--| Each `set` is on the same array, which every later step still reads.
export def sharedSum (n: Nat): Nat :=
  let base := Array.replicate (count := n) 1
  (List.range 0 n).foldLeft 0 (acc i => acc + (base.set i 5).getOr i 0 + base.getOr i 0)

--| Pushes 0, …, n - 1, then pops them all, summing.
export def pushPop (n: Nat): Nat :=
  let pushed := (List.range 0 n).foldLeft (Array.empty: Array Nat) Array.push
  let drain := (List.range 0 n).foldLeft (pushed, 0) (state i =>
    match state.fst.pop with
      | Some (rest, x) => (rest, state.snd + x)
      | None => state)
  drain.snd

--| `get` and `getOr` in and out of range.
export def lookups (n: Nat): Nat :=
  let array := Array.tabulate n (i => i + 1)
  (array.get (n / 2)).getOrElse 0 + array.getOr (n + 3) 100 + array.size
