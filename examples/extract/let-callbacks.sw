-- A `let` whose value a callback uses, and a comparison inside a callback.
-- The elaborator writes `a == b` and `x ∈ xs` with their operands bound,
-- `(a => toBool (decEq a b)) x`, and the generator writes such a function,
-- applied where it's made, as `let`s: a value used once, outside any
-- lambda, goes where it's used; the rest are `const`s at the top of the
-- function's body. So the callbacks below make no closure per element, and
-- a `let` the callback uses is computed once, before the call
-- (SW-594).
--
-- run: notIn [{ id = "a", n = 1 }, { id = "b", n = 2 }, { id = "c", n = 3 }] ["b"]
-- run: notIn [] ["b"]
-- run: countEq [{ id = "a", n = 1 }, { id = "b", n = 2 }, { id = "b", n = 3 }] "b"
-- run: shifted [1, 2, 3] 4
-- run: anyAll [1, 2, 3] [2, 5]
-- run: anyAll [4] [2, 5]
-- run: weighted [1, 2, 3] 2
-- run: usedTwice [1, 2, 3] 2
-- run: direct 5
-- run: logged [1, 2, 3, 2] 1
-- run: logged [] 0

import Std (Bool, List, Nat, Text)

type Card = { id: Text, n: Nat }

-- The case SW-590 found: `c.id ∉ ids2`, with `ids2` from a `let`.
export def notIn (cards: List Card) (ids: List Text): List Card :=
  let ids2 := ids.map (t => t ++ "")
  cards.filter (c => c.id ∉ ids2)

export def countEq (cards: List Card) (key: Text): Nat :=
  let wanted := key ++ ""
  (cards.filter (c => c.id == wanted)).length

-- Nested `let`s, the second using the first, both used by a `map`.
export def shifted (xs: List Nat) (k: Nat): List Nat :=
  let a := k + 1
  let b := a * 2
  xs.map (x => x + a + b)

export def anyAll (xs: List Nat) (ys: List Nat): Bool :=
  let zs := ys.map (y => y * 2)
  xs.any (x => x + x ∈ zs) && xs.all (x => x + 1 ∉ zs)

export def weighted (xs: List Nat) (k: Nat): Nat :=
  let step := k + 3
  xs.foldLeft 0 (acc x => acc + x * step)

-- A `let` inside a callback, used twice: a `const` in the callback's body.
export def usedTwice (xs: List Nat) (k: Nat): List Nat :=
  xs.map (x =>
    let y := x * k
    y + y)

export def direct (x: Nat): Nat := ((y: Nat) => y + y) (x * 3)

-- In an effectful block, each `let` runs once, in order: the log shows it.
ability Log where
  log: Nat → {Log} ()

def collect (prog: () → {Log} Nat): List Nat :=
  handle prog() with
    | return x => [x]
    | Log.log n, k => [n] ++ k()

def steps (xs: List Nat) (k: Nat): {Log} Nat :=
  Log.log 100
  let a := k + 1
  Log.log a
  let kept := xs.filter (x => x != a)
  Log.log kept.length
  let total := kept.foldLeft 0 (acc x => acc + x * a)
  Log.log total
  total + a

export def logged (xs: List Nat) (k: Nat): List Nat := collect (u => steps xs k)
