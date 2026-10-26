-- The library's `Map` and `Set` (std/Map/Map.sw, std/Set/Set.sw,
-- docs/proposals/map-set.md): counting, a set of visited positions, a proof
-- from the library's theorems, and §7.5's cases for the ordering in the type
-- (docs/proposals/interfaces.md), with the real `Ord`.

import Std (Eq, Map, Nat, Option, Ord, Set)

-- Counting with `insertWith`: each word's count, in alphabetical order.
def wordCounts (words: List Text): Map Text Nat :=
  words.foldLeft Map.empty ((counts: Map Text Nat) word => counts.insertWith word 1 Nat.add)

test "counting" := (wordCounts ["b", "a", "b", "c", "b"]).toList == [("a", 1), ("b", 3), ("c", 1)]

-- Maps are equal when they have the same entries, in whatever order they
-- were made.
test "equal maps" := wordCounts ["b", "a", "b"] == Map.fromList [("b", 2), ("a", 1)] ∧ wordCounts ["a"] ≠ wordCounts ["a", "a"]

-- A set of pairs: the positions a walk visits, ordered by row, then column.
def step: (Nat, Nat) → Char → (Nat, Nat)
  | (row, column), 'R' => (row, column + 1)
  | (row, column), 'D' => (row + 1, column)
  | (row, column), 'L' => (row, column - 1)
  | (row, column), _ => (row - 1, column)

def visited (moves: Text): Set (Nat, Nat) :=
  def move (acc: ((Nat, Nat), Set (Nat, Nat))) (m: Char): ((Nat, Nat), Set (Nat, Nat)) :=
    let (pos, seen) := acc
    (step pos m, seen.insert (step pos m))
  (moves.toList.foldLeft ((0, 0), Set.singleton (0, 0)) move).snd

test "a walk" := (visited "RRDLLU").size == 6 ∧ (visited "RLRL").size == 2
test "visited in order" := (visited "RDL").toList == [(0, 0), (0, 1), (1, 0), (1, 1)]
test "membership" := (visited "RD").contains (1, 1) ∧ not ((visited "RD").contains (1, 0))
test "equal sets" := visited "RDLU" == visited "DRUL" ∧ visited "R" ≠ visited "D"

-- Removing and altering.
test "remove" := (wordCounts ["a", "b"] |> Map.remove "a").keys == ["b"]
test "alter" := (wordCounts ["a"] |> Map.alter "a" (n => Some (Option.getOrElse n 0 + 5))).get "a" == Some 6
test "show" := "${wordCounts ["x", "x"]}" == "Map.fromList [(\"x\", 2)]" ∧ "${Set.fromList [2, 1]}" == "Set.fromList [1, 2]"

-- What `get` says after `insert`, from the library's theorems, for any map.
theorem afterTwo (m: Map Nat Text): (m |> Map.insert 1 "a" |> Map.insert 2 "b" |> Map.get 1) = Some "a" :=
  Eq.trans (Map.getInsertOther 2 "b" 1 (Nat.equalFalse 1 2 rfl) (Map.insert m 1 "a")) (Map.getInsert 1 "a" m)

-- The ordering is part of the type (§7.5).

-- Another order, passed by name.
def descending: Ord Nat :=
  Ord.fromCompare (x y => Nat.compare y x)
    (x y h => Eq.sym (Nat.compareEqual y x h))
    (x y => Nat.compareFlip y x)
    (x y z h1 h2 => Nat.compareTrans z y x h2 h1)

def down: Map Nat Text [ord := descending] := Map.fromList [(1, "a"), (3, "c"), (2, "b")]

test "given by name" := down.keys == [3, 2, 1]

-- An operation on an existing map, with another `Ord Nat` in scope: the
-- map's type fixes the ordering (§5.5 step 1), so the local one isn't used.
def insertFive [auto other: Ord Nat] (m: Map Nat Text [ord := descending]): List Nat := m.insert 5 "e" |> .keys

test "the map's own ordering" := insertFive down == [5, 3, 2, 1]

-- `Show (Map k v [ord := o])` keeps the map's ordering: the entries come out
-- in its order.
test "shown in its own order" := "${down}" == "Map.fromList [(3, \"c\"), (2, \"b\"), (1, \"a\")]"

-- A map with a named alternative ordering, as state.
ability State (s: Type) where
  get: () → {State s} s
  put: s → {State s} ()

def runState (init: s) (prog: () → {State s | e} a): {e} (a, s) :=
  let run: s → {e} (a, s) :=
    handle prog() with
      | return x => st => (x, st)
      | get u, k => st => k st st
      | put st2, k => st => k() st2
  run init

def record (n: Nat): {State (Map Nat Nat [ord := descending])} () :=
  put (get().insert n (n * 10))

def recordTwo(): {State (Map Nat Nat [ord := descending])} () :=
  record 4
  record 7

def recorded: Map Nat Nat [ord := descending] :=
  match runState Map.empty recordTwo with
    | (_, m) => m

test "a map as state" := recorded.toList == [(7, 70), (4, 40)]

-- Values that are pure functions are allowed in state too.
def functions: {State (Map Nat (Nat → Nat))} () :=
  put (get().insert 1 (n => n + 1))

def stored: Map Nat (Nat → Nat) :=
  match runState Map.empty (u => functions) with
    | (_, m) => m

test "functions as state" := stored.keys == [1] ∧ Option.map (stored.get 1) (f => f 2) == Some 3

-- Later additions: counts, groupBy, unionWith, ordered lookups, keySet and Set.isSubset.
test "counts" := (Map.counts ["b", "a", "b"]).toList == [("a", 1), ("b", 2)]
test "groupBy" := (Map.groupBy [1, 2, 3, 4, 5] (n => n % 2)).toList == [(0, [2, 4]), (1, [1, 3, 5])]
test "unionWith" := (Map.unionWith (wordCounts ["a", "b"]) (wordCounts ["b", "c"]) Nat.add).toList == [("a", 1), ("b", 2), ("c", 1)]
test "min and below" := (wordCounts ["b", "a", "c"]).min == Some ("a", 1) ∧ (wordCounts ["b", "a", "c"]).below "c" == Some ("b", 1)
test "keySet" := (wordCounts ["b", "a"]).keySet == Set.fromList ["a", "b"]
test "isSubset" := Set.isSubset (visited "R") (visited "RD") ∧ not (Set.isSubset (visited "RD") (visited "R"))
