-- The library's `Map` and `Set` (std/Map/Map.sw, std/Set/Set.sw,
-- docs/proposals/map-set.md): counting, a set of visited positions, a proof
-- from the library's theorems, and §7.5's cases for the ordering in the type
-- (docs/proposals/interfaces.md), with the real `Ord`.

import Std (Eq)

-- Counting with `insertWith`: each word's count, in alphabetical order.
def wordCounts (words: List Text): Map Text Nat :=
  words.foldLeft ((counts: Map Text Nat) word => counts.insertWith Nat.add word 1) Map.empty

test "counting" := (wordCounts ["b", "a", "b", "c", "b"]).toList == [("a", 1), ("b", 3), ("c", 1)]

-- A set of pairs: the positions a walk visits, ordered by row, then column.
def step: (Nat, Nat) -> Char -> (Nat, Nat)
  | (r, c), 'R' => (r, c + 1)
  | (r, c), 'D' => (r + 1, c)
  | (r, c), 'L' => (r, c - 1)
  | (r, c), _   => (r - 1, c)

def visited (moves: Text): Set (Nat, Nat) :=
  def move (acc: ((Nat, Nat), Set (Nat, Nat))) (m: Char): ((Nat, Nat), Set (Nat, Nat)) :=
    let (pos, seen) := acc
    (step pos m, seen.insert (step pos m))
  (moves.toList.foldLeft move ((0, 0), Set.singleton (0, 0))).snd

test "a walk" := (visited "RRDLLU").size == 6 && (visited "RLRL").size == 2
test "visited in order" := (visited "RDL").toList == [(0, 0), (0, 1), (1, 0), (1, 1)]
test "membership" := (visited "RD").contains (1, 1) && not ((visited "RD").contains (1, 0))

-- Removing and altering.
test "remove" := (wordCounts ["a", "b"] |> Map.remove "a").keys == ["b"]
test "alter" := (wordCounts ["a"] |> Map.alter (n => Just (Maybe.withDefault 0 n + 5)) "a").get "a" == Just 6
test "show" := "${wordCounts ["x", "x"]}" == "Map.fromList [(\"x\", 2)]" && "${Set.fromList [2, 1]}" == "Set.fromList [1, 2]"

-- What `get` says after `insert`, from the library's theorems, for any map.
theorem afterTwo (m: Map Nat Text): (m |> Map.insert 1 "a" |> Map.insert 2 "b" |> Map.get 1) = Just "a" :=
  Eq.trans (Map.getInsertOther 2 "b" 1 (Nat.equalFalse 1 2 rfl) (Map.insert 1 "a" m)) (Map.getInsert 1 "a" m)

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
def insertFive [auto other: Ord Nat] (m: Map Nat Text [ord := descending]): List Nat := (m.insert 5 "e").keys

test "the map's own ordering" := insertFive down == [5, 3, 2, 1]

-- `Show (Map k v [ord := o])` keeps the map's ordering: the entries come out
-- in its order.
test "shown in its own order" := "${down}" == "Map.fromList [(3, \"c\"), (2, \"b\"), (1, \"a\")]"

-- A map with a named alternative ordering, as state.
ability State (s: Type) where
  get: () -> {State s} s
  put: s -> {State s} ()

def runState (init: s) (prog: () -> {State s | e} a): {e} (a, s) :=
  let run: s -> {e} (a, s) :=
    handle prog() with
      | return x   => st => (x, st)
      | get u, k   => st => k st st
      | put st2, k => st => k() st2
  run init

def record (n: Nat): {State (Map Nat Nat [ord := descending])} () :=
  put ((get()).insert n (n * 10))

def recordTwo(): {State (Map Nat Nat [ord := descending])} () :=
  record 4
  record 7

def recorded: Map Nat Nat [ord := descending] :=
  match runState Map.empty recordTwo with
    | (_, m) => m

test "a map as state" := recorded.toList == [(7, 70), (4, 40)]

-- Values that are pure functions are allowed in state too.
def functions: {State (Map Nat (Nat -> Nat))} () :=
  put ((get()).insert 1 (n => n + 1))

def stored: Map Nat (Nat -> Nat) :=
  match runState Map.empty (u => functions) with
    | (_, m) => m

test "functions as state" := stored.keys == [1] && Maybe.map (f => f 2) (stored.get 1) == Just 3
