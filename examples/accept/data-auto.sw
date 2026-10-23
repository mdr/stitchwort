-- `auto` parameters on data types (docs/proposals/interfaces.md §7.5,
-- stage 4): a map carries its ordering in its type. `Ordered` stands in for
-- the library's `Ord`; the map is a sorted list, enough to see which
-- ordering each operation uses.

import Ordered (compare)
import Std (Nat, Text)

interface Ordered (k: Type) =
  { compare: k -> k -> Ordering }

instance Ordered.instNat: Ordered Nat :=
  { compare = Nat.compare }

instance Ordered.instText: Ordered Text :=
  { compare = Text.compare }

-- A named alternative: never found, passed by name.
def descending: Ordered Nat := { compare = m n => Nat.compare n m }

-- The ordering is a parameter of the type, found wherever the type is
-- written, as for a function's `auto` argument.
type Map (k: Type) (v: Type) [auto ord: Ordered k] =
  { entries: List (k, v) }

-- Inside a generic function, `Map k v` is the map with its own `ord`.
def Map.empty [auto ord: Ordered k]: Map k v := { entries = [] }

def Map.insertList [auto ord: Ordered k] (key: k) (value: v): List (k, v) -> List (k, v)
  | [] => [(key, value)]
  | Cons (k2, v2) rest => match compare key k2 with
    | Less => Cons (key, value) (Cons (k2, v2) rest)
    | Equal => Cons (key, value) rest
    | Greater => Cons (k2, v2) (Map.insertList key value rest)

def Map.insert [auto ord: Ordered k] (key: k) (value: v) (m: Map k v): Map k v :=
  { entries = Map.insertList key value m.entries }

-- Any ordering, written as a variable (bound automatically).
def Map.keys (m: Map k v [ord := o]): List k := m.entries.map (p => match p with | (a, _) => a)

-- `Map Text Nat` is `Map Text Nat [ord := Ordered.instText]`: found by search.
def words: Map Text Nat := Map.empty |> .insert "b" 2 |> .insert "a" 1 |> .insert "c" 3

test "filled by search" := words.keys == ["a", "b", "c"]

-- Given by name: a different type, whose operations all use `descending`.
def down: Map Nat Nat [ord := descending] :=
  Map.empty |> .insert 1 1 |> .insert 3 3 |> .insert 2 2

test "given by name" := down.keys == [3, 2, 1]

-- A synonym may have an `auto` parameter too.
type Set (k: Type) [auto ord: Ordered k] = Map k () [ord := ord]

def Set.add [auto ord: Ordered k] (key: k) (s: Set k): Set k := Map.insert key () s

def small: Set Nat := Map.empty |> Set.add 2 |> Set.add 1 |> Set.add 2

test "a set" := small.keys == [1, 2]

-- An operation on an existing map, with another `Ordered Nat` in scope: the
-- map's type fixes `insert`'s `ord`, so the local one isn't used (§5.5 step 1).
def insertFive [auto other: Ordered Nat] (m: Map Nat Nat [ord := descending]): List Nat :=
  (m.insert 5 5).keys

test "the map's own ordering" := insertFive down == [5, 3, 2, 1]

-- Written without a name inside that function, `Map Nat Nat` would be the
-- local one's: a dictionary in scope wins over the instance.
def withLocal [auto other: Ordered Nat]: Map Nat Nat := Map.empty |> .insert 1 1 |> .insert 2 2

test "a local ordering" := (withLocal [other := descending]).keys == [2, 1]

-- An instance whose head has the ordering as a variable covers maps with any
-- ordering; matching fixes it, and it's kept, not found again: inside, `o`
-- is the map's own ordering, so its first two keys are in order by `o`.
-- (Found again, `Ordered Nat` would be `Ordered.instNat`, and `down`'s keys
-- `3, 2` would be out of order.)
interface Pretty (a: Type) =
  { pretty: a -> Text }

instance Map.instPretty: Pretty (Map k v [ord := o]) :=
  { pretty = m => match m.entries with
    | Cons (a, _) (Cons (b, _) _) => match compare [ordered := o] a b with
      | Less => "in order"
      | _ => "out of order"
    | _ => "short" }

test "the head's ordering is kept" := Pretty.pretty down == "in order"
test "for any ordering" := Pretty.pretty words == "in order"

-- `==` is derived as for any record: the ordering is a parameter, not a
-- field.
test "equal maps" := words == (Map.empty |> .insert "c" 3 |> .insert "a" 1 |> .insert "b" 2)
test "different maps" := words != Map.empty

-- A map is data when its keys and values are, whatever its ordering: one
-- with a named alternative ordering is a `State`.
ability State (s: Type) where
  get: () -> {State s} s
  put: s -> {State s} ()

def runState (init: s) (prog: () -> {State s | e} a): {e} (a, s) :=
  let run: s -> {e} (a, s) :=
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

test "a map as state" := recorded.keys == [7, 4]

-- Values that are pure functions are allowed in state too (abilities.md:
-- only a computation using the ability itself is refused, Landin's knot;
-- see examples/reject/data-auto-knot.sw).
def functions: {State (Map Nat (Nat -> Nat))} () :=
  put (get().insert 1 (n => n + 1))

def stored: Map Nat (Nat -> Nat) :=
  match runState Map.empty (u => functions) with
    | (_, m) => m

test "functions as state" := stored.keys == [1]
