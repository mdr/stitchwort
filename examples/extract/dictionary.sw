-- `Map Text V` crosses the JS boundary as a plain object, a dictionary from
-- string keys to `V`: `{ readonly [k: string]: V }`. Decoding reads the
-- object's own enumerable string keys and builds the map with the library's
-- own `Map.fromList`; encoding makes a fresh object from the map's entries,
-- in key order. Only maps from `Text` cross, in `Text`'s own order.
--
-- run: total (Map.fromList [("a", 1), ("b", 2), ("c", 39)])
-- run: total Map.empty
-- run: bump (Map.fromList [("a", 1)]) "a"
-- run: bump (Map.fromList [("a", 1)]) "b"
-- run: bump Map.empty "__proto__"
-- run: bump (Map.fromList [("constructor", 7), ("toString", 8)]) "constructor"
-- run: bump (Map.fromList [("", 7), ("é", 1), ("😀", 2), ("a\u{301}", 3)]) ""
-- run: keysOf (Map.fromList [("b", 1), ("a", 2), ("B", 3)])
-- run: keysOf Map.empty
-- run: lookup (Map.fromList [("a", 1)]) "a"
-- run: lookup (Map.fromList [("a", 1)]) "z"
-- run: lookup (Map.fromList [("__proto__", 1)]) "__proto__"
-- run: lookup (Map.fromList [("a", 1)]) "toString"
-- run: ages (Map.fromList [("ada", { name = "Ada Lovelace", age = 36 }), ("alan", { name = "Alan Turing", age = 41 })])
-- run: nested (Map.fromList [("x", Map.fromList [("a", 1), ("b", 2)]), ("y", Map.empty), ("z", Map.fromList [("c", 5)])])
-- run: merge (Map.fromList [("a", 1), ("b", 2)]) (Map.fromList [("b", 20), ("c", 30)])
-- run: same (Map.fromList [("a", 1), ("b", 2)]) (Map.fromList [("b", 2), ("a", 1)])
-- run: same (Map.fromList [("a", 1)]) (Map.fromList [("a", 2)])
-- run: sparse (Map.fromList [("a", Some 1), ("b", None)])
-- run: grouped ["apple", "avocado", "banana", "blueberry", "cherry", ""]
-- run: roster { title = "Team", people = Map.fromList [("a", { name = "A", age = 1 })] }
-- run: lists (Map.fromList [("x", [1, 2]), ("y", [])])
-- run: noScores
-- run: orders (Map.fromList [("10", 1), ("9", 2), ("b", 3), ("a", 4)])

import Std (List, Map, Nat, Option, Text)

type Person = { name: Text, age: Nat }

type Roster = { title: Text, people: Map Text Person }

-- A map in, a number out.
export def total (scores: Map Text Nat): Nat := Map.foldLeft (acc _ n => acc + n) 0 scores

-- A map in and out.
export def bump (scores: Map Text Nat) (who: Text): Map Text Nat := Map.insertWith Nat.add who 1 scores

export def keysOf (scores: Map Text Nat): List Text := Map.keys scores

export def lookup (scores: Map Text Nat) (who: Text): Option Nat := Map.get who scores

-- Records as values: `{ readonly [k: string]: Person }`.
export def ages (people: Map Text Person): Map Text Nat := Map.map (p => p.age) people

-- A map of maps.
export def nested (groups: Map Text (Map Text Nat)): Map Text Nat := Map.map total groups

export def merge (a: Map Text Nat) (b: Map Text Nat): Map Text Nat := Map.union a b

-- Maps have `==`: by entries, in any order the keys were given.
export def same (a: Map Text Nat) (b: Map Text Nat): Bool := a == b

-- An optional value: `number | undefined`.
export def sparse (m: Map Text (Option Nat)): Map Text (Option Nat) := m

-- Lists as values.
export def lists (m: Map Text (List Nat)): Map Text (List Nat) := m

-- Words by first letter.
export def grouped (words: List Text): Map Text (List Text) :=
  List.foldLeft (m w => if Text.isEmpty w then m else Map.insertWith List.append (Text.take 1 w) [w] m) Map.empty words

-- A record with a map in a field.
export def roster (r: Roster): Roster := r

-- A map as a result, with no arguments.
export def noScores: Map Text Nat := Map.empty

-- Keys that look like numbers: JS lists them first, in numeric order.
export def orders (m: Map Text Nat): Map Text Nat := m
