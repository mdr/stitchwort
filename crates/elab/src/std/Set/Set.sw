-- `Set k`: finite sets of keys, a `Map` from the keys to `()`, with the
-- ordering in the type as for `Map` (docs/proposals/interfaces.md §7.5):
-- `Set Nat` is `Set Nat [ord := Nat.instOrd]`. A record around the map, not
-- a synonym for it, so that dot notation on a set finds `Set`'s functions
-- (`s.insert 3`, `s.toList`). docs/proposals/map-set.md.

type Set (k: Type) [auto ord: Ord k] = { items: Map k () [ord := ord] }

-- No keys.
def Set.empty [auto ord: Ord k]: Set k := { items = Map.empty }

-- With `key` (the same set if it's there already).
def Set.insert [auto ord: Ord k] (key: k) (s: Set k): Set k := { items = Map.insert key () s.items }

def Set.singleton [auto ord: Ord k] (key: k): Set k := Set.insert key Set.empty

def Set.contains [auto ord: Ord k] (key: k) (s: Set k): Bool := Map.contains key s.items

-- Without `key` (the same set if it isn't there).
def Set.remove [auto ord: Ord k] (key: k) (s: Set k): Set k := { items = Map.remove key s.items }

-- The number of keys, O(1).
def Set.size (s: Set k [ord := o]): Nat := Map.size s.items

def Set.isEmpty (s: Set k [ord := o]): Bool := Map.isEmpty s.items

-- The keys, in order.
def Set.toList (s: Set k [ord := o]): List k := Map.keys s.items

def Set.fromList [auto ord: Ord k] (xs: List k): Set k := List.foldLeft (s key => Set.insert key s) Set.empty xs

-- Left fold over the keys in order.
def Set.foldLeft (f: b -> k -> b) (z: b) (s: Set k [ord := o]): b := Map.foldLeft (acc key u => f acc key) z s.items

-- The keys for which `p` holds.
def Set.filter [auto ord: Ord k] (p: k -> Bool) (s: Set k): Set k := { items = Map.filter (key u => p key) s.items }

-- The keys of both.
def Set.union [auto ord: Ord k] (a: Set k) (b: Set k): Set k := { items = Map.union a.items b.items }

-- The keys of `a` that are also in `b`.
def Set.intersect [auto ord: Ord k] (a: Set k) (b: Set k): Set k := Set.filter (key => Set.contains key b) a

-- The keys of `a` that aren't in `b`.
def Set.difference [auto ord: Ord k] (a: Set k) (b: Set k): Set k := Set.filter (key => !(Set.contains key b)) a

theorem Set.containsInsert [auto ord: Ord k] (key: k) (s: Set k): (s |> Set.insert key |> Set.contains key) = True :=
  rewrite Map.getInsert key () s.items in rfl

-- `Set.fromList [1, 2]`, in order, whatever the ordering.
instance Set.instShow [auto show: Show k]: Show (Set k [ord := o]) :=
  Show.fromText (s => Text.append "Set.fromList " (Show.list (x => Show.toSource x) (Set.toList s)))

def Set.example: Set Nat := Set.fromList [3, 1, 2, 3]

test "set: toList is in order, without repeats" := Set.toList Set.example == [1, 2, 3]
test "set: size" := Set.size Set.example == 3 && Set.isEmpty (Set.empty: Set Nat)
test "set: contains" := Set.contains 2 Set.example && !(Set.contains 4 Set.example)
test "set: insert" := Set.toList (Set.insert 0 Set.example) == [0, 1, 2, 3] && Set.size (Set.insert 1 Set.example) == 3
test "set: remove" := Set.toList (Set.remove 2 Set.example) == [1, 3] && Set.size (Set.remove 7 Set.example) == 3
test "set: foldLeft" := Set.foldLeft (acc x => acc * 10 + x) 0 Set.example == 123
test "set: union, intersect, difference" :=
  Set.toList (Set.union Set.example (Set.fromList [5, 0])) == [0, 1, 2, 3, 5]
    && Set.toList (Set.intersect Set.example (Set.fromList [2, 3, 4])) == [2, 3]
    && Set.toList (Set.difference Set.example (Set.fromList [2])) == [1, 3]
test "set: show" := "${Set.fromList ["b", "a"]}" == "Set.fromList [\"a\", \"b\"]"

-- The set of `f` applied to each key; keys that map to the same value merge,
-- and the result is ordered by the new ordering.
def Set.map [auto ord: Ord j] (s: Set k [ord := o]) (f: k -> j): Set j := Set.foldLeft (acc key => Set.insert (f key) acc) Set.empty s

-- Whether some key satisfies `p`.
def Set.any (s: Set k [ord := o]) (p: k -> Bool): Bool := Set.foldLeft (acc key => acc || p key) False s

-- The number of keys satisfying `p`.
def Set.count (s: Set k [ord := o]) (p: k -> Bool): Nat := Set.foldLeft (n key => Nat.succIf n (p key)) 0 s

test "set: map merges and reorders" := Set.toList (Set.map Set.example (x => 10 - x / 2)) == [9, 10]
test "set: any" := Set.any Set.example (x => x > 2) && Bool.not (Set.any Set.example (x => x > 3)) && Bool.not (Set.any (Set.empty: Set Nat) (x => True))
test "set: count" := Set.count Set.example (x => x != 2) == 2
