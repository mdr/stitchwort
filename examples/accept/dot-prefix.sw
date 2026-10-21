-- A call by dot notation elaborates exactly like its prefix form (SW-129):
-- `e.f a` is `T.f a e`, with the result compared with the expected type
-- before `e` is checked, so a literal receiver takes its type from there.
-- crates/driver/tests/dot_prefix.rs checks that each `…Dot` below has the
-- same hash as its `…Prefix`.

import Std (List, Nat)

def intsDot: List Int := [1, 2].map (x => x)
def intsPrefix: List Int := List.map (x => x) [1, 2]

def notsDot: List Bool := [True, False].map not
def notsPrefix: List Bool := List.map not [True, False]

def zippedDot: List (Pair Int Nat) := [1, 2].zip [3, 4]
def zippedPrefix: List (Pair Int Nat) := List.zip [1, 2] [3, 4]

def sortedDot: List Nat := [3, 1, 2].sort
def sortedPrefix: List Nat := List.sort [3, 1, 2]

def elemDot: Bool := [1, 2].elem Nat.decEq 2
def elemPrefix: Bool := List.elem Nat.decEq 2 [1, 2]

def lookupDot: Option Text := [MkPair 1 "a", MkPair 2 "b"].lookup Nat.decEq 2
def lookupPrefix: Option Text := List.lookup Nat.decEq 2 [MkPair 1 "a", MkPair 2 "b"]


test "the literal's type comes from the expected type" := intsDot == [1, 2]
test "the others agree" := sortedDot == [1, 2, 3] && elemDot
