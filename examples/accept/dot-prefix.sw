-- A call by dot notation elaborates exactly like its prefix form (SW-129):
-- `e.f a` is `T.f e a` (D303), with the result compared with the expected
-- type before `e` is checked, so a literal receiver takes its type from there.
-- crates/driver/tests/dot_prefix.rs checks that each `…Dot` below has the
-- same hash as its `…Prefix`.

import Std (List, Nat)

def intsDot: List Int := [1, 2].map (x => x)
def intsPrefix: List Int := List.map [1, 2] (x => x)

def reversedDot: List Int := [1, 2].reverse
def reversedPrefix: List Int := List.reverse [1, 2]

def notsDot: List Bool := [True, False].map not
def notsPrefix: List Bool := List.map [True, False] not

def zippedDot: List (Pair Int Nat) := [1, 2].zip [3, 4]
def zippedPrefix: List (Pair Int Nat) := List.zip [1, 2] [3, 4]

def sortedDot: List Nat := [3, 1, 2].sort
def sortedPrefix: List Nat := List.sort [3, 1, 2]

def elemDot: Bool := [1, 2].elem 2 Nat.decEq
def elemPrefix: Bool := List.elem [1, 2] 2 Nat.decEq

def lookupDot: Option Text := [MkPair 1 "a", MkPair 2 "b"].lookup 2 Nat.decEq
def lookupPrefix: Option Text := List.lookup [MkPair 1 "a", MkPair 2 "b"] 2 Nat.decEq

test "the literal's type comes from the expected type" := intsDot == [1, 2] ∧ reversedDot == [2, 1]
test "the others agree" := sortedDot == [1, 2, 3] ∧ elemDot
