-- `List.appendNewBy` and `List.differenceBy` (SW-584): merging two keyed
-- lists, the first's items winning, and what the lemmas say about it.

import Std (List)

type Setting = { name: Text, value: Nat }

-- The user's settings, then each default the user hasn't set.
def withDefaults (user: List Setting) (defaults: List Setting): List Setting := user.appendNewBy defaults (.name)

-- The defaults the user has overridden none of.
def untouched (user: List Setting) (defaults: List Setting): List Setting := defaults.differenceBy user (.name)

def user: List Setting := [{ name = "width", value = 120 }]

def defaults: List Setting := [{ name = "width", value = 80 }, { name = "tabs", value = 4 }]

test "the user's value wins" := List.map (withDefaults user defaults) (.value) == [120, 4]
test "the defaults left" := List.map (untouched user defaults) (.name) == ["tabs"]
test "merging with nothing" := List.map (withDefaults Nil defaults) (.value) == [80, 4]

-- Merged settings have one value per name, when each list has.
theorem withDefaultsDistinct (user: List Setting) (defaults: List Setting) (du: List.Distinct (List.map user (.name)))
    (dd: List.Distinct (List.map defaults (.name))): List.Distinct (List.map (withDefaults user defaults) (.name)) :=
  List.distinctKeysAppendNewBy user defaults (.name) du dd

-- A merge with itself changes nothing.
theorem withDefaultsSelf (settings: List Setting): withDefaults settings settings = settings := List.appendNewBySelf settings (.name)

-- A setting in the merge was the user's, or a default for a name the user didn't set.
theorem memWithDefaults (s: Setting) (user: List Setting) (defaults: List Setting) (m: s ∈ withDefaults user defaults):
    s ∈ user ∨ (s ∈ defaults ∧ s.name ∉ List.map user (.name)) :=
  (List.memAppendNewBy s user defaults (.name)).forward m
