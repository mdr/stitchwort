-- expect-warning: W-RANGE-IN-BRACKETS
-- `[0 ..< 3]` is a list holding one list. `[(0 ..< 3)]` says so, with no warning.
import Std (List, Nat)

def nested: List (List Nat) := [0 ..< 3]

test "one element" := nested == [[0, 1, 2]]

-- Written with its own brackets, the range is meant as the element.
def nestedOnPurpose: List (List Nat) := [(0 ..< 3)]
test "on purpose" := nestedOnPurpose == [[0, 1, 2]]
