-- `matches | …` tests a value against patterns: `True` for the values an
-- arm matches (an arm with no `=> result` gives `True`), `False` for the
-- rest. On one line, a `|` before `=>` joins patterns; arms with different
-- results go on their own lines.
import Std (List, Nat, Bool)

type Instruction = | Mul (left: Nat) (right: Nat) | Do | Dont

def isDont: Instruction → Bool := matches | Dont

def isKnown: Nat → Bool := matches | 133 | 160 | 5760

def bothOrNeither: Bool → Bool → Bool := matches
  | False, False
  | True, True

def hasSmallFactor: Instruction → Bool := matches
  | Mul left right => left <= 3 ∨ right <= 3
  | Do

theorem isDontOfDont: isDont Dont = True := isDont.eq1
theorem isDontOfDo: isDont Do = False := rfl

test "no result means True" := isKnown 160 && !isKnown 161
test "the filter form" := ([1, 133, 2, 5760]: List Nat).filter (matches | 133 | 5760) == [133, 5760]
test "arms" := bothOrNeither True True && !bothOrNeither True False
test "results" := hasSmallFactor (Mul 2 100) && hasSmallFactor Do && !hasSmallFactor (Mul 5 5) && !hasSmallFactor Dont
test "tested value" := Dont |> matches | Dont

-- `matches` is a name anywhere but before a `|`.
def matches: Nat := 4
test "matches as a name" := matches + 1 == 5
