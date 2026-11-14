-- A function that only takes its argument apart can be written as its
-- cases: `match | …` is `x => match x with | …`.
type Reading = | Valid (value: Nat) | Garbled (text: Text) | Missing

def sample: List Reading := [Valid 4, Garbled "xx", Missing, Valid 9]

def numbers: List Nat := sample.map (match
  | Valid value => value
  | _ => 0)

-- `match some` keeps what matches: each result is wrapped in `Some`, and
-- the values no case matches give `None`. It fits `filterMap`.
def bigOnes: List Nat := sample.filterMap (match some | Valid value if value > 5 => value)

-- `matches` is a test: `True` for the cases it lists, `False` for the rest.
def isMissing: Reading → Bool := matches | Missing

-- A case may carry a condition, `if …`. When it is false, the cases below
-- it are tried. A plain `match` still needs a case without a condition.
def grade: Nat → Text
  | score if score >= 90 => "distinction"
  | score if score >= 50 => "pass"
  | _ => "fail"

test "numbers" := numbers == [4, 0, 0, 9]
test "bigOnes" := bigOnes == [9]
test "isMissing" := sample.count isMissing == 1
test "grade" := grade 95 == "distinction" ∧ grade 60 == "pass" ∧ grade 10 == "fail"
