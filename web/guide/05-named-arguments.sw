-- Name an argument with `(name := value)`. Named arguments can come in any
-- order and be mixed with positional ones.
def clamp (value: Nat) (low: Nat) (high: Nat): Nat :=
  if value < low then low else if value > high then high else value

test "in any order" := clamp (value := 50) (high := 10) (low := 0) == 10
test "mixed with positional" := clamp 50 (high := 10) (low := 0) == 10

-- Leave some out and you get a function of the rest, in their order.
def atMostHundred: Nat → Nat := clamp (low := 0) (high := 100)

test "a function of the rest" := [5, 500].map atMostHundred == [5, 100]

-- Pipes and dot notation take names too.
test "in a pipe" := (500 |> clamp (low := 0) (high := 100)) == 100
