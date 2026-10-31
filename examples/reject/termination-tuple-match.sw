-- expect-error: E-TERMINATION
-- Matching on a tuple of the parameters hides that `later` is a part of
-- `columns`: the patterns take apart the tuple `(numbers, columns)`, not
-- `columns`. The message says so, and that `match numbers, columns with`
-- (without the brackets) is structural (SW-941, from AoC 2021 day 3).
def rating (columns: Nat) (numbers: List (List Bool)): Option (List Bool) :=
  match (numbers, columns) with
    | ([number], _) => Some number
    | (_, Zero) => None
    | (_, Succ later) => rating later numbers
