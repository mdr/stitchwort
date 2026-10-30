-- expect-error: E-CASES
-- Which variable the fallback splits first, and how many cases it makes,
-- shown by a statement false in one of them (examples/accept/cases-fallback.sw,
-- `keyFewest`, with `Enter` left out of the list). Fewest cases first splits
-- `flag` (2 against 11), so the open case's path starts with it. The case
-- `flag = True` is closed whole by `omega` (`… ∨ True = True`) before
-- anything else is split, so `key` is split only when `flag = False`: 12
-- cases, 11 closed and `flag = False, key = Enter` open.
import Std (Bool, List)

type NumericKey =
  | Digit0
  | Digit1
  | Digit2
  | Digit3
  | Digit4
  | Digit5
  | Digit6
  | Digit7
  | Digit8
  | Digit9
  | Enter

def digits: List NumericKey := [Digit0, Digit1, Digit2, Digit3, Digit4, Digit5, Digit6, Digit7, Digit8, Digit9]

theorem keyFewest (flag: Bool) (key: NumericKey): Or (key ∈ digits) (flag = True) := cases
