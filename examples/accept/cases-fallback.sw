-- `cases`' fallback split (docs/proposals/decide.md §6.1.3): when the goal
-- isn't stuck on anything and nothing closes it, `cases` splits a variable
-- the goal mentions anyway, the one whose split makes the fewest cases, ties
-- to the latest bound, and goes on in each case.
import Std (Bool, List)

type Direction =
  | Up
  | Down
  | Left
  | Right

type DirectionKey =
  | Arrow (direction: Direction)
  | Activate

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

def numericKeys: List NumericKey := [Digit0, Digit1, Digit2, Digit3, Digit4, Digit5, Digit6, Digit7, Digit8, Digit9, Enter]

def directionKeys: List DirectionKey := [Arrow Up, Arrow Down, Arrow Left, Arrow Right, Activate]

-- Day 21's `everyNumericKey`: `key ∈ numericKeys` computes to a disjunction
-- of equations, not stuck on `key`, so `key` is split as a fallback, and
-- each of the 11 cases decides `Yes`.
theorem everyNumericKey: (key: NumericKey) → key ∈ numericKeys := cases

-- `key` (2 cases), then in the `Arrow d` case `d` (4): 5 cases.
theorem everyDirectionKey: (key: DirectionKey) → key ∈ directionKeys := cases

type Month =
  | Jan
  | Feb
  | Mar
  | Apr
  | May
  | Jun
  | Jul
  | Aug
  | Sep
  | Oct
  | Nov
  | Dec

-- The rule itself: decide/fallback.sw's two statements, written out by hand
-- there. Only `flag` matters, and fewest cases first splits it (2 against
-- 12): 2 cases, where latest first would make 24.
theorem flagFewest (flag: Bool) (month: Month): Or (flag = True) (Or (flag = False) (month = month)) := cases

-- The same with two months: latest first would split `later`, then
-- `earlier`, 144 cases, past the budget; fewest first makes 2.
theorem flagFewestOfThree (flag: Bool) (earlier: Month) (later: Month): Or (flag = True) (Or (flag = False) (earlier = later)) := cases

-- Only `key` matters, but fewest first splits `flag` (2 against 11). The
-- case `flag = True` is closed whole by `omega` (`… ∨ True = True`), so
-- `key` is split only when `flag = False`: 12 cases, not the 22 that
-- deciding alone would make (decide/fallback.sw, by hand). The order shows
-- in examples/reject/cases-fallback-count.sw.
theorem keyFewest (flag: Bool) (key: NumericKey): Or (key ∈ numericKeys) (flag = True) := cases
