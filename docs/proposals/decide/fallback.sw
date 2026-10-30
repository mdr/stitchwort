-- R2 (review-1.md §4): which variable should the fallback split take, when
-- the goal isn't stuck on any? Neither order can run today (the fallback
-- isn't built), so each is written out by hand: the `match`es are the splits
-- the fallback would make, in the order each heuristic picks, and each leaf
-- is `byDecision`, the term the decision closer would write. The leaf counts
-- are the cases each heuristic makes.
--
-- Today neither statement is proved by `cases in byDecision`: the goal isn't
-- stuck on either variable (an equation with a variable side isn't a `case`
-- on it), so nothing is split, and `byDecision` on the whole goal gives
--   [E-AUTO-STUCK] Error: can't decide `key ∈ numericKeys ∨ flag = True` here
import Std (Bool, List)

def byDecision [p: Prop] [auto h: p]: p := h

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

-- 1. Only `flag` matters; `month` is mentioned but decides nothing.
-- Fewest cases first splits `flag` (2 cases against 12): 2 leaves.
theorem flagFewest (flag: Bool) (month: Month): Or (flag = True) (Or (flag = False) (month = month)) :=
  match flag with
    | True => byDecision
    | False => byDecision

-- Latest first splits `month` (bound last), then `flag` in each: 24 leaves.
theorem flagLatest (flag: Bool) (month: Month): Or (flag = True) (Or (flag = False) (month = month)) :=
  match month with
    | Jan =>
      match flag with
        | True => byDecision
        | False => byDecision
    | Feb =>
      match flag with
        | True => byDecision
        | False => byDecision
    | Mar =>
      match flag with
        | True => byDecision
        | False => byDecision
    | Apr =>
      match flag with
        | True => byDecision
        | False => byDecision
    | May =>
      match flag with
        | True => byDecision
        | False => byDecision
    | Jun =>
      match flag with
        | True => byDecision
        | False => byDecision
    | Jul =>
      match flag with
        | True => byDecision
        | False => byDecision
    | Aug =>
      match flag with
        | True => byDecision
        | False => byDecision
    | Sep =>
      match flag with
        | True => byDecision
        | False => byDecision
    | Oct =>
      match flag with
        | True => byDecision
        | False => byDecision
    | Nov =>
      match flag with
        | True => byDecision
        | False => byDecision
    | Dec =>
      match flag with
        | True => byDecision
        | False => byDecision

-- 2. Only `key` matters, and `Decidable.or` decides left to right, so a
-- stuck left side is stuck even when the right side is true.
-- Latest first splits `key` (bound last): 11 leaves.
theorem keyLatest (flag: Bool) (key: NumericKey): Or (key ∈ numericKeys) (flag = True) :=
  match key with
    | Digit0 => byDecision
    | Digit1 => byDecision
    | Digit2 => byDecision
    | Digit3 => byDecision
    | Digit4 => byDecision
    | Digit5 => byDecision
    | Digit6 => byDecision
    | Digit7 => byDecision
    | Digit8 => byDecision
    | Digit9 => byDecision
    | Enter => byDecision

-- Fewest cases first splits `flag` (2 against 11); in each case the goal is
-- still stuck on `key`, so `key` next: 22 leaves.
theorem keyFewest (flag: Bool) (key: NumericKey): Or (key ∈ numericKeys) (flag = True) :=
  match flag with
    | True =>
      match key with
        | Digit0 => byDecision
        | Digit1 => byDecision
        | Digit2 => byDecision
        | Digit3 => byDecision
        | Digit4 => byDecision
        | Digit5 => byDecision
        | Digit6 => byDecision
        | Digit7 => byDecision
        | Digit8 => byDecision
        | Digit9 => byDecision
        | Enter => byDecision
    | False =>
      match key with
        | Digit0 => byDecision
        | Digit1 => byDecision
        | Digit2 => byDecision
        | Digit3 => byDecision
        | Digit4 => byDecision
        | Digit5 => byDecision
        | Digit6 => byDecision
        | Digit7 => byDecision
        | Digit8 => byDecision
        | Digit9 => byDecision
        | Enter => byDecision
