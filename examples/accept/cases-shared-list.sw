-- Stuck calls that wait for the same list: `cases` splits the list, once,
-- so they compute together (SW-939, from AoC 2021 day 3). Splitting
-- `List.get t 0` and `List.head t` one after the other would leave a case
-- with one `None` and the other `Some`, which can't happen.
import Std (List, Option)

theorem getZeroHead ∀ (t: List Bool): List.get t 0 = List.head t := cases

-- Under a prefix, by recursion on it; `cases` does the last step.
theorem getAfterPrefix ∀ (t prefix: List Bool): List.get (List.append prefix t) (List.length prefix) = List.head t :=
  match prefix with
    | [] => cases
    | [first, ..rest] => getAfterPrefix t rest

def afterBit (bit: Bool): List Bool → Option (List Bool)
  | [] => None
  | [first, ..rest] => if first == bit then Some rest else None

-- Both sides wait for `rest`; then for its first bit.
theorem headAfterBit ∀ (rest: List Bool) (bit: Bool):
    (List.head rest == Some bit) = Option.isSome (afterBit bit rest) :=
  cases

-- From a hypothesis too: it and the goal wait for `t`.
theorem headOfGet ∀ (t: List Nat) (n: Nat) (h: List.get t 0 = Some n): List.head t = Some n := cases
