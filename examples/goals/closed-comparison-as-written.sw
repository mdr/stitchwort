-- A goal with no variables left to compute on, like `0 < 1`, shows as
-- written, not as the `True = True` it computes to: in a plain theorem, in
-- each arm of a `match`, with what the arm's pattern made of a variable or
-- an expression put in (`1 * 2 < 3`), and inside a larger statement.
import Std (Nat, Bool)

theorem plain ∀ (n: Nat): 0 < 1 := ?

theorem arms ∀ (n: Nat): 0 < 1 := match n with
  | 0 => ?
  | _ => ?

theorem split ∀ (n: Nat): n * 2 < 3 := match n with
  | 0 => ?
  | 1 => ?
  | _ => ?

theorem nested ∀ (n: Nat): 2 ≤ 3 ∧ n = n := ?

-- A `match` on an expression the goal mentions: each arm shows the
-- statement with the arm's value in its place (`pick True < 2`).
def pick (b: Bool): Nat := if b then 1 else 0

theorem decided ∀ (n: Nat): pick (n == 0) < 2 := match n == 0 with
  | True => ?
  | False => ?

-- A goal that is not the statement's keeps its own: the argument here must
-- prove `0 < 1`, not the `2 < 3` the theorem states.
theorem apart ∀ (h: 0 < 1 → 2 < 3): 2 < 3 := h ?

-- Under a lambda for the statement's `→`, the goal is what it implies.
theorem under ∀ (n: Nat): n = n → 0 < 1 := same => ?
