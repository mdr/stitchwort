-- expect-error: E-NO-READING
-- `a || b` reads as `a ∨ b`, which `Both` can't take apart; the error says
-- what the test reads as (docs/proposals/bool-as-proposition.md §6.7).
import Std (Bool)

theorem left (a b: Bool) (h: (a || b) = True): a :=
  match h with
    | Both x _ => x
