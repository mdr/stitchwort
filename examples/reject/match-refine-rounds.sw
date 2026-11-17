-- expect-error: E-MATCH-ROUNDS
-- `byComputing` rewrites a scrutinee the goal uncovers along the `match`'s
-- equation, but only so many times: `chain n 20 (spare n)` uncovers one
-- more `spare n` each time the last is replaced by `True`. With 2 it is
-- three rounds and checks (match-refinement.md R3).
import Std (Bool, Nat)

def spare (n: Nat): Bool := 10 < n

def chain (n k: Nat) (b: Bool): Bool := match b with
  | False => False
  | True =>
    match k with
      | 0 => True
      | Succ k => chain n k (spare n)

theorem few ∀ (n: Nat): chain n 2 (spare n) = spare n := match s: spare n with
  | True => byComputing
  | False => byComputing

theorem many ∀ (n: Nat): chain n 20 (spare n) = spare n := match s: spare n with
  | True => byComputing
  | False => byComputing
