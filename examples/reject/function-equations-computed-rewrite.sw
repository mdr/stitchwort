-- expect-error: E-REWRITE-NOTHING
-- `size.eq1`'s left side is `size []`, which computes: the goal holds `n`
-- already, so the equation has nothing to replace. The note says arm
-- equations are for stuck calls (docs/proposals/function-equations.md §7.3,
-- stage 1c).
import Std (List, Nat)

def size: List Nat → Nat
  | [] => 0
  | Cons _ rest => size rest + 1

theorem sizeNil (n: Nat): size [] + n = n := rewrite size.eq1 in rfl
