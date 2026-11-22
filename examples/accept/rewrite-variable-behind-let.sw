-- A `rewrite` by a hypothesis about a variable reaches the copies of the
-- variable behind a `let`, a lambda or a local definition that the goal
-- shows only by name: a `let` slot computes to its value, never to a
-- variable of its own (docs/proposals/let.md §6.1), a lambda closes over
-- the value, and a local definition is lifted with the variable as an
-- argument. So the completeness check's shortcut for a variable (a motive
-- that doesn't mention it has no copy hidden in a call, SW-4469) holds
-- here, and each goal is closed by computing (SW-4606).
import Std (Nat)

def double (n: Nat): Nat := n + n

theorem cheapLet ∀ (x: Nat) (h: x = 5): x + double (x + 1) = 17 :=
  let y := x + 1
  (rewrite h: x + double y = 17)

theorem lambdaLet ∀ (x: Nat) (h: x = 5): x + (x + 1) = 11 :=
  let f := (n: Nat) => n + x
  (rewrite h: x + f 1 = 11)

theorem localDef ∀ (x: Nat) (h: x = 5): x + (x + 1) = 11 :=
  def g (n: Nat): Nat := match n with
    | Zero => x
    | Succ k => Succ (g k)
  (rewrite h: x + g 1 = 11)
