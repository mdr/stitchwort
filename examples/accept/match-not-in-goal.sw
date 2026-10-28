-- expect-warning: W-MATCH-NOT-FOUND
-- A named `match` on an expression the goal doesn't contain, whose arms
-- don't use the equation, replaces nothing: every arm has the goal unchanged.
-- It warns, showing the goal where the expression was looked for. Written as
-- the goal shows it, or with the equation used, it doesn't warn.
import Std (Nat)
import Std.Void (exfalso)

def double (n: Nat): Nat := n + n

theorem notFound (n: Nat): double n = n + n :=
  match h: n * 2 with
    | Zero => rfl
    | Succ k => rfl

theorem found (n: Nat): double n = n + n :=
  match h: n + n with
    | Zero => rfl
    | Succ k => rfl

theorem equationUsed (n: Nat): n = n :=
  match h: Succ n with
    | Zero => exfalso (Nat.succNotZero n h)
    | Succ k => rfl
