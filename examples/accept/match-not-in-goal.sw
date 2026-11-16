-- expect-warning: W-MATCH-NOT-FOUND
-- A named `match` on an expression the goal doesn't contain, whose arms
-- don't use the equation, replaces nothing: every arm has the goal unchanged.
-- It warns, showing the goal where the expression was looked for. Written as
-- the goal shows it, or with the equation used, it doesn't warn.
import Std (Bool, Nat)
import Std.Void (impossible)

def double (n: Nat): Nat := n + n

theorem notFound ∀ (n: Nat): double n = n + n := match h: n * 2 with
  | Zero => byComputing
  | Succ k => byComputing

theorem found ∀ (n: Nat): double n = n + n := match h: n + n with
  | Zero => byComputing
  | Succ k => byComputing

theorem equationUsed ∀ (n: Nat): n = n := match h: Succ n with
  | Zero => impossible (Nat.succNotZero n h)
  | Succ k => byComputing

-- Nothing in the goal or in `b`'s type could be a `Bool`, so the expression
-- isn't computed (SW-1096). It might have computed to the variable `b`, and
-- a `match` on a variable doesn't warn, so this doesn't either.
type Top: Prop = | Intro

def same (b: Bool): Bool := b

theorem variableNormal ∀ (b: Bool): Top := match h: same b with
  | True => Intro
  | False => Intro
