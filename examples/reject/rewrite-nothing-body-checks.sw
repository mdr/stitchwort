-- expect-error: E-REWRITE-NOTHING
-- In the `Succ m` branch the goal has computed `depth + Succ (Succ m)` to
-- `Succ (depth + Succ m)`, so `Nat.addSucc` has nothing left to rewrite. The
-- hypothesis `h` after `in` proves the goal as it is, and the message says to
-- drop the `rewrite`.
import Std (Nat)

theorem computedPast (p: Nat → Prop) (depth: Nat) (more: Nat) (h: p (Succ (depth + more))):
    p (depth + Succ more) :=
  match more with
    | Zero => h
    | Succ m => rewrite Nat.addSucc depth m in h
