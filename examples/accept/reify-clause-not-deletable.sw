-- Every clause of a `match reify` is required (`E-NONEXHAUSTIVE` without
-- it), so one whose case a hypothesis rules out is not offered for deletion:
-- no `W-UNREACHABLE`. Here `h` is `Ok x = Err "no"` in the `return` clause.

import Std (Eq, Fail, Result, Void)

theorem alwaysFails ∀ (t: () → {Fail} Nat) (h: Fail.toResult (() => t ()) = Err "no"): Fail.toResult (() => t ()) = Err "no" :=
  match reify t with
    | return x => Void.exfalso (Result.errNotOk (Eq.sym h))
    | Fail.stop msg, _ => h
