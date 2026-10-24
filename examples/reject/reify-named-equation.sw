-- expect-error: E-PARSE
-- `match h: reify` would give an equation between computations, whose type
-- has no spelling.
import Std (Fail)

theorem same (t: () -> {Fail} a): Fail.toResult t = Fail.toResult t :=
  match h: reify t with
    | return x => rfl
    | Fail.stop msg, _ => rfl
