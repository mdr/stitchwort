-- expect-error: E-NONEXHAUSTIVE
-- The computation may fail, and there's no clause for that.
import Std (Fail)

theorem same (t: () → {Fail} a): Fail.toResult t = Fail.toResult t :=
  match reify t with
    | return x => rfl
