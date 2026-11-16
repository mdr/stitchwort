-- expect-error: E-ABILITY
-- `Abort.stop` isn't an operation of a `{Fail}` computation.
import Std (Abort, Fail)

theorem same (t: () → {Fail} a): Fail.toResult t = Fail.toResult t :=
  match reify t with
    | return x => byComputing
    | Fail.stop msg, _ => byComputing
    | Abort.stop (), _ => byComputing
