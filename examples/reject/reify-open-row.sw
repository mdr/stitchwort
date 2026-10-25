-- expect-error: E-REIFY
-- An open row may hold abilities it doesn't list; R1 splits closed rows only.
import Std (Fail)

theorem same (t: () → {Fail | e} a): Unit :=
  match reify t with
    | return x => Trivial
    | Fail.stop msg, _ => Trivial
