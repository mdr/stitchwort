-- expect-error: E-PROOF-ONLY
-- A predicate may use `reify`, but deciding it is data: an instance of
-- `Decidable` would run.
import Std (Fail)

def Finishes (t: () → {Fail} a): Prop :=
  match reify t with
    | return x => Unit
    | Fail.stop msg, _ => Void

instance decFinishes (t: () → {Fail} a): Decidable (Finishes t) :=
  match reify t with
    | return x => Yes Trivial
    | Fail.stop msg, _ => No (v => v)
