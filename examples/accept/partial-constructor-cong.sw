-- A constructor with a field still to come (`Call o`) passed where a function
-- is expected, when its type parameters are not yet known: the metavariables
-- for them must not capture the lambda's own parameter.
import Std (Eq)
import Std.Effect (Comp)
import Std.Effect.Comp (Call)

theorem callCong [op: Type] [res: op → Type] [a: Type] (o: op) (f g: res o → Comp op res a)
    (p: f = g): Call o f = Call o g :=
  Eq.cong (Call o) p

theorem someCong (x y: Nat) (p: x = y): Option.Some x = Option.Some y :=
  Eq.cong Option.Some p
