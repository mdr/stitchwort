-- expect-error: E-TYPE-MISMATCH
import Std (Eq)
import Std.Effect (Comp)
import Std.Effect.Comp (Call)

theorem callCong [op: Type] [res: op → Type] [a: Type] (o: op) (f g: res o → Comp op res a)
    (p: f = g): Call o f = Call o g :=
  Eq.cong (Call o) rfl
