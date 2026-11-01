-- expect-error: E-TYPE-MISMATCH
-- A mismatch between two calls of a partly applied constructor prints
-- without the lambda's parameter leaking (SW-410). `rfl`, checked after
-- the rest of the call (stage 7), is blamed for `f` and `g`; a proof of
-- the wrong equation gives the mismatch of the two calls.
import Std (Eq)
import Std.Effect (Comp)
import Std.Effect.Comp (Call)

theorem callCong [op: Type] [res: op → Type] [a: Type] (o: op) (f g: res o → Comp op res a)
    (p: f = g): Call o f = Call o g :=
  Eq.cong (Call o) rfl

theorem callCongSame [op: Type] [res: op → Type] [a: Type] (o: op) (f g: res o → Comp op res a)
    (p: f = f): Call o f = Call o g :=
  Eq.cong (Call o) p
