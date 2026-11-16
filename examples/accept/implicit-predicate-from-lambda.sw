-- A lemma whose conclusion applies an implicit predicate to a value
-- (`holds 0`, `holds n`) learns the predicate from its lambda, checked in
-- place, and then meets the goal. This is not `Parse.readsThen`'s shape
-- (an unknown applied to what another computes), so its lambda isn't held
-- for the goal (SW-3561's review, F1): held, the goal would meet `?holds
-- 0`, which says nothing.
import Std (Nat)

theorem atZero ∀ [holds: Nat → Prop] (all: ∀ (k: Nat) => holds k): holds 0 := all 0

theorem useZero: 0 * 1 = 0 := atZero (k => Std.Nat.mulOne k)

theorem atAny ∀ [holds: Nat → Prop] [n: Nat] (all: ∀ (k: Nat) => holds k): holds n := all n

theorem useAtAny ∀ (m: Nat): m * 1 = m := atAny (k => Std.Nat.mulOne k)

theorem atAnyFixed ∀ [holds: Nat → Prop] [n: Nat] (which: n = n) (all: ∀ (k: Nat) => holds k): holds n := all n

theorem useFixed ∀ (m: Nat): m * 1 = m := atAnyFixed (byComputing: m = m) (k => Std.Nat.mulOne k)
