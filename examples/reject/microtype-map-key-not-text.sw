-- expect-error: E-EXPORT
-- A plain object's keys are strings: a microtype over `Nat` can't be one.
import Std (Map, Nat)

@[js.unboxed]
type Count = { value: Nat }

export def size (m: Map Count Nat): Nat := Map.size m
