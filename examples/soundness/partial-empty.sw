-- expect-error: E-PARTIAL
-- A partial function can have any result type, even an empty one, because
-- it might never return. Its result must never reach total code, or that
-- would be a value of a type with no values, and so a proof of anything.
type Empty : Type

spin : Nat -> {Partial} Empty
spin n = spin (n + 1)

boom : Empty
boom = spin 0

theorem anything : Void
anything = absurdEmpty boom

absurdEmpty : Empty -> Void
absurdEmpty ()
