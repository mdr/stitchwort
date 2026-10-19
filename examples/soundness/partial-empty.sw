-- expect-error: E-PARTIAL
-- A partial function can have any result type, even an empty one, because
-- it might never return. Its result must never reach total code, or that
-- would be a value of a type with no values, and so a proof of anything.
type Empty: Type

def spin (n: Nat): {Partial} Empty := spin (n + 1)

def boom: Empty := spin 0

theorem anything: Void := absurdEmpty boom

def absurdEmpty: Empty -> Void
  | ()
