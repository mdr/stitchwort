-- expect-error: E-EXPORT
-- Without `@[js.unboxed]` a one-field record crosses as an object, which
-- can't be a key of a plain object.
import Std (Map, Nat, Text)

type UserId = { value: Text }

export def size (m: Map UserId Nat): Nat := Map.size m
