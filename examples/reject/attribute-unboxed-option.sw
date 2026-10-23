-- expect-error: E-ATTRIBUTE
-- Unboxed, an `Option` of this record would have two values that are
-- `undefined`: `None` and `Some { value = None }`.
@[js.unboxed]
type Nickname = { value: Option Text }
