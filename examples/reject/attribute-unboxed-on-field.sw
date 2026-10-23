-- expect-error: E-ATTRIBUTE
-- `js.unboxed` is written on the record, not on its field.
type UserId = { @[js.unboxed] value: Text }
