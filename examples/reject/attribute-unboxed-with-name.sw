-- expect-error: E-ATTRIBUTE
-- An unboxed record's field has no key to rename.
@[js.unboxed]
type UserId = { @[js.name "id"] value: Text }
