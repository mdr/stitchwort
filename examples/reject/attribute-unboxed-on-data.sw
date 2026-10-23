-- expect-error: E-ATTRIBUTE
-- `js.unboxed` is for a record with one field: a data type with
-- constructors crosses as tagged objects.
@[js.unboxed]
type Shape =
  | Dot
  | Circle (radius: Nat)
