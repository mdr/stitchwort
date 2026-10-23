-- expect-error: E-ATTRIBUTE
-- `js.unboxed` belongs on a record type, not on a constructor.
type Event =
  | @[js.unboxed] Created (by: Text)
  | Deleted
