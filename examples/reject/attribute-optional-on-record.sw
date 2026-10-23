-- expect-error: E-ATTRIBUTE
-- A record's `Option` field is already an optional property.
type Point = { x: Nat, @[js.optional] label: Option Text }
