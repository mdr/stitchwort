-- expect-error: E-ATTRIBUTE
-- A record crosses as an object without a tag.
@[js.tag "type"]
type Point = { x: Nat, y: Nat }
