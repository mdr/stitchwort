-- expect-error: E-JS-NAME-CLASH
-- Assigning the key `__proto__` sets an object's prototype instead of
-- making a property, so no field may have it (a tag value may).
type Shape =
  | @[js.name "__proto__"] Circle (@[js.name "__proto__"] radius: Nat)
