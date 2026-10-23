-- expect-error: E-ATTRIBUTE
-- A proof field has no property in JavaScript, so it has no key to rename.
type Positive = { value: Nat, @[js.name "ok"] valueOk: 0 < value }
