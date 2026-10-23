-- expect-error: E-ATTRIBUTE
-- A proof has no property in JavaScript.
type Positive =
  | MkPositive (n: Nat) (@[js.optional] ok: 0 < n)
