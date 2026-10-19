-- expect-error: E-PARSE
-- After `=`, a sum type's constructors each start with `|`; without it
-- `type T = Foo (x : Nat)` would be a synonym, so it's refused.
type T = Foo (x : Nat)
