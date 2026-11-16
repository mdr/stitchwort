-- expect-error: E-PARSE
-- The body of a `rewrite` follows `then` (D3648); the old spelling with
-- `in` is an error naming `then`.
import Std (Nat)

theorem swap (a b: Nat) (h: a = b): b = a :=
  rewrite h in byComputing
