-- expect-error: E-REWRITE-NOTHING
-- `rewrite … in` rewrites the goal; here only the hypothesis `sized` has
-- `size a`, so the note suggests naming it with `at`.

import Std (Nat)

theorem sizedSame (size: Nat → Nat) (a: Nat) (b: Nat) (fixed: size a = a) (sized: size a = b): a = b :=
  rewrite fixed in sized
