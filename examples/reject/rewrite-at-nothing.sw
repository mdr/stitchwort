-- expect-error: E-REWRITE-NOTHING
-- `rewrite … at h` searches the type of `h`, not the goal: `h` is about `n`,
-- so there is no `d` in it to replace.
import Std (Bool)
theorem bad (d: Nat) (n: Nat) (e: d = 0) (h: 1 <= n): d != 0 :=
  x => Bool.falseNotTrue (rewrite e at h)
