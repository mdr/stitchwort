-- expect-error: E-REWRITE-NO-RULES
-- Every arm of `len` is a constructor pattern, so a call on a constructor
-- computes at once and there are no rules to rewrite with. Asking for it
-- alone is reported at its name, not left as an empty rule list.
import Std (Bool, Eq, List, Nat)

def len (xs: List Nat): Nat := match xs with
  | [] => 0
  | [_, ..rest] => len rest + 1

theorem a ∀ (xs: List Nat): len xs = len xs := rewrite repeatedly [len] then byComputing
