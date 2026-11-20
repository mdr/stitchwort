-- Shows: rewrite repeatedly [len], every arm of len a constructor pattern and so left out, panics (repeatedly.rs:833, index out of bounds on an empty rule list) instead of an error. The guarded walkR of sibling-rewrite.sw panics the same way.
import Std (Bool, Eq, List, Nat)

def len (xs: List Nat): Nat := match xs with
  | [] => 0
  | [_, ..rest] => len rest + 1

theorem a ∀ (xs: List Nat): len xs = len xs := rewrite repeatedly [len] then byComputing
