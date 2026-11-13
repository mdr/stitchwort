-- `cases` takes a record apart before the stuck call's own result: `same x x`
-- waits on `x`, so `x` is split (one case) and `n == n` then closes. Splitting
-- the result first left the case `same x x = False`, which reads as if the
-- statement were false (SW-2840).
import Std (Bool, Nat)

type Tag =
  | MkTag (n: Nat)

def same (a b: Tag): Bool := match a, b with
  | MkTag n, MkTag m => n == m

theorem sameRefl ∀ (x: Tag): same x x = True := cases
