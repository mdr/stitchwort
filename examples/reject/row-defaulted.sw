-- expect-error: E-TYPE-MISMATCH
-- A row nothing decides is set to the empty row at the end of the
-- declaration (D1124). Here `countAll answer` is never run, so nothing says
-- which abilities it may perform, and `answer`'s result type `Answer ?flag`
-- is stuck on a flag nothing solves. Once the row is empty, `Answer ?flag`
-- must be `Nat`, which can't be shown: the error points at the call whose
-- row was set to empty.
import Std (List)

def Answer: Bool -> Type
  | True => Text
  | False => Nat

type Tagged (flag: Bool): Type =
  | Tag (n: Nat)

def answer [flag: Bool] (tagged: Tagged flag): Answer flag := match flag with
  | True => "t"
  | False => 0

def countAll [flag: Bool] (f: Tagged flag -> {e} Nat) (xs: List (Tagged flag)): {e} Nat := match xs with
  | Nil => 0
  | Cons x rest =>
    let n := f x
    let m := countAll f rest
    n + m

def neverSolved: Nat :=
  let counter := countAll answer
  0
