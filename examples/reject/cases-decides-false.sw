-- expect-error: E-CASES
-- A case whose goal decides `No`, and nothing else closes it: the error
-- names the case and says that the goal's decision procedure says it is
-- false.
import Std (Bool, List)

type Key =
  | K0
  | K1
  | K2

def pick (b: Bool): Key := if b then K2 else K1

theorem pickIn (b: Bool): pick b ∈ [K0, K1] := cases
