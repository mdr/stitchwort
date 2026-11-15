-- expect-error: E-TERMINATION
-- Pairs with accept/text-patterns-prefix-recursion.sw: the rest after an
-- empty start is the text itself, and `"a" ++ rest` put back together is
-- the matched text, so both call themselves on the same text for ever.
import Std (Nat, Text)

def emptyStart: Text → Nat
  | "" ++ rest => emptyStart rest

def putBack: Text → Nat
  | "a" ++ rest => putBack ("a" ++ rest)
  | _ => 0
