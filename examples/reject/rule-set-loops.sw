-- expect-error: E-REWRITE-REPEATEDLY-RULE

import Std (Nat)

-- A set's rules are checked where it is declared, as `rewrite repeatedly`
-- checks its rules: `a + b = b + a` would rewrite forever.
rules commuting := [Nat.addComm]
