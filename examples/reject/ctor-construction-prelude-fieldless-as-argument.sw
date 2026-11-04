-- expect-error: E-PARSE
-- The same for a constructor from the prelude, which this file doesn't
-- declare.

def d: Option (Option Nat) := Some None { value = 1 }
