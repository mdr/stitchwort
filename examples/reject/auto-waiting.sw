-- expect-error: E-AUTO-NONE
-- `decToken` is above `client`, but uses `laterHelper`, which is below it, so
-- it's checked after `client` and `auto` can't use it there yet
-- (docs/proposals/mutual-recursion.md §8.1).
type Token : Prop =
  | MkToken

def needsToken : [auto t : Token] -> Nat := 1

def decToken : Decidable Token := laterHelper

def client : Nat := needsToken

def laterHelper : Decidable Token := Yes MkToken
