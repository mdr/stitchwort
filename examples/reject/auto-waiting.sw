-- expect-error: E-AUTO-NONE
-- `decToken` is above `client`, but uses `laterHelper`, which is below it, so
-- it's checked after `client` and `auto` can't use it there yet
-- (docs/proposals/mutual-recursion.md §8.1).
type Token : Prop =
  | MkToken

needsToken : [auto t : Token] -> Nat
needsToken = 1

decToken : Decidable Token
decToken = laterHelper

client : Nat
client = needsToken

laterHelper : Decidable Token
laterHelper = Yes MkToken
