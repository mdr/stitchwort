-- expect-error: E-AUTO-NONE
-- `auto` only uses decision procedures written above where it's used, and
-- `decToken` is below `client`.
type Token : Prop =
  | MkToken

needsToken : [auto t : Token] -> Nat
needsToken = 1

client : Nat
client = needsToken

decToken : Decidable Token
decToken = Yes MkToken
