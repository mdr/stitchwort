-- expect-error: E-AUTO-NONE
-- A decision procedure checked together with its use (they call each
-- other) can't run while they're being checked.
type Token : Prop =
  | MkToken

needsToken : [auto t : Token] -> Nat
needsToken = 1

decToken : Nat -> Decidable Token
decToken 0        = Yes MkToken
decToken (Succ n) = if client n == 0 then Yes MkToken else decToken n

client : Nat -> Nat
client 0        = needsToken
client (Succ n) = if toBool (decToken n) then 0 else client n
