-- expect-error: E-AUTO-NONE
-- A decision procedure checked together with its use (they call each
-- other) can't run while they're being checked.
type Token: Prop =
  | MkToken

def needsToken: [auto t: Token] -> Nat := 1

def decToken: Nat -> Decidable Token
  | 0      => Yes MkToken
  | Succ n => if client n == 0 then Yes MkToken else decToken n

def client: Nat -> Nat
  | 0      => needsToken
  | Succ n => if Decidable.toBool (decToken n) then 0 else client n
