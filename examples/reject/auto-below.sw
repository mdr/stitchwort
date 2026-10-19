-- expect-error: E-AUTO-NONE
-- `auto` only uses decision procedures written above where it's used, and
-- `decToken` is below `client`.
type Token: Prop =
  | MkToken

def needsToken: [auto t: Token] -> Nat := 1

def client: Nat := needsToken

def decToken: Decidable Token := Yes MkToken
