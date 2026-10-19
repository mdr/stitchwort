namespace N

type Token: Prop =
  | MkToken

def p1: Decidable Token := helper

def needsToken: [auto t: Token] -> Nat := 1

def u: Nat := needsToken
