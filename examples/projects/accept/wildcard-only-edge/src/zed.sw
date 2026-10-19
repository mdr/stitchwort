namespace Zed

type Token: Prop =
  | MkToken

def needsToken: [auto t: Token] -> Nat := 1

def decZ: Decidable Token := Yes MkToken

test "zed" := needsToken == 1
