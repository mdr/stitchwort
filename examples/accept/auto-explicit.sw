-- A decision procedure passed explicitly is a dependency, so it's checked
-- first, wherever it's written (compare reject/auto-below.sw and
-- reject/auto-waiting.sw).
type Token: Prop =
  | MkToken

def needsToken: [auto t: Token] -> Nat := 1

def client: Nat := needsToken [t := Decidable.fromYes decToken Trivial]

def decToken: Decidable Token := laterHelper

def laterHelper: Decidable Token := Yes MkToken

test "client" := client == 1
