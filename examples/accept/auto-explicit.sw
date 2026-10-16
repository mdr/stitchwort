-- A decision procedure passed explicitly is a dependency, so it's checked
-- first, wherever it's written (compare reject/auto-below.sw and
-- reject/auto-waiting.sw).
type Token : Prop =
  | MkToken

needsToken : [auto t : Token] -> Nat
needsToken = 1

client : Nat
client = needsToken [t := Decidable.fromYes decToken Trivial]

decToken : Decidable Token
decToken = laterHelper

laterHelper : Decidable Token
laterHelper = Yes MkToken

test "client" = client == 1
