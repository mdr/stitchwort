-- The proposition and its decision procedure.
namespace N

type Token: Prop =
  | MkToken

instance decToken: Decidable Token := Yes MkToken

def needsToken: [auto t: Token] -> Nat := 1
