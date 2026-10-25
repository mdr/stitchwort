-- A proposition with a function that needs it proved by `auto`.
namespace Base

type Token: Prop =
  | MkToken

def needsToken: [auto t: Token] → Nat := 1
