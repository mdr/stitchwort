-- expect-error: E-PARSE
-- A syntax error nothing smaller recovers from skips the rest of the body:
-- the definition is failed, its statement stands in for it, so `usesHalf`
-- checks against it, and `wrong`'s own mistake is still reported. A body
-- that runs out after `:=` is missing, not absent: `later` is a definition
-- with a syntax error, not a primitive.
def half (n: Nat): Nat :=
  let a := n + ) 1
  a / 2

def usesHalf: Nat := half 4 + 1

def later: Nat :=

def usesLater: Nat := later

def wrong: Nat := "x"
