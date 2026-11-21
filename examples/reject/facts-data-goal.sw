-- expect-error: E-FACTS
-- `byFacts` proves propositions. Against a type of data it would return
-- whichever value fitted first (here `n`), so it is refused before it looks.

def pick (n: Nat): Nat := byFacts [n]
