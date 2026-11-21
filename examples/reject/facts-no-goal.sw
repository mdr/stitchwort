-- expect-error: E-FACTS
-- With nothing saying what it proves, `byFacts` asks for a type.

def noGoal: Nat :=
  let proof := byFacts
  3
