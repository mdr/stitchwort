-- expect-error: E-PARSE
-- Handler clauses don't take conditions.

ability Log where
  say: Nat → {Log} ()

def run (n: Nat): Nat :=
  handle say n with
    | return x if True => 0
