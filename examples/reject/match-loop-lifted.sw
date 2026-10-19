-- expect-error: E-TERMINATION
-- A lifted `match` that recurses on a larger argument isn't terminating.
def loop (n: Nat): Nat := 1 + match Succ n with
               | Zero   => 0
               | Succ k => loop k
