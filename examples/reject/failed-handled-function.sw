-- expect-error: E-UNKNOWN-NAME
-- A proof about a handled computation whose function has an error: only the
-- error in the function is reported, not a mismatch in the proof.

def greet(): {IO} () :=
  let unused := notDefinedAnywhere
  IO.print "Hello"

theorem greetOutput: Pair.fst (IO.simulate [] greet) = ["Hello"] := rfl
