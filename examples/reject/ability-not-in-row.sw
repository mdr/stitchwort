-- expect-error: E-ABILITY
-- `twice` may only choose, but `logged` also logs.
ability Choose where
  choose : () -> {Choose} Bool

ability Log where
  say : Nat -> {Log} ()

def logged () : {Log, Choose} Bool :=
  say 1
  choose ()

def twice () : {Choose} Bool := logged ()
