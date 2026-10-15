-- expect-error: E-ABILITY
-- `twice` may only choose, but `logged` also logs.
ability Choose where
  choose : () -> {Choose} Bool

ability Log where
  say : Nat -> {Log} ()

logged : () -> {Log, Choose} Bool
logged u =
  say 1
  choose ()

twice : () -> {Choose} Bool
twice u = logged ()
