-- Abilities, interfaces and instances.
ability State (s: Type) where
  get: () -> {State s} s
  put: s -> {State s} ()

interface Sizable (a: Type) = {
  size: a -> Nat,
  empty: a -> Bool
}

instance Nat.instSizable: Sizable Nat := {
  size = n => n,
  empty = n => n == 0
}
