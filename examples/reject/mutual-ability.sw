-- expect-error: E-MUTUAL-KIND
-- An ability whose operation returns a type that stores computations using
-- the ability: Landin's knot (DESIGN.md §8). Data types can be defined
-- together, but not with an ability.
ability Ask where
  ask : () -> {Ask} Box

type Box : Type =
  | MkBox (run : Nat -> {Ask} Nat)
