-- expect-error: E-INTERFACE-CYCLE
-- A field whose type is an interface is a superclass, and the superclasses
-- can't form a cycle (docs/proposals/interfaces.md §5.1): `Ping` contains a
-- `Pong`, which contains a `Ping`. The accepted neighbour, an acyclic
-- hierarchy, is `Child` and `Base` in
-- examples/accept/interfaces-superclasses.sw.

interface Ping (a: Type) =
  { pong: Pong a, ping: a -> Text }

interface Pong (a: Type) =
  { ping: Ping a, pong: a -> Text }
