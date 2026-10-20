-- expect-error: E-INSTANCE-REDUNDANT
-- `Child a` already contains a `Base a`, so asking for both would give two
-- `Base a` dictionaries, which needn't agree (docs/proposals/interfaces.md
-- §5.8 (c)). The accepted neighbour asks for `Child a` alone: `twice` in
-- examples/accept/interfaces-superclasses.sw.

interface Base (a: Type) =
  { op: a -> a }

interface Child (a: Type) =
  { base: Base a, name: a -> Text }

def twice [auto b: Base a] [auto c: Child a] (x: a): a := Base.op (Base.op x)
