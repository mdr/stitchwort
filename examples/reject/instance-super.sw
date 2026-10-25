-- expect-error: E-INSTANCE-SUPER
-- A global instance's superclass must be the instance the compiler finds
-- for that parent (docs/proposals/interfaces.md §5.8 (b)), so every route
-- to a `Base Bool` agrees. This one gives another. It's checked, never
-- replaced. The accepted neighbour leaves `base` out, to be filled in:
-- `Child.instNat` in examples/accept/interfaces-superclasses.sw.

interface Base (a: Type) =
  { op: a → a }

interface Child (a: Type) =
  { base: Base a, name: a → Text }

instance Base.instBool: Base Bool :=
  { op = b => b }

def always: Base Bool := { op = b => True }

instance Child.instBool: Child Bool :=
  { base = always, name = b => "bool" }
