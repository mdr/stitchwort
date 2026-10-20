-- Superclasses (docs/proposals/interfaces.md §5.8): a field whose type is an
-- interface. An interface record literal that leaves one out has it filled
-- in, before its later fields are checked; a global instance's is checked
-- against the instance found for that parent.

interface Base (a: Type) =
  { op: a -> a }

-- `law` mentions the superclass `base`.
interface Child (a: Type) =
  { base: Base a
  , law: (x: a) -> base.op (base.op x) = base.op x
  }

interface Named (a: Type) =
  { base: Base a
  , name: a -> Text
  }

instance Base.instNat: Base Nat :=
  { op = n => 0 }

-- `base` is filled with `Base.instNat` at once, so `law`'s type computes,
-- to `0 = 0`, and `rfl` proves it.
instance Child.instNat: Child Nat :=
  { law = x => rfl }

-- Given explicitly, it must be the instance found: it is.
instance Named.instNat: Named Nat :=
  { base = Base.instNat, name = n => "nat" }

-- A dictionary in scope gives its superclasses too: `Base a` here is
-- `c.base`.
def twice [auto c: Child a] (x: a): a := Base.op (Base.op x)

-- In a helper, the superclass is filled from the parameter, the only
-- `Base a` in scope.
def namedBy [auto b: Base a] (name: a -> Text): Named a := { name = name }

def describe [auto n: Named a] (x: a): Text := n.name (Base.op x)

-- The literal's type, `Named ?a`, is only fixed by `name`: `base` waits
-- for it, and is found once it's known.
def deferred: Text := describe [n := ({ name = (n: Nat) => "deferred" }: Named _)] 4

test "twice" := twice 5 == 0
test "filled" := (Child.base [child := Child.instNat]).op 7 == 0
test "by path" := Child.instNat.base.op 3 == 0
test "helper" := describe [n := namedBy (n => "helper")] 1 == "helper"
test "deferred" := deferred == "deferred"
test "given" := describe 9 == "nat"
