-- An interface says what operations a type must support; an instance
-- provides them. The compiler finds the instance from the type.
interface Describe (a: Type) =
  { describe: a → Text }

type Order = { id: Nat, total: Nat }

instance Order.instDescribe: Describe Order :=
  { describe = o => "order ${o.id} for ${o.total}" }

-- `[auto Describe a]` asks for an instance for whatever `a` the caller uses.
def describeAll [auto Describe a] (xs: List a): List Text := xs.map Describe.describe

def orders: List Order := [{ id = 1, total = 30 }, { id = 2, total = 5 }]

test "describe orders" := describeAll orders == ["order 1 for 30", "order 2 for 5"]
