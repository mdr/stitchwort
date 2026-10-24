import Std (List)

-- Declaring a type gives it equality (`==`), ordering and text for free,
-- as long as every field supports them.
type Priority = | Low | Medium | High

type Ticket = { title: Text, priority: Nat }

def a: Ticket := { title = "fix bug", priority = 2 }
def b: Ticket := { title = "fix bug", priority = 3 }

test "equality" := a == a && !(a == b)
test "ordering" := Ord.compare Low High == Less
test "sorting" := List.sort [High, Low, Medium] == [Low, Medium, High]
test "sorting records" := List.sort [b, a] == [a, b]
test "text" := "${Medium} and ${a}" == "Medium and { title = \"fix bug\", priority = 2 }"
