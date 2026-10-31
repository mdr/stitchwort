-- An imported namespace never hides another meaning of its name: each use
-- is E-AMBIGUOUS, listing the full names. A use of the full name is fine.
namespace Use

import Day12 (Spec)
import Day13 (Spec)
import Lib (List)

-- Two imported namespaces called `Spec`.
test "two specs" := Spec.answer == 12

test "in full" := Day13.Spec.answer == 13

-- An imported namespace `List`, and the prelude's type `List`.
test "list" := List.length [1] == 1
