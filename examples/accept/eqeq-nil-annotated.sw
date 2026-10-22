-- `==` on empty lists works once the element type is known (SW-108).

import Std (Bool)

test "annotated nil" := (Nil: List Nat) == Nil
test "annotated brackets" := ([]: List Text) == []
test "unannotated, from the other side" := !([] == [1])
