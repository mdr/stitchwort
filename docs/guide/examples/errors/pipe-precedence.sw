import Std (List)

test "evens" := [1, 2, 3, 4] |> .filter (n => n % 2 == 0) == [2, 4]
