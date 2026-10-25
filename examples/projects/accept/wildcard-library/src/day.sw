namespace Day

import List (..)
import Lib (..)
import Std (List)

test "library" := List.reverse [1, 2] == [2, 1]
test "project" := Lib.reverse [1, 2] == [1, 2]
test "unqualified" := sum (map [1, 2] (x => x + 1)) == 5
