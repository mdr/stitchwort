namespace Day

import List (..)
import Lib (..)

test "library" := List.reverse [1, 2] == [2, 1]
test "project" := Lib.reverse [1, 2] == [1, 2]
test "unqualified" := sum (map (\x => x + 1) [1, 2]) == 5
