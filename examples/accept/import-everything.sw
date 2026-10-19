-- `import N (..)` brings every name declared directly in `N`, below the
-- names imported one by one. `length` is in both namespaces, so it is
-- written in full.
import List (..)
import Text (..)

def total(xs: List Nat): Nat := sum (map (\x => x + 1) (filter (\x => not (x == 0)) (reverse xs)))

test "wildcard names" := total [1, 0, 2] == 5
test "the same name from two namespaces, in full" := List.length [1, 2] + Text.length "abc" == 5
test "split" := List.length (split ',' "a,b") == 2
