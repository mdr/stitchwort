-- Sorting doubles by JS's `<=` (`Float.ieeeLe`), which is total only
-- without the NaN: `List.sortWithSortedOn` needs totality only on the
-- values the elements are (here, every double but the NaN), and
-- `List.pairwiseOfSortedOn` transitivity only there (std/List/SortLemmas.sw,
-- with the order's laws from std/Float/Float.sw).
import Std (Bool, List, Float)

def NotNaN (x: Float): Prop := Float.isNaN x = False

theorem sortedByIeeeLe (xs: List Float) (clean: List.All NotNaN xs): List.Sorted Float.ieeeLe (List.sortWith xs Float.ieeeLe) :=
  List.sortWithSortedOn Float.ieeeLe NotNaN (x y nx ny h => Float.ieeeLeTotal x y nx ny h) xs clean

-- With transitivity, each element is at most every later one.
theorem pairwiseByIeeeLe (xs: List Float) (clean: List.All NotNaN xs):
    List.Pairwise (x y => Float.ieeeLe x y = True) (List.sortWith xs Float.ieeeLe) :=
  List.pairwiseOfSortedOn Float.ieeeLe NotNaN (x y z px py pz h1 h2 => Float.ieeeLeTrans x y z h1 h2) (List.sortWith xs Float.ieeeLe)
    (List.allSortWith Float.ieeeLe NotNaN xs clean) (sortedByIeeeLe xs clean)

-- The NaN is why the hypothesis is needed: `<=` is false on it both ways.
theorem nanNotLe (x: Float) (h: Float.ieeeLe Float.nan x = True): Void :=
  Bool.trueNotFalse (And.left (Float.ieeeLeNotNaN Float.nan x h))

-- Stable: `0.0` and `-0.0` are equal under `<=`, so they keep their order.
test "sorted by <=" := List.sortWith [2.5, -1.0, 0.0, -0.0] Float.ieeeLe == [-1.0, 0.0, -0.0, 2.5]
