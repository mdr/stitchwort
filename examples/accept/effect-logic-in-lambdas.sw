-- `&&` and `||` in a lambda passed to an effect-polymorphic function, such as
-- `List.all`'s test `a → {e} Bool`, whose right side calls another one
-- (`List.any`). The lambda is elaborated as a computation, and once its row
-- is empty it computes to the term the same text gets in a pure function, so
-- a statement and its proof can write the test either way and `rfl` closes
-- the gap.
import Std (List)

def keptBy (page: Nat) (later: List Nat) (rule: Nat): Bool := !(page == rule) || !(later.any (== rule))

theorem allKeptBy (page: Nat) (rules later: List Nat):
    rules.all (rule => !(page == rule) || !(later.any (== rule))) = rules.all (keptBy page later) :=
  rfl

-- Both sides of `||` call effect-polymorphic functions.
def eitherCalls (pages: List Nat) (page: Nat): Bool := pages.any (== page) || pages.all (== page)

theorem anyEitherCalls (pages later: List Nat):
    later.any (page => pages.any (== page) || pages.all (== page)) = later.any (eitherCalls pages) :=
  rfl

-- `&&` with a call on the left and a pure comparison on the right.
def bothCallFirst (limit: Nat) (pages: List Nat) (page: Nat): Bool := pages.any (== page) && page < limit

theorem allBothCallFirst (limit: Nat) (pages later: List Nat):
    later.all (page => pages.any (== page) && page < limit) = later.all (bothCallFirst limit pages) :=
  rfl

-- A decided proposition on the left of `&&` and of `||`.
def bothCompareFirst (limit: Nat) (pages: List Nat) (page: Nat): Bool := limit < page && pages.any (== page)

theorem anyBothCompareFirst (limit: Nat) (pages later: List Nat):
    later.any (page => limit < page && pages.any (== page)) = later.any (bothCompareFirst limit pages) :=
  rfl

def eitherCompareFirst (pages: List Nat) (page: Nat): Bool := pages.length < page || pages.any (== page)

theorem allEitherCompareFirst (pages later: List Nat):
    later.all (page => pages.length < page || pages.any (== page)) = later.all (eitherCompareFirst pages) :=
  rfl

-- Nested: `(a && !b) || c`, each part a call or a comparison.
def mixed (pages: List Nat) (page: Nat): Bool := pages.any (== page) && !(pages.all (== page)) || pages.length == page

theorem anyMixed (pages later: List Nat):
    later.any (page => pages.any (== page) && !(pages.all (== page)) || pages.length == page) = later.any (mixed pages) :=
  rfl

test "kept by" := [1, 2].all (rule => !(3 == rule) || !([3].any (== rule)))
test "not kept by" := !([3].all (rule => !(3 == rule) || !([3].any (== rule))))
test "both compare first" := [5, 6].any (page => 4 < page && [6].any (== page))
