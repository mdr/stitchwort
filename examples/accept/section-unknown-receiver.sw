-- A method section whose argument's type isn't known where it's written
-- waits for it (docs/proposals/postponement.md, K3). `.drop 1` is
-- `x => x.drop 1`; bound by a `let`, nothing says what `x` is until `g xs`
-- does, and then `drop` is looked up in `List`'s namespace. Before the
-- postponement queue this was rejected with "can't tell what `.drop` is
-- applied to"; a section nothing ever applies still is
-- (`examples/reject/section-never-applied.sw`).

import Std (List, Nat, Pair)

def f (xs: List Nat): List Nat :=
  let g := .drop 1
  g xs

-- At the head of an application: `"abcd"` says what it takes, and the `Nat`
-- expected of the application what it gives.
def four: Nat := (.length) "abcd"

-- A section holding another: `.length` waits for `.map`'s list to be known.
def lengths (xss: List (List Nat)): List Nat :=
  let each := .map .length
  each xss

-- Passed before the argument that says what it takes: it waits until
-- `pairs` is checked. A section whose receiver comes last is the function
-- itself (D506), as it is when its argument's type is known from the start.
def anyOf (p: a -> Bool) (xs: List a): Bool := xs.any p

def pairs: List (Pair Nat Bool) := [(1, False), (2, True)]

theorem waits_for_pairs: anyOf .snd pairs = anyOf Pair.snd pairs := rfl

test "drop" := f [1, 2, 3] == [2, 3]

test "drop from nothing" := f [] == []

test "at the head" := four == 4

test "a section in a section" := lengths [[1], [2, 3], []] == [1, 2, 0]

test "any" := anyOf .snd pairs == True

test "none" := anyOf .snd [(3, False)] == False
