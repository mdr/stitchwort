-- Definitions that call each other (docs/proposals/mutual-recursion.md
-- §8.6), extracted to JavaScript, written top-down: every name is visible
-- throughout the module. Each case of the calling convention: direct calls
-- between members, an export wrapper for a member, a member passed bare to a
-- function outside its group, a member returning a function (applied to
-- more arguments outside the group), and a value computed from a member
-- when the module loads. (Mutual tail calls aren't loops: `isEven` on a
-- large number runs out of stack, as tested in `crates/cli/tests/extract.rs`.)
--
-- run: isEven 10
-- run: isOdd 7
-- run: parities [0, 1, 2, 3]
-- run: shifted 3 10
-- run: shifted 4 10
-- run: tenIsEven 0
-- run: total [[1, 2], [], [3]]
-- run: total []

export
isEven : Nat -> Bool
isEven 0        = True
isEven (Succ n) = isOdd n

export
isOdd : Nat -> Bool
isOdd 0        = False
isOdd (Succ n) = isEven n

-- `isEven`, bare, passed to a function outside its group.
export
parities : List Nat -> List Bool
parities xs = mapList isEven xs

mapList : (a -> b) -> List a -> List b
mapList f Nil         = Nil
mapList f (Cons x xs) = Cons (f x) (mapList f xs)

-- Members returning functions, applied to one more argument outside the
-- group.
export
shifted : Nat -> Nat -> Nat
shifted n x = evenShift n x

evenShift : Nat -> (Nat -> Nat)
evenShift 0        = \x -> x
evenShift (Succ n) = oddShift n

oddShift : Nat -> (Nat -> Nat)
oddShift 0        = \x -> Succ x
oddShift (Succ n) = evenShift n

-- A value outside the group, computed from a member when the module loads.
ten : Bool
ten = isEven 10

export
tenIsEven : Nat -> Bool
tenIsEven _ = ten

-- The sum of a list of lists: `total` and `inner` take turns, `inner`
-- shrinking the inner list and `total` the outer one.
export
total : List (List Nat) -> Nat
total Nil          = 0
total (Cons xs xss) = inner xs xss

inner : List Nat -> List (List Nat) -> Nat
inner Nil         xss = total xss
inner (Cons x xs) xss = x + inner xs xss
