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

export def isEven : Nat -> Bool
  | 0      => True
  | Succ n => isOdd n

export def isOdd : Nat -> Bool
  | 0      => False
  | Succ n => isEven n

-- `isEven`, bare, passed to a function outside its group.
export def parities (xs : List Nat) : List Bool := mapList isEven xs

def mapList (f : a -> b) : List a -> List b
  | Nil       => Nil
  | Cons x xs => Cons (f x) (mapList f xs)

-- Members returning functions, applied to one more argument outside the
-- group.
export def shifted (n : Nat) (x : Nat) : Nat := evenShift n x

def evenShift : Nat -> (Nat -> Nat)
  | 0,      x  => x
  | Succ n, a1 => oddShift n a1

def oddShift : Nat -> (Nat -> Nat)
  | 0,      x  => Succ x
  | Succ n, a1 => evenShift n a1

-- A value outside the group, computed from a member when the module loads.
def ten : Bool := isEven 10

export def tenIsEven : Nat -> Bool
  | _ => ten

-- The sum of a list of lists: `total` and `inner` take turns, `inner`
-- shrinking the inner list and `total` the outer one.
export def total : List (List Nat) -> Nat
  | Nil => 0
  | Cons xs xss => inner xs xss

def inner : List Nat -> List (List Nat) -> Nat
  | Nil,       xss => total xss
  | Cons x xs, xss => x + inner xs xss
