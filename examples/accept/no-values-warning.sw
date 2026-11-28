-- expect-warning: W-NO-VALUES
-- A type whose every constructor has a field of the type itself has no
-- values (W-NO-VALUES, SW-4965): building one needs one first. It is still
-- accepted. A constructor without the field (`End`), a function from the
-- position (`Nat -> a`), and recursion under another type former don't warn.
type Co (a: Type) = { head: a, tail: Co a }

type Chain = | Link (previous: Chain) | Join (left: Chain) (right: Chain)

type Stream (a: Type) = { at: Nat -> a }

type Tree (a: Type) = | End | Node (left: Tree a) (value: a) (right: Tree a)

type Rose (a: Type) = { label: a, children: List (Rose a) }
