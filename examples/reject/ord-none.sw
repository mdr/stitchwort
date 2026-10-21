-- expect-error: E-INSTANCE-NONE
-- `List.sort` needs an `Ord` instance for the elements
-- (docs/proposals/interfaces.md §7.4), and functions have none. A one-off
-- order without laws is `List.sortBy` with a comparison instead.

def byResult (fs: List (Nat -> Nat)): List (Nat -> Nat) := List.sort fs
