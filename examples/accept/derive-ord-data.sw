-- Derived `Ord` for data types with fields (docs/proposals/interfaces.md
-- §5.11): constructors in the order they're declared, then their fields
-- left to right. A field of the type itself compares recursively.

type Shape =
  | Dot
  | Circle (radius: Nat)
  | Rect (w: Nat) (h: Nat)
  | Label (text: Text) (size: Nat)
  | Group (first: Shape) (rest: Shape)

test "constructors first" := Ord.compare (Circle 100) (Rect 1 1) == Less
test "then fields" := Ord.compare (Rect 2 1) (Rect 1 5) == Greater
test "second field" := Ord.compare (Rect 2 1) (Rect 2 5) == Less
test "text field" := Ord.compare (Label "b" 1) (Label "a" 9) == Greater
test "recursive" := Ord.compare (Group Dot (Circle 2)) (Group Dot (Circle 1)) == Greater
test "equal" := Ord.compare (Group (Rect 1 2) Dot) (Group (Rect 1 2) Dot) == Equal

test "sort" :=
  List.sort [Group Dot Dot, Rect 3 1, Dot, Label "x" 2, Circle 5, Rect 1 9] ==
    [Dot, Circle 5, Rect 1 9, Rect 3 1, Label "x" 2, Group Dot Dot]

-- A proof field between data fields is left out, as for `==` (D179).
type Small =
  | MkSmall (n: Nat) (small: Nat.leq n 10 = True) (label: Text)
  | Big

test "proof field left out" := Ord.compare (MkSmall 3 rfl "b") (MkSmall 3 rfl "a") == Greater
test "small before big" := Ord.compare (MkSmall 9 rfl "z") Big == Less

-- One constructor, not a record.
type Version = | V (major: Nat) (minor: Nat) (patch: Nat)

test "versions" := List.sort [V 1 2 0, V 1 0 9, V 0 9 9] == [V 0 9 9, V 1 0 9, V 1 2 0]

-- `Equal` means equal: the law, used.
theorem sameShape (s: Shape) (t: Shape) (h: Ord.compare s t = Equal): s = t := Ord.equal s t h
