-- Instance heads (docs/proposals/interfaces.md §5.2): a type name applied
-- to distinct variables. One instance per interface and type name, so
-- these don't overlap.

interface Size (a: Type) =
  { size: a -> Nat }

instance Size.instNat: Size Nat :=
  { size = n => n }

instance Size.instList [auto s: Size a]: Size (List a) :=
  { size = xs => xs.foldLeft (n x => n + Size.size x) 0 }

instance Size.instPair [auto sa: Size a] [auto sb: Size b]: Size (a, b) :=
  { size = p => match p with
      | (x, y) => Size.size x + Size.size y }

-- An indexed family applied to variables, values among them.
instance Size.instVec [auto s: Size a]: Size (Vec a n) :=
  { size = v => n }

-- A data type with a value parameter.
type Tagged (tag: Nat) =
  | MkTagged

instance Size.instTagged: Size (Tagged tag) :=
  { size = t => tag }

-- A synonym is unfolded: this is `Size (Option a)`.
type Optional (a: Type) = Option a

instance Size.instOptional [auto s: Size a]: Size (Optional a) :=
  { size = m => match m with
      | Some x => Size.size x
      | None => 0 }

test "nat" := Size.size 4 == 4
test "list" := Size.size [1, 2, 3] == 6
test "pair" := Size.size (2, [3]) == 5
test "vec" := Size.size (VCons 5 (VCons 6 VNil)) == 2
test "tagged" := Size.size (MkTagged: Tagged 7) == 7
test "maybe" := Size.size (Some [4]) == 4
