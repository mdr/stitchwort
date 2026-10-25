-- Dictionaries in scope come before global instances, and where two
-- different ones would fit, one is passed by name
-- (docs/proposals/interfaces.md §5.5, §5.7, §5.8 (c)).

interface Pretty (a: Type) =
  { pretty: a → Text }

instance Pretty.instNat: Pretty Nat :=
  { pretty = n => "global" }

def loud: Pretty Nat := { pretty = n => "loud" }

-- A dictionary in scope wins over the global instance, even at `Nat`.
def local [auto p: Pretty Nat] (n: Nat): Text := Pretty.pretty n

-- Two different `Pretty a` in scope: each use says which.
def sideBySide [auto first: Pretty a] [auto second: Pretty a] (x: a): Text :=
  Pretty.pretty [pretty := first] x ++ "/" ++ Pretty.pretty [pretty := second] x

-- A diamond: two routes to a `Root a` inside a `Both a`. A use names one.
interface Root (a: Type) =
  { name: a → Text }

interface Left (a: Type) =
  { root: Root a, left: a → Text }

interface Right (a: Type) =
  { root: Root a, right: a → Text }

interface Both (a: Type) =
  { left: Left a, right: Right a }

def viaLeft [auto d: Both a] (x: a): Text := Root.name [root := d.left.root] x

-- At `Nat`, all from global instances: both routes are the same
-- instance, so they agree.
instance Root.instNat: Root Nat := { name = n => "root" }
instance Left.instNat: Left Nat := { left = n => "left" }
instance Right.instNat: Right Nat := { right = n => "right" }
instance Both.instNat: Both Nat := {}

test "global" := local 1 == "global"
test "local wins" := local [p := loud] 1 == "loud"
test "side by side" := sideBySide [first := loud] 2 == "loud/global"
test "via left" := viaLeft 3 == "root"
test "same routes" := Both.instNat.left.root.name 0 == Both.instNat.right.root.name 0
