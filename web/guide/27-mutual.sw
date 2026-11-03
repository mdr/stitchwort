-- Declarations can come in any order, and definitions can call each other.
-- Each recursive call is on a smaller piece, so termination is still checked.
def describe (n: Nat): Text := if isEven n then "even" else "odd"

def isEven: Nat → Bool
  | 0 => True
  | Succ n => isOdd n

def isOdd: Nat → Bool
  | 0 => False
  | Succ n => isEven n

-- Types can refer to each other too: a tree whose children are a forest.
type Tree =
  | Node (label: Nat) (kids: Forest)

type Forest =
  | FNil
  | FCons (first: Tree) (rest: Forest)

def Tree.total: Tree → Nat
  | Node label kids => label + Forest.total kids

def Forest.total: Forest → Nat
  | FNil => 0
  | FCons first rest => Tree.total first + Forest.total rest

test "even and odd" := describe 10 == "even" ∧ describe 7 == "odd"
test "tree total" := Tree.total (Node 1 (FCons (Node 2 FNil) (FCons (Node 3 FNil) FNil))) == 6
