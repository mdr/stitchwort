-- Attributes (docs/syntax.md, Attributes) change only how a data type
-- crosses to JavaScript: patterns, field access and `show` inside
-- Stitchwort use the Stitchwort names.
@[js.tag "type"]
type Shape =
  | @[js.name "CIRCLE"] Circle (radius: Nat) (@[js.name "center_x"] centerX: Nat)
  | @[js.name "DOT"] Dot

def radius: Shape → Nat
  | Circle r _ => r
  | Dot => 0

test "patterns use the Stitchwort names" := radius (Circle 3 4) == 3
test "show uses the Stitchwort names" := "${Circle 1 2}" == "Circle 1 2"

type Point = { @[js.name "x_pos"] x: Nat, y: Nat }

test "fields use the Stitchwort names" := ({ x = 1, y = 2 }: Point).x == 1

-- A type that never crosses the boundary has no JS names to check (D612):
-- the key `__proto__` would be refused only once an export reached it.
type Node =
  | Leaf
  | Branch (tag: Nat) (__proto__: Nat) (next: Node)

def size: Node → Nat
  | Leaf => 0
  | Branch _ _ next => 1 + size next
