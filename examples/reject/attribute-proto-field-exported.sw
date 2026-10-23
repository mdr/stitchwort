-- expect-error: E-JS-NAME-CLASH
-- A type without attributes is checked once an export reaches it (D612):
-- the key `__proto__` would set an object's prototype.
type Node =
  | Leaf
  | Branch (__proto__: Nat) (next: Node)

export def size: Node -> Nat
  | Leaf => 0
  | Branch _ next => 1 + size next
