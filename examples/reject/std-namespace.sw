-- expect-error: E-STD-NAMESPACE
-- A program can't add to the standard library's namespaces: `List` here
-- means the library's `List`.
def List.sum: List Nat -> Nat
  | Nil => 0
  | Cons x xs => x + List.sum xs
