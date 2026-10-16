-- expect-error: E-STD-NAMESPACE
-- A program can't add to the standard library's namespaces: `List` here
-- means the library's `List`.
List.sum : List Nat -> Nat
List.sum Nil = 0
List.sum (Cons x xs) = x + List.sum xs
