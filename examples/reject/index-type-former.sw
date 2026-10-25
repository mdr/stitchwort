-- expect-error: E-INDEX-STUCK
-- Type formers aren't injective in matching (D139): `TList` on a
-- `Ty (List Nat)` would need `List b = List Nat`, and types are never taken
-- apart. Pairs with `depth`, which matches a `Ty c`, in
-- accept/indexed-families.sw (docs/proposals/indexed-families.md §9, test 6).
type Ty: Type → Type 1 =
  | TNat: Ty Nat
  | TList (t: Ty b): Ty (List b)

def depth: Ty (List Nat) → Nat
  | TNat    => 0
  | TList _ => 1
