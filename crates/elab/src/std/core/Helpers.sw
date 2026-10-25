-- core/Helpers.sw. Small definitions the later sections use:
-- `List.concatMap`, `Bool.inspect`, `Bool.toNat`. Loaded with the core: The
-- `Ord` laws and the `Show` machinery below need them, so they stay with the
-- core (docs/proposals/prelude-slim.md §2.1).

def List.concatMap: List a → (f: a → List b) → List b
  | Nil, f => Nil
  | Cons x xs, f => List.append (f x) (List.concatMap xs f)

-- Lemmas the rest of the prelude uses. (Sorting and the lemmas around it are
-- the library file std/List/Sort.sw; these stay because the core, or a
-- later section that hasn't moved, needs them.)

-- `Bool.inspect b motive t f` proves `motive b` by cases on `b`, remembering
-- which case it is. A proof about `if le x y then ... else ...` uses it with
-- `b = le x y` to get the branch's evidence (`le x y = True` or `= False`).
theorem Bool.inspect: (b: Bool) → (motive: Bool → Prop) → (b = True → motive True) → (b = False → motive False) → motive b
  | True, m, t, f => t rfl
  | False, m, t, f => f rfl

-- 1 for `True`, 0 for `False`.
def Bool.toNat: Bool → Nat
  | False => 0
  | True => 1
