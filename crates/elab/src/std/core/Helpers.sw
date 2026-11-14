--| Small definitions the later sections use:
--| [`List.concatMap`], [`Bool.inspect`], [`Bool.toNat`].
-- Loaded with the core: The `Ord` laws and the `Show` machinery below need
-- them, so they stay with the core (docs/proposals/prelude-slim.md §2.1).

--| `f` on each element, the results joined in order: the core's version of
--| `List.flatMap`.
def List.concatMap: (xs: List a) → (f: a → List b) → List b
  | [], f => []
  | [x, ..xs], f => List.append (f x) (List.concatMap xs f)

--| The value itself: `id 3` is `3`. It is the function to pass where one is
--| wanted and nothing should change, as in `options.filterMap id`
--| (`List.somes` is that).
def id (x: a): a := x

--| `f` applied to the two parts of a pair: `uncurry (+) (2, 3)` is `5`. It lets a
--| two-argument function take the pairs a list holds, as in
--| `pairs.map (uncurry Connection.between)`; where the parts deserve names in
--| the body, a lambda `(((first, second)) => …)` reads better.
def uncurry (f: a → b → c) (pair: (a, b)): c := f pair.fst pair.snd

test "uncurry" := uncurry (+) (2, 3) == 5 ∧ uncurry (a b => a) (True, 4) == True

test "id" := id 3 == 3 ∧ id True == True

-- Lemmas the rest of the prelude uses. (Sorting and the lemmas around it are
-- the library file std/List/Sort.sw; these stay because the core, or a
-- later section that hasn't moved, needs them.)

--| `Bool.inspect b motive t f` proves `motive b` by cases on `b`, remembering
--| which case it is. A proof about `if le x y then ... else ...` uses it with
--| `b = le x y` to get the branch's evidence (`le x y = True` or `= False`).
theorem Bool.inspect ∀ (b: Bool) (motive: Bool → Prop) (t: b = True → motive True) (f: b = False → motive False):
    motive b :=
  match b, motive with
    | True, m => t rfl
    | False, m => f rfl

--| 1 for `True`, 0 for `False`.
def Bool.toNat: (b: Bool) → Nat
  | False => 0
  | True => 1
