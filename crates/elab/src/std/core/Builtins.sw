--| The built-in names: `rfl`, `J` and the quotient forms. Their meaning is the
--| kernel's, not a definition's, so this file only documents them. Each is
--| declared here with its signature and, as a body, the kernel form it names,
--| which the kernel checks against that signature: a signature that no longer
--| matches the built-in fails when the core loads (`E-BUILTIN`).
-- Loaded with the core, first (a name used before its declaration waits for it;
-- this uses only `=`, `Prop` and the forms
-- themselves). A use of one of these names is the built-in, never these
-- definitions; they exist so that go-to-definition, hover and `stitchwort doc`
-- have somewhere to land (SW-1146). The built-in is more general than a
-- signature can say where noted: the one here is its instance at `Type`.

--| The proof that a value equals itself: `rfl: x = x`. It is checked against
--| the equation it should prove, so `x` and the type come from the expected
--| type, and the two sides must be equal by computation (`2 + 2 = 4` is
--| `rfl`).
def rfl: [a: Type] → [x: a] → x = x

--| Transport along an equality: from `p: x = y`, and `base` for `x`, a value
--| for `y`. The `motive` is written as a function of two arguments, the new
--| endpoint and the proof (`y' p' => …`), and gives the statement being
--| proved; `base` proves it at `x` with `rfl`. `J motive base rfl` computes to
--| `base`. Everything about equality is built from this (`Eq.cong`, `Eq.sym`,
--| `Eq.trans`).
--|
--| The motive may be a proposition or a type; the signature shows the case of
--| a motive in `Type`.
def J: [a: Type] → [x y: a] → (motive: (y': a) → x = y' → Type) → (base: motive x rfl) → (p: x = y) → motive y p

--| The quotient of `a` by the relation `r`: `a` with every pair related by `r`
--| treated as equal. Its elements are `Quot.mk x`; a function out of it is
--| built by `Quot.lift`, and a statement about all of them is proved by
--| `Quot.ind`.
def Quot: (a: Type) → (r: a → a → Prop) → Type

--| The element of the quotient for `x`.
def Quot.mk: [a: Type] → [r: a → a → Prop] → (x: a) → Quot a r

--| A function out of the quotient: `f` applied to the representative. `h` shows
--| that `f` can't tell related values apart. It computes on `Quot.mk`:
--| `Quot.lift f h (Quot.mk x)` is `f x`.
def Quot.lift: [a: Type]
      → [r: a → a → Prop]
      → [b: Type]
      → (f: a → b)
      → (h: ∀ (x y: a) => r x y → f x = f y)
      → (q: Quot a r)
      → b

--| Induction: a statement about every element of the quotient follows from
--| one about each `Quot.mk x`. It proves only propositions, and never
--| computes.
def Quot.ind: [a: Type]
      → [r: a → a → Prop]
      → [p: Quot a r → Prop]
      → (h: ∀ (x: a) => p (Quot.mk x))
      → ∀ (q: Quot a r) => p q

--| Related values have equal classes: `Quot.mk x = Quot.mk y` when `r x y`.
--| This is the one axiom of the core theory (`stitchwort axioms` lists a
--| definition that uses it).
def Quot.sound: [a: Type] → [r: a → a → Prop] → [x y: a] → (h: r x y) → Quot.mk [r := r] x = Quot.mk [r := r] y
