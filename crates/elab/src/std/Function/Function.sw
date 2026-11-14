--| Facts about functions in general, whatever they act on: what it means for
--| a function to be its own inverse, and what follows.
-- A file of its own, as for `Bool` and `Iff`, so that programs that never
-- state these don't check them.

--| An involution (a function that undoes itself, `f (f x) = x`) is
--| injective: equal results come from equal arguments. `List.reverse` and
--| `not` are involutions.
theorem Function.involutionInjective ∀ (f: a → a) (h: ∀ (x: a) => f (f x) = x) (x y: a) (e: f x = f y): x = y :=
  Eq.trans (Eq.sym (h x)) (Eq.trans (Eq.cong f e) (h y))
