-- expect-warning: W-ARROW-FORALL
-- A statement written `(x: T) -> P` warns (W-ARROW-FORALL, D3462): `∀ (x: T)
-- => P` is how a statement about every `x` is written, and `->` is for a
-- function type. The editor's quick fix "Write ∀ instead of ->" makes the
-- edit. An arrow whose variable nothing uses, `(n: Nat) -> True`, an
-- implication with a named proof, `(h: p) -> q`, and a function type to a
-- type don't warn.
theorem addZero ∀ (m: Nat): (n: Nat) -> n + 0 = n := n => rfl

theorem unusedVariable ∀ (m: Nat): (n: Nat) -> m = m := n => rfl

theorem namedProof ∀ (m: Nat): (h: m = 1) -> m = 1 := h => h

def vector (n: Nat): Type := Nat

def functionType: (n: Nat) -> Type := n => vector n
