-- expect-error: E-REFL
-- A catch-all arm knows the value is none of the literals above it, and
-- nothing more: here `n` may still be 7, so `kind n` may be 2 and can't
-- be computed. (accept/literal-match-facts.sw lists both literals.)
def kind: Nat → Nat
  | 3 => 1
  | 7 => 2
  | _ => 0

theorem bad (n: Nat): Or (n = 3) (kind n = 0) :=
  match n with
    | 3 => Inl rfl
    | _ => Inr rfl
