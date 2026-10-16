-- expect-error: E-NO-NAMESPACE
-- `Family n` can't be unfolded while `n` is unknown, so there's no namespace
-- after `Family` to look `size` up in.

Family : Nat -> Type
Family Zero = Nat
Family (Succ n) = Text

size : (n : Nat) -> Family n -> Nat
size n x = x.size
