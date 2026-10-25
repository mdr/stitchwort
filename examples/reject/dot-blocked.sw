-- expect-error: E-NO-NAMESPACE
-- `Family n` can't be unfolded while `n` is unknown, so there's no namespace
-- after `Family` to look `size` up in.

def Family: Nat → Type
  | Zero => Nat
  | Succ n => Text

def size (n: Nat) (x: Family n): Nat := x.size
