-- expect-error: E-AUTO-FALSE
-- An auto argument can't be satisfied by a false proposition: `get` on an
-- empty list is refused at compile time.
def get: (xs: List a) -> (i: Nat) -> [auto ok: i < List.length xs] -> a
  | Cons x xs, Zero   => x
  | Cons x xs, Succ i => get xs i
  | Nil,       i      => Void.absurd (Bool.falseNotTrue ok)

def nothing: Nat := get [a := Nat] Nil 0
