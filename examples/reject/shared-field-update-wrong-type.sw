-- expect-error: E-TYPE-MISMATCH
-- The new value of `id` must be a `Text`.

type Shape =
  | Dot (id: Text) (start: Nat)
  | Circle (id: Text) (start: Nat) (text: Text)

def f (s: Shape): Shape := { s | id = 3 }
