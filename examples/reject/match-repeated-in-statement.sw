-- expect-error: E-REFL
-- The same `match` written again in a lemma is a second generated function,
-- which isn't the one `reach` calls: the message says how to name it (SW-194).

def reach (flag: Nat -> Bool): Nat -> Nat -> Nat -> Bool
  | Zero,   c, d => c == d
  | Succ k, c, d =>
    if flag c then
      (match c with
         | Zero   => False
         | Succ b => reach flag k b d)
        || reach flag k (c + 1) d
    else reach flag k c d

theorem split (flag: Nat -> Bool) (k: Nat) (c: Nat) (d: Nat) (s: flag c = True):
    reach flag (Succ k) c d = ((match c with | Zero => False | Succ b => reach flag k b d) || reach flag k (c + 1) d) :=
  rewrite s
