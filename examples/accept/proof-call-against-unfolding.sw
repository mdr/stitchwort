-- A transport by a `def` that unfolds to a `J` stuck on `p` equals one by
-- that unfolding written out, both when computed (`byComputing`) and when
-- unified (a hypothesis against the goal). The lemmas are `def`s, which
-- unfold: a theorem is sealed (D3722), so a transport by one never
-- computes. (A folded call with a `J` or argument after it is
-- `lift-call-over-applied.sw`.)
type Tag (n: Nat) = | MkTag (k: Nat)

def flipped (n: Nat) (p: n = 3): 3 = n := J (m _ => m = n) byComputing p

theorem computed ∀ (n: Nat)
    (p: n = 3) (x: Tag 3):
    J (m _ => Tag m) x (flipped n p) = J (m _ => Tag m) x (J (m _ => m = n) byComputing p) :=
  byComputing

theorem unified ∀ (n: Nat)
    (p: n = 3)
    (x: Tag 3) (q: Tag n → Prop) (h: q (J (m _ => Tag m) x (flipped n p))):
    q (J (m _ => Tag m) x (J (m _ => m = n) byComputing p)) :=
  h

-- A lemma whose case tree returns a lambda has arity 1, so `viaCase 0 h`
-- is the call with an argument after it, which unfolds as `0` is a
-- constructor.
def viaCase (n: Nat): n = n → n = n := match n with
  | Zero => h => h
  | Succ _ => h => h

theorem overApplied ∀ (h: 0 = 0) (x: Tag 0): J (m _ => Tag m) x (viaCase 0 h) = J (m _ => Tag m) x h := byComputing

-- Two calls of one lemma whose arguments differ only in one it ignores
-- unify through their unfoldings, the same `J` on `p`.
def flippedIgnoring (k n: Nat) (p: n = 3): 3 = n := J (m _ => m = n) byComputing p

theorem sameUnfolding ∀ (n: Nat)
    (p: n = 3)
    (x: Tag 3) (q: Tag n → Prop) (h: q (J (m _ => Tag m) x (flippedIgnoring 1 n p))):
    q (J (m _ => Tag m) x (flippedIgnoring 2 n p)) :=
  h
