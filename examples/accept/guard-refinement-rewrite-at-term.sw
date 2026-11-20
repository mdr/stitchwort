-- expect-warning: W-REWRITE-GUARD-REFINED
-- The same for a `rewrite … at h` with no `then`, whose result is the fact
-- itself: the quick fix leaves `h`.

def weight (c: Char): Nat := match c with
  | c if c == '(' => 1
  | _ => 2

theorem weightKept ∀ (c: Char) (h: weight c = 2): weight c = 2 := match c with
  | c if g: c == '(' => rewrite weight.eq1 c g at h
  | c => h
