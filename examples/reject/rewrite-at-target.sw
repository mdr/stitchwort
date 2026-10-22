-- expect-error: E-REWRITE-TARGET
-- `in` gives a name a new type for the rest of the proof, so it needs a local
-- name after `at`. Without `in`, any term can be rewritten where it stands.
theorem bad (n: Nat) (m: Nat) (e: n = m) (k: Nat): m + Succ k = Succ (m + k) :=
  rewrite e at Nat.addSucc n k in Nat.addSucc m k
