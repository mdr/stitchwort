-- The proof of `examples/accept/proof-chain-warning.sw` written as a `calc`:
-- every intermediate term is on the page, and no warning (D3656).
theorem chained ∀ (a b c d: Nat) (ab: a = b) (bc: b = c) (cd: c = d): a = d := calc a
  _ = b := ab
  _ = c := bc
  _ = d := cd
