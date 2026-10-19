-- expect-error: E-TYPE-MISMATCH
-- Known limitation, for now: after `let p := n` the checker only knows `p`
-- is some `Nat`, not that it is `n`. Stage 3 of docs/proposals/let.md (a
-- transparent `let` in the kernel) makes this check; then this file moves
-- to accept/.
theorem one (n : Nat) : n <= n + 1 :=
  let p := n
  Nat.leAddRight p 1
