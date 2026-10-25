-- expect-error: E-PARSE
-- There are no set operators (D1207), so `⊆` is refused with a note on what
-- to write instead (D1208): a function, such as `List.All`.
theorem sub (xs: List Nat) (ys: List Nat): xs ⊆ ys := ?
