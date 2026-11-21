--| Slice 6a's formatter on small cases: `rewrite` with its rules, `<-`,
--| `at`, `then` chains and `repeatedly`, `cases` with names and `then`,
--| facts, `calc` and `↔`. The harness (`dev/fmt-twin s6a`) compares every
--| declaration within the slices with the Rust formatter's; these pin the
--| main shapes, each expected text being `stitchwort fmt`'s.

namespace Fmt.Tests
import Fmt (..)
import Std (Bool, Result, Text)

test "rewrite on one line: `<-`, `at`, `then` chains, `repeatedly` and facts" :=
  formats
      "theorem a: P := rewrite <- h, g x at k then rfl\ntheorem b: P := rewrite h, g\ntheorem c: P := rewrite a then rewrite b then arithmetic [h, g]\ntheorem d: P := rewrite repeatedly [a, <- b] at h then algebra\n"
      "theorem a: P := rewrite <- h, g x at k then rfl\ntheorem b: P := rewrite h, g\ntheorem c: P := rewrite a then rewrite b then arithmetic [h, g]\ntheorem d: P := rewrite repeatedly [a, <- b] at h then algebra\n"

test "a long `rewrite` puts its body below at 2, and its rules one a line at 4 when they don't fit" :=
  formats
      "theorem f: P := rewrite aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb, cccccccccccccccccccccccccccccccccc then rfl\ntheorem h: P := rewrite aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb then ccccccccccccccccccccccccccccccc dddddddd\ntheorem l: P := rewrite a then\n  let x := 1\n  x\n"
      "theorem f: P :=\n  rewrite aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,\n      bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb,\n      cccccccccccccccccccccccccccccccccc then\n    rfl\ntheorem h: P :=\n  rewrite aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb then\n    ccccccccccccccccccccccccccccccc dddddddd\ntheorem l: P :=\n  rewrite a then\n    let x := 1\n    x\n"

test "comments in a `rewrite` keep it broken" :=
  formats
      "theorem a: P := rewrite h, -- why\n  g then rfl\ntheorem b: P := rewrite h then -- next\n  rfl\ntheorem d: P :=\n  -- above\n  rewrite h,\n    -- before g\n    g then rfl\n"
      "theorem a: P :=\n  rewrite h, -- why\n      g then\n    rfl\ntheorem b: P :=\n  rewrite h then -- next\n    rfl\ntheorem d: P :=\n  -- above\n  rewrite h,\n      -- before g\n      g then\n    rfl\n"

test "`calc` steps one a line at 2, a blank line kept, and in an arm below the `=>`" :=
  formats
      "theorem a: x = z := calc x\n  _ = y := h1\n  _ = z := rewrite h2 then rfl\ntheorem b: x <= z := calc f x y\n\n    -- step\n    _ < z := aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\ntheorem c: P := match x with\n  | A => calc a\n    _ = b := h\n  | B => cases then rfl\n"
      "theorem a: x = z := calc x\n  _ = y := h1\n  _ = z := rewrite h2 then rfl\ntheorem b: x <= z := calc f x y\n\n  -- step\n  _ < z :=\n    aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\ntheorem c: P := match x with\n  | A =>\n    calc a\n      _ = b := h\n  | B => cases then rfl\n"

test "`cases` with names to split, as the Rust formatter's golden `cases-named` has it" :=
  formats
      "theorem t ∀ (a b: Bool): (a || b) = (b || a) :=   cases   a ,b   then   byComputing\n\ntheorem u ∀ (a: Bool): (a || a) = a := cases   a\n\ntheorem v ∀ (a b: Bool): (a || b) = (b || a) :=\n  cases a,  b then\n    byComputing\n"
      "theorem t ∀ (a b: Bool): (a || b) = (b || a) := cases a, b then byComputing\n\ntheorem u ∀ (a: Bool): (a || a) = a := cases a\n\ntheorem v ∀ (a b: Bool): (a || b) = (b || a) := cases a, b then byComputing\n"

test "comments among a `cases`'s names, and a long one, print as Rust's" :=
  formats
      "theorem a: P := cases x -- c\n  , y then rfl\ntheorem b: P := cases x,\n  -- above y\n  y then rfl\ntheorem c: P := cases aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb, cccccccccccccccc then ddddddddddddddddd eeeeeeeeeeeeeeeeeeeeeeeeeeeee\n"
      "theorem a: P := cases x, -- c\n  y then rfl\ntheorem b: P :=\n  cases x,\n    -- above y\n    y then rfl\ntheorem c: P :=\n  cases aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb, cccccccccccccccc then ddddddddddddddddd\n      eeeeeeeeeeeeeeeeeeeeeeeeeeeee\n"

test "a long `↔` breaks before the operator" :=
  formats
      "theorem i (p q: Prop): p ↔ q := aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa ↔ bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\n"
      "theorem i ∀ (p q: Prop): p ↔ q :=\n  aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa ↔ bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\n"

test "a comment on `<-`, one above a `calc` step's `:=`, and a `calc` whose first expression could hug are outside the slice" :=
  refuses "theorem a: P := rewrite <- -- c\n  h then rfl\n"
    && refuses "theorem b: P := calc x\n  _ = y\n    -- c\n    := h\n"
    && refuses "theorem c: P := calc f [x]\n  _ = y := h\n"

test "a list of plain values with a comment inside is never filled: a trailing comment before more items breaks it, one that ends it keeps it on its line" :=
  formats "theorem a: P := rewrite [1, -- c\n  2, 3] then rfl\ntheorem b: P := rewrite [1, 2, 3, -- c\n  ] then rfl\n"
      "theorem a: P :=\n  rewrite [\n        1, -- c\n        2,\n        3\n      ] then\n    rfl\ntheorem b: P := rewrite [1, 2, 3] -- c\n  then rfl\n"
