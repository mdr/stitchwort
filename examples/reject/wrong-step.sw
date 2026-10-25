-- expect-error: E-TYPE-MISMATCH

import Std (List)

-- The recursive call proves the statement for `xs`, not for `Cons x xs`.
theorem appendLength: (xs: List a) → (ys: List a) →
    List.length (List.append xs ys) = List.length xs + List.length ys
  | Nil,       ys => rfl
  | Cons x xs, ys => appendLength xs ys
