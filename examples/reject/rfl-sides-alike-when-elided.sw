-- expect-error: E-REFL
-- The two sides are too long to print whole, and print the same once their
-- inner parts are shown as `…`. They differ in `c + 7` against `c + 8`, an
-- explicit argument, so the message names that place and doesn't say they
-- differ only in arguments the compiler fills in.

import Std (List)

theorem deep (n: Nat) (c: Nat):
    List.foldLeft (List.range n) 0 (acc x => acc + (x * c + (c + (x + 1)))) + List.foldLeft (List.range n) 0 (acc x => acc + (x * c + (c + (x + 2)))) + List.foldLeft (List.range n) 0 (acc x => acc + (x * c + (c + (x + 3)))) + List.foldLeft (List.range n) 0 (acc x => acc + (x * x + (c * x + (x + (c + 7))))) =
        List.foldLeft (List.range n) 0 (acc x => acc + (x * c + (c + (x + 1)))) + List.foldLeft (List.range n) 0 (acc x => acc + (x * c + (c + (x + 2)))) + List.foldLeft (List.range n) 0 (acc x => acc + (x * c + (c + (x + 3)))) + List.foldLeft (List.range n) 0 (acc x => acc + (x * x + (c * x + (x + (c + 8))))) := rfl
