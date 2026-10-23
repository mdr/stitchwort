-- expect-error: E-TYPE-MISMATCH
-- A constructor's literals take the type from a sibling operand, not the
-- other way round: `m` fixes `i` as `Text`, so the `10` is checked as a
-- `Text` and refused, rather than defaulting to a `Nat` and the mismatch being
-- reported against `m`. (The accepted neighbours are in
-- examples/accept/generic-constructor-literals.sw.)

import Std (List, Nat)

type Mark (i: Type) (n: Type) =
  | Point (ref: Nat) (label: Text) (at: i)
  | Span (ref: Nat) (label: Text) (from: i) (length: n)

def pair (x: a) (y: a): List a := [x, y]

def bad (m: Mark Text Nat): List (Mark Text Nat) := pair (Point 1 "p" 10) m
