-- expect-error: E-INSTANCE-NONE
-- Derived `==`, `<` and `${…}` look into any earlier data type without
-- indices (docs/proposals/derived-equality.md §5.4): a type nested in a
-- `Vec`, whose length is an index, gets none, and the note names the
-- container. accept/nested-data-derived.sw and accept/mutual-data-derived.sw
-- have the ones that are derived.

import Std (Nat, Vec)

type Branching: Type =
  | Tip
  | Fork (kids: Vec Branching 2)

test "vec" := Fork (VCons Tip (VCons Tip VNil)) == Fork (VCons Tip (VCons Tip VNil))
