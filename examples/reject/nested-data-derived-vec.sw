-- expect-error: E-INSTANCE-NONE
-- Derived `==`, `<` and `${…}` look into `List`, `Option` and pairs only
-- (docs/proposals/nested-data-types.md §10, stage 2): a type nested in a
-- `Vec`, or in a type of the program, gets none, and the note names the
-- container. accept/nested-data-derived.sw has the ones that are derived.

import Std (Nat, Vec)

type Branching: Type =
  | Tip
  | Fork (kids: Vec Branching 2)

test "vec" := Fork (VCons Tip (VCons Tip VNil)) == Fork (VCons Tip (VCons Tip VNil))

type Box (a: Type): Type =
  | MkBox (inner: a)

type Boxed: Type =
  | End
  | More (next: Box Boxed)

def describe (b: Boxed): Text := "${b}"
