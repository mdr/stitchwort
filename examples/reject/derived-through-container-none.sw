-- expect-error: E-INSTANCE-NONE
-- Through a container a type's `Show` (or `Ord`) is derived only when the
-- container's is (derived-through-own-instance.sw), and the note says which it is:
-- here `Holder` has no `Show` because of its function field, not
-- because its module wrote one.

import Std (Nat, Text)

type Holder (a: Type) = | Holds (call: Nat → Bool) (item: a)

type Held = | Nothing | Wrap (h: Holder Held)

def describe (x: Held): Text := "${x}"
