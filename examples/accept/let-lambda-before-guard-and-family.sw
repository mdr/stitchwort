-- A lambda bound by `let` whose parameter has no written type, before a
-- guard on a `Bool` variable or a case on an indexed family's variable,
-- used in the arms: those splits leave the parameter's unknown type alone
-- too, as `match` on a variable does (SW-873, SW-4586, SW-4589).

import Std (Bool, List, Nat)

type Box = { items: List Nat }

type Vec (a: Type): Nat → Type =
  | VNil: Vec a 0
  | VCons (x: a) (xs: Vec a n): Vec a (Succ n)

theorem guarded ∀ (flag: Bool) (b: Box): b.items.length = b.items.length :=
  let size := r => r.items.length
  match b with
    | _ if flag => (byComputing: size b = size b)
    | _ => (byComputing: size b = size b)

-- The split also substitutes the index `k`.
theorem family ∀ (k: Nat) (v: Vec Nat k) (b: Box): b.items.length = b.items.length :=
  let size := r => r.items.length
  match v with
    | VNil => (byComputing: size b = size b)
    | VCons _ _ => (byComputing: size b = size b)
