-- expect-error: E-TYPE-MISMATCH
-- `<` on a type with no `Ord` says why the order wasn't derived, as
-- `Ord.compare` does (derive-ord-none.sw): a note names the field.

import Std (Decidable, Eq)

def AllSame (x y: Nat): Prop := Unit

type Secret = { code: Quot Nat AllSame }

theorem Secret.codeSame ∀ (p q: Quot Nat AllSame): p = q :=
  Quot.ind [p := p' => p' = q] (x => Quot.ind [p := q' => Quot.mk x = q'] (y => Quot.sound Trivial) q) p

theorem Secret.same ∀ (x y: Secret): x = y := match x, y with
  | { code = a }, { code = b } => Eq.cong (c => ({ code = c }: Secret)) (Secret.codeSame a b)

instance Secret.instDecEq: DecEq Secret := { decide = x y => Decidable.yes (Secret.same x y) }

type Tagged = { name: Text, tag: Secret }

def before (x y: Tagged): Bool := x < y
