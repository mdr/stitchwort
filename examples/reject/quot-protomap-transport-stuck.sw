-- expect-error: E-REFL
-- Transporting a number along an equation between two maps that are equal
-- only through the quotient (docs/proposals/map-equality.md §9.1, §14.2
-- property 6, on the step 1.6 prototype): `J` on `Quot.sound` doesn't
-- compute in the kernel, so `transported` is a stuck `Nat`, not `0`. When
-- run, the proof is erased and `J` gives its base, `0`
-- (accept/quot-protomap.sw's `transported`, with every runner).

import Std (Eq, Map, Quot)

type ProtoMap (k: Type) (v: Type) [auto ord: Ord k] = { raw: Quot (Map k v [ord := ord]) Map.Equiv }

def up: Map Nat Text := Map.fromList [(1, "a"), (2, "b")]
def down: Map Nat Text := Map.fromList [(2, "b"), (1, "a")]

def forwards: ProtoMap Nat Text := { raw = Quot.mk up }
def backwards: ProtoMap Nat Text := { raw = Quot.mk down }

theorem same: forwards = backwards :=
  Eq.cong (r => ({ raw = r }: ProtoMap Nat Text)) (Quot.sound [x := up] [y := down] rfl)

def transported: Nat := J (y p => Nat) 0 same

theorem stuck: transported = 0 := rfl
