-- Owns the interface `Area`, so it may declare an instance for any type:
-- here `Nat`, which `Std` owns.
namespace Geometry

interface Area (a: Type) =
  { area: a → Nat }

instance Area.instNat: Area Nat :=
  { area = n => n * n }
