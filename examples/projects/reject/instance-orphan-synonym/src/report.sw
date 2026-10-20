-- `LocalNat` is this module's name for `Nat`, but naming a type doesn't
-- make this module its owner.
namespace Report

import Geometry (Area)

type LocalNat = Nat

instance instArea: Area LocalNat :=
  { area = n => n }
