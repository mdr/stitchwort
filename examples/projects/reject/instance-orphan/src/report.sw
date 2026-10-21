-- An orphan: neither the interface nor the type is this module's.
namespace Report

import Geometry (Area)

instance instArea: Area Nat :=
  { area = n => n }
