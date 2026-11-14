-- A reading for another namespace's test: it must be declared in `Tests`,
-- with `small`.
namespace Readings

import Tests (small)

@[reading]
theorem smallReads (n: Nat): small n ↔ n < 10 := { forward = h => h, backward = h => h }
