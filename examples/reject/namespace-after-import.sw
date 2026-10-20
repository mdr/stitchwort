-- expect-error: E-NAMESPACE-NOT-FIRST
-- The namespace line must come before the imports.
import List (length)
namespace Demo

def x: Nat := length [1]
