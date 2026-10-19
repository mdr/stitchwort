-- expect-error: E-PARSE
-- The namespace line goes before the imports.
import List (length)
namespace Demo

def x: Nat := length [1]
