-- Can't add to Lib's type from another namespace.
namespace Day

import Lib (Range)

def Range.extra (r: Range): Nat := 1
