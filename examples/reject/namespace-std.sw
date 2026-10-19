-- expect-error: E-STD-NAMESPACE
-- A program's namespace can't be `Std`, the library's, or inside it.
namespace Std.Extra

def x: Nat := 1
