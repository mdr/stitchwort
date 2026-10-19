-- expect-error: E-NAMESPACE-RESERVED
-- A namespace can't start with the name of one of the library's: `List`.
namespace List

def x: Nat := 1
