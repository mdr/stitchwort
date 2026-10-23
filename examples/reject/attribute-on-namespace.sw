-- expect-error: E-ATTRIBUTE
-- A group of attributes before `namespace` attaches there, and is refused;
-- it doesn't drift onto the type below.
@[js.tag "type"]
namespace Drawings

type Shape =
  | Circle (radius: Nat)
