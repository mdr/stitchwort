-- `colorOrd` has a type error, so it isn't an instance anything can use.
namespace Colors

type Color =
  | Red
  | Green

instance colorOrd: Ord Color := True
