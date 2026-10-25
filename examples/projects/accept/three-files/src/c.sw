-- Uses both, by dot notation and by name.
namespace Shapes

test "area" := (Rect 2 3).area == 6
test "odd" := isOdd 3 ∧ isEven 4
