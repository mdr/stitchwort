-- expect-error: E-EXPORT
-- A map from a microtype crosses as a plain object only in the microtype's
-- derived order, which is `Text`'s (D1068): the codec builds the map from
-- the object's keys in that order. Any other order is refused, even one
-- that sorts the same way.
import Std (Map, Nat, Ord, Text)

@[js.unboxed]
type UserId = { value: Text }

def reversed: Ord UserId :=
  Ord.fromCompare (x y => Text.compare y.value x.value)
    (x y h => UserId.ext x y (Std.Eq.sym (Text.compareEqual y.value x.value h)))
    (x y => Text.compareFlip y.value x.value)
    (x y z h1 h2 => Text.compareTrans z.value y.value x.value h2 h1)

export def size (m: Map UserId Nat [ord := reversed]): Nat := Map.size m
