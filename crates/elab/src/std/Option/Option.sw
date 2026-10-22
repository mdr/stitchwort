-- Helpers for `Option`. These were in the core (docs/proposals/prelude-slim.md
-- stage 3); only the text readers needed them there.

def Option.flatMap (f: a -> Option b): Option a -> Option b
  | None => None
  | Some x  => f x

def Option.map (f: a -> b): Option a -> Option b
  | None => None
  | Some x  => Some (f x)

-- `Some` is injective: equal `Some`s hold equal values.
theorem Option.someInjective (x: a) (y: a) (h: Some x = Some y): x = y := Eq.cong (Option.getOrElse x) h

-- `MkPair` is injective: equal pairs have equal parts.
theorem Pair.mkInjectiveFst (x1: a) (y1: b) (x2: a) (y2: b) (h: MkPair x1 y1 = MkPair x2 y2): x1 = x2 := Eq.cong Pair.fst h
theorem Pair.mkInjectiveSnd (x1: a) (y1: b) (x2: a) (y2: b) (h: MkPair x1 y1 = MkPair x2 y2): y1 = y2 := Eq.cong Pair.snd h
