-- A lambda applied to its arguments on the spot, whose parameter types
-- leave something to work out: `Box`'s type argument, or a `_`. The
-- unknown in `b`'s type is made with `a` in scope, so it's applied to `a`;
-- once `a` is `[1]`, `[True]` asks for `?t [1] = Bool`, which isn't a
-- plain pattern. Nothing written in `b`'s type mentions `a`, so the unknown
-- may ignore it: `t` is `Bool` (SW-3890).
def Box [t: Type]: Type := List t

def direct: Nat := ((a b: Box) => a.length + b.length) [1] [True]

def holes: Nat := ((a b: List _) => a.length + b.length) [1] [True]

def curried: Nat := ((a: List _) => (b: List _) => a.length + b.length) [1] [True]

def named: Nat :=
  let both := (a b: List _) => a.length + b.length
  both [1, 2] [True]

theorem directIsTwo: direct = 2 := byComputing
theorem holesIsTwo: holes = 2 := byComputing
theorem curriedIsTwo: curried = 2 := byComputing
theorem namedIsThree: named = 3 := byComputing
