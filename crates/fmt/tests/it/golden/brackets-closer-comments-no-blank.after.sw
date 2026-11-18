def x: T := [
  aaa, -- c
  bbb -- e
] -- d
def y: T := f (
  aaa, -- c
  bbb -- e
) -- d
def z: T := {
  a = aaa, -- c
  b = bbb -- e
} -- d
def w: T :=
  f
    (g aaa -- c
      bbb -- e
    ) -- d
def v: T := (
  aaa, -- c
  bbb -- e
) -- d
