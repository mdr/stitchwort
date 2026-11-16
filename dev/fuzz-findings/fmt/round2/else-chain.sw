def clamp (x lo hi: Int): Int :=
 if x < lo then lo
  else-- c
 if hi < x then hi
  else x
