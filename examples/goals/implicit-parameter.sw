-- Implicit parameters are in the context too.
def identity [a: Type] (x: a): a := ?

theorem symmetric ∀ [a: Type] (x y: a) (h: x = y): y = x := ?
