-- A lowercase name in a type is a type variable: this works for any `a`.
def twice (f: a -> a) (x: a): a := f (f x)

-- Implicit arguments are filled in by the compiler. Here `a` is found from
-- the list you pass; you never write it.
def firstOr (fallback: a): List a -> a
  | [] => fallback
  | Cons x _ => x

-- A type with parameters, like `List a` or `Option a`.
type Swapped (a: Type) (b: Type) = { left: a, right: b }

def Swapped.flip (p: Swapped a b): Swapped b a := { left = p.right, right = p.left }

test "twice" := twice (n => n + 3) 10 == 16
test "firstOr" := firstOr 0 [] == 0
test "flip" := (Swapped.flip { left = 1, right = "one" }).left == "one"
