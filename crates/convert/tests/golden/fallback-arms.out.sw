-- Each case where rule 2 refuses a column, so everything is arms.

-- Different variable names in the equations.
def diffNames : Nat -> List Nat -> Nat
  | k, Nil => k
  | j, Cons l ls => j + l

-- A wildcard in one equation.
def wild : Nat -> List Nat -> Nat
  | k, Nil => k
  | _, Cons l ls => l

-- The variable occurs in the type.
def same : a -> a
  | a => a

def same2 : a -> List a -> a
  | a, Nil => a
  | a, Cons x xs => x

-- The variable is the name of an implicit binder.
def implName : [n : Nat] -> Nat -> List Nat -> Nat
  | n, Nil => n
  | n, Cons x xs => x

-- A named Pi binder whose name differs and is used later in the type.
def vec : (n : Nat) -> List Nat -> n = n
  | k, Nil => rfl
  | k, Cons x xs => rfl

-- A multi-name binder only partly covered.
def two (x z : Nat) : List Nat -> Nat
  | Nil => x
  | Cons a as => z

-- A multi-name binder where only the first name's column is named.
def two2 : (x y : Nat) -> List Nat -> Nat
  | x, y, Nil => x
  | x, w, Cons a as => w
