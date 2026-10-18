-- Each case where rule 2 refuses a column, so everything is arms.

-- Different variable names in the equations.
diffNames : Nat -> List Nat -> Nat
diffNames k Nil = k
diffNames j (Cons l ls) = j + l

-- A wildcard in one equation.
wild : Nat -> List Nat -> Nat
wild k Nil = k
wild _ (Cons l ls) = l

-- The variable occurs in the type.
same : a -> a
same a = a

same2 : a -> List a -> a
same2 a Nil = a
same2 a (Cons x xs) = x

-- The variable is the name of an implicit binder.
implName : [n : Nat] -> Nat -> List Nat -> Nat
implName n Nil = n
implName n (Cons x xs) = x

-- A named Pi binder whose name differs and is used later in the type.
vec : (n : Nat) -> List Nat -> n = n
vec k Nil = rfl
vec k (Cons x xs) = rfl

-- A multi-name binder only partly covered.
two : (x y : Nat) -> List Nat -> Nat
two x z Nil = x
two x z (Cons a as) = z

-- A multi-name binder where only the first name's column is named.
two2 : (x y : Nat) -> List Nat -> Nat
two2 x y Nil = x
two2 x w (Cons a as) = w
