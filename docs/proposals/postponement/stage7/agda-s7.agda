-- SW-988: D2118's case in Agda (Agda 2.8.0, builtins only; output in
-- other-runs.txt). Literals are overloaded through `Number` and
-- `Negative` instances (Agda.Builtin.FromNat, FromNeg).
module agda-s7 where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.FromNat using (Number; fromNat)
open import Agda.Builtin.FromNeg using (Negative; fromNeg)

instance
  NumberNat : Number Nat
  NumberNat = record { Constraint = λ _ → ⊤ ; fromNat = λ n → n }

  NumberInt : Number Int
  NumberInt = record { Constraint = λ _ → ⊤ ; fromNat = λ n → pos n }

  NegativeInt : Negative Int
  NegativeInt = record { Constraint = λ _ → ⊤ ; fromNeg = λ { 0 → pos 0 ; (Nat.suc n) → negsuc n } }

_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)

map : {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

record V : Set where
  constructor mkV
  field
    dx : Int
    dy : Int

-- the record's fields fix the components' types: checks
vs : List V
vs = map (λ { (x , y) → mkV x y }) ((7 , 2) ∷ (17 , -4) ∷ [])

-- nothing fixes them: Agda has no defaulting
ws = (7 , 2) ∷ (17 , -4) ∷ []
