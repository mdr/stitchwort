-- expect-error: E-TERMINATION
-- Pairs with accept/termination-wrapper-honest.sw: each argument here is the
-- parameter itself or may be as big, so each function may run for ever.
-- `MkW []` in the `[]` branch is the parameter; `MkRose [k, k, ..rest]`
-- grows; `MkRose [k]` is the parameter when it was `MkRose [k]`; and the
-- `Vec` inside `MkWv` is rebuilt whole, or rebuilt with `y` twice.
type W (a: Type): Type = | MkW (x: a)

def emptyAgain: W (List Nat) → Nat
  | MkW [] => emptyAgain (MkW [])
  | _ => 0

type Rose: Type = | MkRose (kids: List Rose)

def roseGrows: Rose → Nat
  | MkRose [k, ..rest] => roseGrows (MkRose [k, k, ..rest])
  | MkRose [] => 1

def roseFirst: Rose → Nat
  | MkRose [k, ..rest] => roseFirst (MkRose [k])
  | MkRose [] => 1

type Vec (a: Type): Nat → Type =
  | VNil: Vec a 0
  | VCons [n: Nat] (x: a) (xs: Vec a n): Vec a (Succ n)

type Wv (n: Nat): Type = | MkWv (v: Vec Nat n)

def vecAgain [n: Nat]: Wv n → Nat
  | MkWv (VCons x (VCons y rest)) => vecAgain (MkWv (VCons x (VCons y rest)))
  | _ => 0

def vecSameLength [n: Nat]: Wv n → Nat
  | MkWv (VCons x (VCons y rest)) => vecSameLength (MkWv (VCons y (VCons y rest)))
  | _ => 0
