import Std (Bool, Nat, List, Parse)

def atomMiddle (lo x hi: Nat): Bool := lo <= x <= hi

def callMiddle (lo hi: Nat) (xs: List Nat): Bool := lo < xs.length() <= hi

def threeLinks (a b c d: Nat): Bool := a < b <= c < d

def descending (a b c: Nat): Bool := a > b >= c

def inLogic (a b c: Nat): Bool := a < b < c && b <= c < a || a < b

def effectful(): {Parse} Bool :=
  let a := 0 < Parse.nat() <= Parse.nat()
  a

-- An unannotated `let` of `&&`, `||` or a chain whose operands perform is a
-- `Bool` computation: a proposition can't perform.

def pureBool (x y z: Nat): Bool :=
  let b := x < y && y < z
  b

def pureChain (x y z: Nat): Bool :=
  let b := x < y < z
  b

def andInferred(): {Parse} Bool :=
  let a :=
    let c := Parse.nat()
    0 < c && c <= Parse.nat()
  a

def orInferred(): {Parse} Bool :=
  let a :=
    let c := Parse.nat()
    c < 1 || c <= Parse.nat()
  a

def chainInferred(): {Parse} Bool :=
  let a := (0 < Parse.nat() <= Parse.nat())
  a

def chainBare(): {Parse} Bool :=
  let a := 0 < Parse.nat() <= Parse.nat()
  a

def annotated(): {Parse} Bool :=
  let a: Bool := 0 < Parse.nat() <= Parse.nat()
  a
