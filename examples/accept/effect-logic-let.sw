import Std (Bool, Nat, Parse)

-- An unannotated `let` of `&&`, `||` or a chain whose operands perform is a
-- `Bool` computation: a proposition can't perform.

def pureBool (x y z: Nat): Bool :=
  let b := x < y && y < z
  b

def pureChain (x y z: Nat): Bool :=
  let b := x < y < z
  b

def andInferred(): {Parse Char} Bool :=
  let a :=
    let c := Parse.nat()
    0 < c && c <= Parse.nat()
  a

def orInferred(): {Parse Char} Bool :=
  let a :=
    let c := Parse.nat()
    c < 1 || c <= Parse.nat()
  a

def chainInferred(): {Parse Char} Bool :=
  let a := (0 < Parse.nat() <= Parse.nat())
  a

def chainBare(): {Parse Char} Bool :=
  let a := 0 < Parse.nat() <= Parse.nat()
  a

def annotated(): {Parse Char} Bool :=
  let a: Bool := 0 < Parse.nat() <= Parse.nat()
  a
