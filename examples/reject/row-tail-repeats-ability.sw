-- expect-error: E-DUPLICATE
-- A row has each ability at most once, also when a row variable is
-- instantiated by hand with a signature that already holds the ability:
-- `{Log | dupSig}` would be `Log` twice. (`opsOf` and `resOf` read the
-- signature of `sayN`'s row, since source can't name an ability's types.)
import Std.Effect (Comp, Sig)

ability Log where
  say: Nat -> {Log} ()

def opsOf [op: Type] [res: op -> Type] [a: Type] (f: Nat -> Comp op res a): Type := op
def resOf [op: Type] [res: op -> Type] [a: Type] (f: Nat -> Comp op res a): op -> Type := res

def sayN (n: Nat): {Log} () := say n

def dupSig: Sig := MkSig (opsOf sayN) (resOf sayN)

def twice(): {Log | dupSig} () :=
  say 1
  say 2
