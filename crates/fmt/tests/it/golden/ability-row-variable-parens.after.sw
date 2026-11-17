-- After a row that starts with a variable (`{e}`), the brackets stay: bare,
-- the row would read as a record applied to what follows.
def a: {e} (.f) := x
def b: {e} (match x with | _ => 1) := z
def c: {e} (include "x") y := z
def d: {e} (-x) * y := z
def e: {e} (!x) ∧ y := z
def f: {e} (if a then b else c) := z
-- Kept off: a row that starts with an ability name has no such trouble.
def g: {Fail, e} List Nat := z
def h: {e} List Nat := z
