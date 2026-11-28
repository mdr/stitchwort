-- SW-4981: the second `match`'s annotated type mentions the first, which
-- calls the owner `f`, so it is unfinished: the elaborator refuses it
-- (E-MUTUAL-SIGNATURE) before declaring the helper to the kernel.
def f (b: Bool): Nat → Nat
  | Zero => 0
  | Succ k =>
    let pick: Nat := match b with
      | True => f b k
      | False => 2
    let same: pick = pick := match b with
      | True => byComputing
      | False => byComputing
    0
