-- SW-4913, shape (a): the second `match` calls its owner, so it is admitted
-- with it; the comparison in its arm is made when the owner's body is
-- finished, before either reaches the kernel.
def f (b: Bool): Nat → Nat
  | Zero => 0
  | Succ k =>
    let pick: Nat := match b with
      | True => 2
      | False => 2
    let same: pick = 0 := match b with
      | True => byComputing
      | False =>
        let x := f b k
        byComputing
    0
