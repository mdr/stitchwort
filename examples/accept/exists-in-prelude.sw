-- `Exists` and its constructor `Witness` are in the prelude beside `And` and
-- `Or`: no `import Std (Exists)` is needed to state or build one.

theorem someSquare: Exists Nat (n => n * n = 49) := Witness 7 byComputing

theorem someOrOther: (Exists Nat (n => n = 1)) ∨ (Exists Nat (n => n = 2)) := Inl (Witness 1 byComputing)

theorem takenApart ∀ (h: Exists Nat (n => n = 3)): Exists Nat (n => n + 1 = 4) := match h with
  | Witness n e => Witness n (rewrite e then byComputing)

test "exists is in the prelude" := True
