-- `import Std (Eq)` makes the namespace `Eq` usable as a qualifier, though
-- it holds no name of its own. Dot notation needs no import.
import Std (Eq)

theorem flip (a: Nat) (b: Nat) (p: a = b): b = a := Eq.sym p

theorem flipDot (a: Nat) (b: Nat) (p: a = b): b = a := p.sym
