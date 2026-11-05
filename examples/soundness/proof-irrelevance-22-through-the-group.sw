-- expect-error: E-REFL
-- `grpA` takes `h` apart (with `J`), so `h` isn't inert in `grpB` either,
-- which only passes it on: the marks are a fixed point over the group.
-- Partner: `quietGroup` in accept/proof-irrelevance.sw.
import Std (Nat)

def grpA (n: Nat) (h: 0 = 0): Nat :=
  match n with
    | Zero => J (y e => Nat) 0 h
    | Succ m => grpB m h

def grpB (n: Nat) (h: 0 = 0): Nat :=
  match n with
    | Zero => 1
    | Succ m => grpA m h

theorem t22 (n: Nat) (p: 0 = 0) (q: 0 = 0): grpB n p = grpB n q := rfl
