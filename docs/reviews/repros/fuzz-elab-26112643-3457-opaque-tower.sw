-- SW-4932, reduced by Overmind from fuzz batch 67 case 3457: with `idn`
-- opaque the casts stay stuck and the refusal (E-REFL, correct) takes 7.8 s
-- and about 1.9 GB at depth 40; peak memory grows about 55-60 MB a level
-- past depth 8 (12: 347 MB, 20: 812 MB). It should cost about what the
-- accepted version does (0.7 s, 170 MB).
import Std (Nat)

opaque def idn (k: Nat): Nat := k

def tower (hyp: ∀ (k: Nat) => idn k = k) (n: Nat): Nat := match n with
  | Zero => 0
  | Succ m => J (y e => Nat) 0 (hyp (tower hyp m))

theorem towerZero ∀ (hyp: ∀ (k: Nat) => idn k = k): tower hyp 40 = 0 := byComputing
