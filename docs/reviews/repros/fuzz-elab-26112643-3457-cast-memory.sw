-- A cast into data tests its ends (rule K) when it is evaluated, and a test
-- met again inside another is answered from the first. Here each cast's
-- ends mention the recursive call below it, so comparing them evaluates
-- that call twice, and each evaluation tests the next cast: without the
-- remembered answers the work doubled at each level (both theorems ran for
-- minutes), and the ends are evaluated with their calls kept as calls.
import Std (Nat)

def idn (k: Nat): Nat := match k with
  def idn (k: Nat): Nat := match k with
  | Zero => Zero
  | Succ j => Succ (idn j)

def tower (hyp: ∀ (k: Nat) => idn k = k) (n: Nat): Nat := match n with
  | Zero => 0
  | Succ m => J (y e => Nat) 0 (hyp (tower hyp m))

-- Both sides are the same stuck cast: no test is needed.
theorem oneStep ∀ (hyp: ∀ (k: Nat) => idn k = k): tower hyp 41 = J (y e => Nat) 0 (hyp (tower hyp 39)) := byComputing

-- Every level's cast fires, each tested once.
theorem towerZero ∀ (hyp: ∀ (k: Nat) => idn k = k): tower hyp 40 = 0 := byComputing
