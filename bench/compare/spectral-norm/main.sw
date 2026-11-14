-- The Benchmarks Game's spectral-norm: the largest singular value of the
-- infinite matrix a(i, j) = 1 / ((i + j) (i + j + 1) / 2 + i + 1), cut to N by
-- N (default 1000; `-- 100` for a small run), by ten rounds of the power
-- method on AᵀA. The answer is printed to nine decimals.
--
-- There is no `Float.sqrt` yet, so the one square root at the end is Newton's
-- method (`sqrt`); it agrees with a correctly rounded root far beyond the nine
-- printed digits.
import Std (Array, Fail, Float, IO, Int, List, Nat, Text)

--| Entry `i`, `j` of the matrix.
def entry (i j: Nat): Float := 1.0 / Float.ofNat ((i + j) * (i + j + 1) / 2 + i + 1)

--| Row `i` of A applied to `vector`, or of Aᵀ when `transposed`.
def dot (size: Nat) (transposed: Bool) (vector: Array Float) (i: Nat): Float :=
  List.foldLeft (List.range 0 size) 0.0 (sum j =>
    let weight := if transposed then entry j i else entry i j
    sum + weight * vector.getOr j 0.0)

--| A applied to `vector`, or Aᵀ when `transposed`.
def apply (size: Nat) (transposed: Bool) (vector: Array Float): Array Float :=
  Array.tabulate size (dot size transposed vector)

--| AᵀA applied to `vector`.
def normal (size: Nat) (vector: Array Float): Array Float := apply size True (apply size False vector)

--| The power method's `u` and `v` after `rounds` rounds from `u`: `v = AᵀA u`,
--| then `u = AᵀA v`.
def power (size: Nat): Nat → Array Float → Array Float → (Array Float, Array Float)
  | Zero, u, v => (u, v)
  | Succ rest, u, v =>
    let next := normal size u
    power size rest (normal size next) next

def dotProduct (xs ys: Array Float): Float :=
  List.foldLeft (List.range 0 xs.size) 0.0 (sum i => sum + xs.getOr i 0.0 * ys.getOr i 0.0)

--| The square root of a positive `x` by Newton's method, from 1.
def sqrt (x: Float): Float := List.foldLeft (List.range 0 30) 1.0 (guess step => (guess + x / guess) / 2.0)

--| `x` to nine decimals, rounded half up like `%.9f` except for exact ties.
def nineDecimals (x: Float): Text := match Float.toInt (Float.round (x * 1000000000.0)) with
  | None => "nan"
  | Some scaled =>
    let units := scaled.toNat
    "${units / 1000000000}.${(Nat.toText (units % 1000000000)).padLeft 9 '0'}"

def main(): {IO, Fail} () :=
  let size := match IO.args() with
    | [] => 1000
    | [text] => Fail.need text.toNat "expected no arguments, or a size"
    | _ => Fail.fail "expected no arguments, or a size"
  let ones := Array.replicate size 1.0
  let (u, v) := power size 10 ones ones
  IO.print (nineDecimals (sqrt (dotProduct u v / dotProduct v v)))
