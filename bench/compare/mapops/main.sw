-- A mix of operations on std's `Map` of Nat keys to Nat values, driven by a
-- Park-Miller linear congruential generator. Each step draws `x`; the key is
-- `x % keys` and the operation is `(x / keys) % 10`: 0 to 3 insert, 4 to 6
-- look up, 7 and 8 update (`insertWith`: add to the existing value, else
-- insert), 9 remove. The answer is the final size and a checksum of the
-- lookups and of the final map folded in key order. N is the argument of
-- steps (default 1000000; `-- 1000` for a small run).
import Std (Fail, IO, List, Map, Nat, Option)

def keys: Nat := 200000

def modulus: Nat := 2147483647

def checkModulus: Nat := 1000000007

--| What one step does to the map.
type Op = | Insert | Lookup | Update | Remove

--| The operation a draw selects.
def Op.ofDraw (draw: Nat): Op :=
  let slot := draw / keys % 10
  if slot < 4 then Insert else if slot < 7 then Lookup else if slot < 9 then Update else Remove

--| The map, the generator's state and the running checksum.
type Workload = { map: Map Nat Nat, seed: Nat, check: Nat }

def Workload.start: Workload := { map = Map.empty, seed = 1, check = 0 }

--| One step, numbered `step`: draw, then apply the operation it selects.
def Workload.step (w: Workload) (step: Nat): Workload :=
  let draw := w.seed * 48271 % modulus
  let key := draw % keys
  let value := step % 1000
  match Op.ofDraw draw with
    | Insert => { w | map = w.map.insert key value, seed = draw }
    | Lookup =>
      match w.map.get key with
        | Some found => { w | seed = draw, check = (w.check + found + 1) % checkModulus }
        | None => { w | seed = draw }
    | Update => { w | map = w.map.insertWith key value Nat.add, seed = draw }
    | Remove => { w | map = w.map.remove key, seed = draw }

--| `steps` steps from step `from`.
def Workload.run (w: Workload) (from steps: Nat): Workload := match steps with
  | Zero => w
  | Succ rest => (w.step from).run (from + 1) rest

--| The checksum with the final map folded in, in key order.
def Workload.finish (w: Workload): Nat :=
  w.map.foldLeft w.check (acc key value => (acc * 31 + key * 7 + value) % checkModulus)

def main(): {IO, Fail} () :=
  let steps := match IO.args() with
    | [] => 1000000
    | [text] => Fail.need text.toNat "expected no arguments, or a count"
    | _ => Fail.fail "expected no arguments, or a count"
  let done := Workload.start.run 0 steps
  IO.print "${done.map.size} ${done.finish}"
