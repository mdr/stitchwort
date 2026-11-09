import Std.Data.TreeMap

-- A mix of operations on an ordered map of Nat keys to Nat values, driven by a
-- Park-Miller linear congruential generator. Each step draws x; the key is
-- x % keys and the operation is (x / keys) % 10: 0-3 insert, 4-6 lookup,
-- 7-8 update (add to the existing value, else insert), 9 remove. The answer is
-- the final size and a checksum of the lookups and of the final map folded in
-- key order. `Std.TreeMap` is Lean's ordered map (`Lean.RBMap` is deprecated
-- in its favour); `Std.HashMap` would be the counterpart of Python's dict.

def keys : Nat := 200000
def modulus : Nat := 2147483647
def checkModulus : Nat := 1000000007

inductive Op where
  | insert | lookup | update | remove

def Op.ofDraw (draw : Nat) : Op :=
  let slot := draw / keys % 10
  if slot < 4 then .insert
  else if slot < 7 then .lookup
  else if slot < 9 then .update
  else .remove

structure Workload where
  map : Std.TreeMap Nat Nat compare
  seed : Nat
  check : Nat

def Workload.start : Workload := { map := {}, seed := 1, check := 0 }

def Workload.step (w : Workload) (step : Nat) : Workload :=
  let draw := w.seed * 48271 % modulus
  let key := draw % keys
  let value := step % 1000
  match Op.ofDraw draw with
  | .insert => { w with map := w.map.insert key value, seed := draw }
  | .lookup =>
    match w.map[key]? with
    | some found => { w with seed := draw, check := (w.check + found + 1) % checkModulus }
    | none => { w with seed := draw }
  | .update =>
    let updated := (w.map.getD key 0) + value
    { w with map := w.map.insert key updated, seed := draw }
  | .remove => { w with map := w.map.erase key, seed := draw }

def Workload.run (w : Workload) (from_ : Nat) : Nat → Workload
  | 0 => w
  | n + 1 => (w.step from_).run (from_ + 1) n

def Workload.finish (w : Workload) : Nat :=
  w.map.foldl (fun acc key value => (acc * 31 + key * 7 + value) % checkModulus) w.check

def main (args : List String) : IO Unit := do
  let steps := match args with
    | [] => 1000000
    | text :: _ => text.toNat!
  let done := Workload.start.run 0 steps
  IO.println s!"{done.map.size} {done.finish}"
