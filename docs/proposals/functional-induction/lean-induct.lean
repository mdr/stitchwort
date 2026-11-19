def withoutR (ok : Nat → Nat → Bool) (behind : List Nat) : List Nat → List Nat
  | [] => behind
  | a :: b :: after => if ok a b then withoutR ok (b :: behind) after else withoutR ok (a :: behind) (b :: after)
  | a :: after => withoutR ok (a :: behind) after

#check @withoutR.induct
#check @withoutR.fun_cases

def g : Nat → Nat
  | 0 => 0
  | 3 => 1
  | n+1 => g n

#check @g.induct

mutual
def ev : Nat → Bool
  | 0 => true
  | n+1 => od n
def od : Nat → Bool
  | 0 => false
  | n+1 => ev n
end
#check @ev.induct
#check @ev.mutual_induct

def log2 (n : Nat) : Nat := if h : n ≥ 2 then 1 + log2 (n / 2) else 0
#check @log2.induct

inductive T | node : List T → T
def T.size : T → Nat
  | .node ts => 1 + (ts.attach.map (fun ⟨t, _⟩ => t.size)).sum
#check @T.size.induct

theorem lenLe (ok : Nat → Nat → Bool) (behind rest : List Nat) : (withoutR ok behind rest).length ≤ behind.length + rest.length := by
  fun_induction withoutR ok behind rest <;> grind
def step (owed x : Nat) : Option Nat := if x = 0 then none else some (owed + x)

def stands (owed : Nat) : List Nat → Bool
  | [] => owed == 0
  | x :: rest =>
    if x = 1 then
      decide (owed ≤ 5) && (match step owed x with
        | none => false
        | some still => stands still rest)
    else stands owed rest
#check @stands.induct

def sumMap : List (List Nat) → List Nat
  | [] => []
  | xs :: more => xs.map (fun x => x + (sumMap more).length) ++ sumMap more
#check @sumMap.induct
