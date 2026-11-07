structure Equation where
  testValue : Nat
  numbers : Array Nat
  deriving Inhabited

def parseEquation (line : String) : Equation :=
  match line.splitOn ":" with
  | [testValue, rest] =>
    { testValue := testValue.toNat!,
      numbers := (rest.splitOn " ").filter (· ≠ "") |>.map String.toNat! |>.toArray }
  | _ => panic! s!"bad equation {line}"

def digitCount (number : Nat) : Nat := if number < 10 then 1 else 1 + digitCount (number / 10)

def placeValue (number : Nat) : Nat := 10 ^ digitCount number

/-- Whether the numbers before `count`, taken from the end, can make `target`
with `first` the leftmost: undo the last operator at each step. -/
def canMake (concatenate : Bool) (numbers : Array Nat) (target : Nat) : Nat → Bool
  | 0 => target == numbers[0]!
  | index + 1 =>
    let last := numbers[index + 1]!
    (last <= target && canMake concatenate numbers (target - last) index)
    || (if last != 0 then target % last == 0 && canMake concatenate numbers (target / last) index
        else target == 0)
    || (concatenate &&
        let place := placeValue last
        target % place == last && canMake concatenate numbers (target / place) index)

def calibrationResult (concatenate : Bool) (equations : Array Equation) : Nat :=
  equations.foldl (fun total equation =>
    if canMake concatenate equation.numbers equation.testValue (equation.numbers.size - 1)
    then total + equation.testValue else total) 0

def main : IO Unit := do
  let stdin ← IO.getStdin
  let equations := (← stdin.readToEnd).splitOn "\n" |>.filter (· ≠ "") |>.map parseEquation |>.toArray
  IO.println s!"Part 1: {calibrationResult false equations}"
  IO.println s!"Part 2: {calibrationResult true equations}"
