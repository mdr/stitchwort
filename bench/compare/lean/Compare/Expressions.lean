inductive Operator where
  | plus
  | times

def Operator.apply : Operator → Nat → Nat → Nat
  | .plus, left, right => left + right
  | .times, left, right => left * right

inductive Expression where
  | number (value : Nat)
  | operation (operator : Operator) (left right : Expression)
  | parenthesised (inner : Expression)

def Expression.value : Expression → Nat
  | .number value => value
  | .operation operator left right => operator.apply left.value right.value
  | .parenthesised inner => inner.value

/-- The operators of each precedence level, loosest first. -/
abbrev Precedence := List (List Operator)

def samePrecedence : Precedence := [[.plus, .times]]

def additionFirst : Precedence := [[.times], [.plus]]

def Operator.spaced : Operator → String
  | .plus => " + "
  | .times => " * "

/-- A parse reads from a byte position and gives the expression and the
position after it; an error is a message. -/
abbrev Parser := ByteArray → Nat → Except String (Expression × Nat)

def hasAt (line : ByteArray) (position : Nat) (text : String) : Bool :=
  let bytes := text.toUTF8
  position + bytes.size <= line.size && (List.range bytes.size).all fun i => line[position + i]! == bytes[i]!

def parseNat (line : ByteArray) (position : Nat) : Except String (Nat × Nat) := Id.run do
  let mut end_ := position
  let mut value := 0
  while end_ < line.size && line[end_]! >= 48 && line[end_]! <= 57 do
    value := value * 10 + (line[end_]!.toNat - 48)
    end_ := end_ + 1
  if end_ == position then return .error s!"expected a number at {position}"
  return .ok (value, end_)

/-- Whichever of `operators` is next at `position`, with the position after it. -/
def nextOperator (line : ByteArray) (position : Nat) (operators : List Operator) : Option (Operator × Nat) :=
  operators.findSome? fun operator =>
    if hasAt line position operator.spaced then some (operator, position + 3) else none

mutual
  /-- The loosest level's chain, left-associative, over the tighter levels. -/
  partial def level (precedence : Precedence) : Precedence → Parser
    | [], line, position => operand precedence line position
    | operators :: tighter, line, position => do
      let (first, after) ← level precedence tighter line position
      chain precedence operators tighter line first after
  partial def chain (precedence : Precedence) (operators : List Operator) (tighter : Precedence)
      (line : ByteArray) (left : Expression) (position : Nat) : Except String (Expression × Nat) :=
    match nextOperator line position operators with
    | some (operator, afterOperator) =>
      match level precedence tighter line afterOperator with
      | .ok (right, after) => chain precedence operators tighter line (.operation operator left right) after
      | .error _ => .ok (left, position)
    | none => .ok (left, position)
  partial def operand (precedence : Precedence) : Parser := fun line position =>
    if hasAt line position "(" then do
      let (inner, after) ← level precedence precedence line (position + 1)
      if hasAt line after ")" then .ok (.parenthesised inner, after + 1)
      else .error s!"expected ) at {after}"
    else do
      let (value, after) ← parseNat line position
      .ok (.number value, after)
end

def parseLine (precedence : Precedence) (line : String) : Except String Expression := do
  let bytes := line.toUTF8
  let (expression, after) ← level precedence precedence bytes 0
  if after != bytes.size then throw s!"unexpected input at {after}"
  return expression

def homeworkSum (precedence : Precedence) (lines : List String) : Nat :=
  lines.foldl (fun total line =>
    match parseLine precedence line with
    | .ok expression => total + expression.value
    | .error message => panic! message) 0

def main : IO Unit := do
  let stdin ← IO.getStdin
  let lines := (← stdin.readToEnd).splitOn "\n" |>.filter (· ≠ "")
  IO.println s!"Part 1: {homeworkSum samePrecedence lines}"
  IO.println s!"Part 2: {homeworkSum additionFirst lines}"
