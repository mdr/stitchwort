import Std.Data.HashMap
open Std

inductive Rule where
  | letter (letter : Char)
  | alternatives (sequences : List (List Nat))
  deriving Inhabited

/-- The rules as numbered in the input, in order (a later entry for a number wins). -/
structure Received where
  numbered : List (Nat × Rule)
  messages : List (Array Char)

def parseRule (line : String) : Nat × Rule :=
  match line.splitOn ": " with
  | [number, body] =>
    if body.startsWith "\"" then (number.toNat!, .letter (body.toList[1]!))
    else (number.toNat!, .alternatives ((body.splitOn " | ").map fun sequence =>
      (sequence.splitOn " ").map String.toNat!))
  | _ => panic! s!"bad rule {line}"

def parseReceived (input : String) : Received :=
  let lines := input.splitOn "\n"
  let rules := lines.takeWhile (· ≠ "")
  let messages := (lines.dropWhile (· ≠ "")).drop 1 |>.filter (· ≠ "")
  { numbered := rules.map parseRule, messages := messages.map (·.toList.toArray) }

/-- Rules as a table; where a number is given twice, the earlier entry wins. -/
def ruleTable (numbered : List (Nat × Rule)) : HashMap Nat Rule :=
  numbered.foldr (fun (number, rule) table => table.insert number rule) {}

mutual
  /-- The positions the message can have been read up to, matching rule `number`
  from `position`, within `fuel` rule applications. -/
  def endsWith (table : HashMap Nat Rule) (message : Array Char) (fuel : Nat) (number position : Nat) : List Nat :=
    match fuel with
    | 0 => []
    | fuel + 1 =>
      match table[number]? with
      | none => []
      | some (.letter letter) => if message[position]? == some letter then [position + 1] else []
      | some (.alternatives sequences) =>
        sequences.flatMap fun sequence => endsWithAll table message fuel sequence position
  def endsWithAll (table : HashMap Nat Rule) (message : Array Char) (fuel : Nat) : List Nat → Nat → List Nat
    | [], position => [position]
    | number :: later, position =>
      (endsWith table message fuel number position).flatMap fun after => endsWithAll table message fuel later after
end

def matchesCompletely (table : HashMap Nat Rule) (ruleCount : Nat) (message : Array Char) : Bool :=
  let fuel := (message.size + 1) * (ruleCount + 2)
  (endsWith table message fuel 0 0).any (· == message.size)

def matchingCount (received : Received) : Nat :=
  let table := ruleTable received.numbered
  let ruleCount := received.numbered.length
  received.messages.countP (matchesCompletely table ruleCount)

def Received.withLoops (received : Received) : Received :=
  { received with numbered :=
      (8, .alternatives [[42], [42, 8]]) :: (11, .alternatives [[42, 31], [42, 11, 31]]) :: received.numbered }

def main : IO Unit := do
  let stdin ← IO.getStdin
  let received := parseReceived (← stdin.readToEnd)
  IO.println s!"Part 1: {matchingCount received}"
  IO.println s!"Part 2: {matchingCount received.withLoops}"
