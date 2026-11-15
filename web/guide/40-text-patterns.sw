-- A word is a pattern: each arm matches exactly that text.
type Command = | Go (steps: Nat) | Turn | Stop

def command (word: Text) (steps: Nat): Option Command := match word with
  | "go" | "walk" => Some (Go steps)
  | "turn" => Some Turn
  | "stop" | "halt" => Some Stop
  | _ => None

-- On a list of characters, the same literal is that list, as a lexer
-- wants. It mixes with list patterns.
def token: List Char → Text
  | "->" => "arrow"
  | "=>" => "fat arrow"
  | ['-', '-', .._] => "comment"
  | _ => "other"

-- `"--" ++ rest` matches anything that starts with `--`, and names the rest.
def flag (arg: Text): Option Text := match arg with
  | "--" ++ name => Some name
  | "-" ++ letter => Some letter
  | _ => None

test "a command" := command "walk" 3 == Some (Go 3)
test "not a command" := command "run" 3 == None
test "tokens" := token "->".toList == "arrow" ∧ token "-- note".toList == "comment"
test "flags" := flag "--verbose" == Some "verbose" ∧ flag "-v" == Some "v" ∧ flag "v" == None

-- A call on a known word computes, so `rfl` proves what it gives.
theorem haltStops: command "halt" 0 = Some Stop := rfl
