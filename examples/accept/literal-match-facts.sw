-- What a catch-all arm knows after literal patterns
-- (docs/proposals/literal-match-facts.md): that the value is none of the
-- literals above it. So in a proof's `_` arm, a program's own match on the
-- same literals (or fewer) takes its `_` arm too, and "no other key is a
-- command" is a proof by the same match.
import Std (List, Option, Void)

type Command = | Up | Down | Quit

def commandOf (char: Char): Option Command :=
  match char with
    | 'k' => Some Up
    | 'w' => Some Up
    | 'j' => Some Down
    | 's' => Some Down
    | 'q' => Some Quit
    | _ => None

def commandKeys: List Char := ['k', 'w', 'j', 's', 'q']

-- A key that is listed, decided (in each arm below, the key is a literal).
theorem listed (char: Char) [auto isIn: char ∈ commandKeys]: char ∈ commandKeys := isIn

-- The catch-all, directly: any other character is no command.
theorem otherIsNone (char: Char): Or (char ∈ commandKeys) (commandOf char = None) :=
  match char with
    | 'k' => Inl (listed char)
    | 'w' => Inl (listed char)
    | 'j' => Inl (listed char)
    | 's' => Inl (listed char)
    | 'q' => Inl (listed char)
    | _ => Inr rfl

-- So a character that is a command is one of the five.
theorem onlyListed (char: Char) (command: Command) (found: commandOf char = Some command): char ∈ commandKeys :=
  match char with
    | 'k' => listed char
    | 'w' => listed char
    | 'j' => listed char
    | 's' => listed char
    | 'q' => listed char
    | _ => Void.exfalso (Option.noneNotSome command found)

-- From hypotheses: knowing the number is none of the literals, match on
-- them, rule each out, and the `_` arm is the program's.
def kind: Nat → Nat
  | 3 => 1
  | 7 => 2
  | _ => 0

theorem kindOfOther (n: Nat) (not3: Not (n = 3)) (not7: Not (n = 7)): kind n = 0 :=
  match n with
    | 3 => Void.exfalso (not3 rfl)
    | 7 => Void.exfalso (not7 rfl)
    | _ => rfl

-- A proof may list more literals than the program: the program's are among
-- them.
theorem kindOfBig (n: Nat): Or (kind n = 0) (Or (n = 3) (n = 7)) :=
  match n with
    | 0 => Inl rfl
    | 3 => Inr (Inl rfl)
    | 7 => Inr (Inr rfl)
    | _ => Inl rfl

-- Two numbers more than `n` is none of 3 and 7 when `n` is none of 1 and 5.
theorem kindShifted (n: Nat): Or (kind (Succ (Succ n)) = 0) (Or (n = 1) (n = 5)) :=
  match n with
    | 1 => Inr (Inl rfl)
    | 5 => Inr (Inr rfl)
    | _ => Inl rfl

-- Nested: an inner match on the same variable knows the outer literals too.
theorem kindNested (n: Nat): Or (kind n = 0) (Or (n = 3) (n = 7)) :=
  match n with
    | 3 => Inr (Inl rfl)
    | m =>
      match n with
        | 7 => Inr (Inr rfl)
        | _ => Inl rfl

-- On `Int` too: in each sign's catch-all, the size is none of that sign's
-- literals.
def sign: Int → Nat
  | 0 => 0
  | 1 => 1
  | (-1) => 2
  | _ => 3

theorem signOther (i: Int): Or (sign i = 3) (Or (i = 0) (Or (i = 1) (i = (-1)))) :=
  match i with
    | 0 => Inr (Inl rfl)
    | 1 => Inr (Inr (Inl rfl))
    | (-1) => Inr (Inr (Inr rfl))
    | _ => Inl rfl

test "commands" := ['k', 'j', 'q', 'x'].map commandOf == [Some Up, Some Down, Some Quit, None]
test "kind" := [3, 7, 8].map kind == [1, 2, 0]
