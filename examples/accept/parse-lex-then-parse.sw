-- Lexing, then parsing, with Std.Parse: a sum of numbers such as "1 + 20 + 3".
-- The lexer's tokens remember where they were read (`Parse.located`); the
-- parser reads the tokens with the same combinators, and a failure in it
-- names the line and column of the token it stopped at (SW-3283).
import Std (Fail, List, Option, Parse, Result, Text)
import Std.Fail (toResult)

type Token = | Num (value: Nat) | Plus

def number(): {Parse Char} Parse.Located Token := Parse.located (() => Num Parse.nat())

def plus(): {Parse Char} Parse.Located Token := Parse.located (() =>
  Parse.char '+'
  Plus)

def lexToken(): {Parse Char} Parse.Located Token :=
  Parse.spaces()
  Parse.oneOf [number, plus]

def lex(): {Parse Char} List (Parse.Located Token) := Parse.many lexToken

def numberOf (token: Parse.Located Token): Option Nat := match token with
  | { value = Num value, .. } => Some value
  | _ => None

def isPlus (token: Parse.Located Token): Option () := match token with
  | { value = Plus, .. } => Some ()
  | _ => None

def operand(): {Parse (Parse.Located Token)} Nat := Parse.one "a number" numberOf

def sum(): {Parse (Parse.Located Token)} Nat :=
  let first := operand()
  let more := Parse.many (() =>
    Parse.one "'+'" isPlus
    operand())
  more.foldLeft first (total next => total + next)

def parseSum (input: Text): {Fail} Nat := Parse.tokens input lex sum

test "a sum" := toResult (() => parseSum "1 + 20 + 3") == Ok 24
test "one operand" := toResult (() => parseSum "7") == Ok 7
test "a missing operand, past the last token" :=
  toResult (() => parseSum "1 +") == Err "line 1, column 4: expected a number, got the end of the input"
test "an operator where an operand is expected" :=
  toResult (() => parseSum "1 + + 2") == Err "line 1, column 5: expected a number, got '+'"
test "two numbers in a row" :=
  toResult (() => parseSum "1 2") == Err "line 1, column 3: expected '+' or the end of the input, got '2'"
test "a lexing failure keeps the lexer's message" :=
  toResult (() => parseSum "1 - 2") == Err "line 1, column 3: expected a number or '+', got '-'"

theorem sumIsTwentyFour: toResult (() => parseSum "1 + 20 + 3") = Ok 24 := byComputing

-- What the lexer reads. A number token reads digits and is a `Num` of their
-- value (`Parse.readsLocated` gives the value's reading, `readsMap` and
-- `readsNat` the number's).
def NumberRead (read: List Char) (token: Parse.Located Token): Prop :=
  read ≠ [] ∧ read.all Parse.isDigit = True ∧ token.value = Num (Parse.digitsValue read)

theorem readsNumber: Parse.Reads number NumberRead :=
  Parse.readsWeaken
    (Parse.readsLocated (() => Num Parse.nat()) _ (Parse.readsMap Parse.nat Num _ Parse.readsNat))
    (read token h =>
      match h with
        | Witness n (Both (Both some (Both digits made)) is) => Both some (Both digits (rewrite made at is then is)))

--| Every token, with the spaces before it, reads at least one character.
def TokenRead (read: List Char) (token: Parse.Located Token): Prop := read ≠ []

theorem readsPlus: Parse.Reads plus (read token => read ≠ []) :=
  Parse.readsLocated
    (() =>
      Parse.char '+'
      Plus)
    (read value => read ≠ [])
    (Parse.readsThen (Parse.readsChar '+') (charRead u isPlus =>
      Parse.readsDone Plus _ (rewrite isPlus then List.appendNotNilLeft ['+'] [] (List.consNotNil '+' []))))

theorem readsLexToken: Parse.Reads lexToken TokenRead := Parse.readsThen Parse.readsSpaces (spaces u spaced =>
  Parse.readsWeaken
    (Parse.readsOneOf
      (read token => read ≠ [])
      [number, plus]
      (Both (Parse.readsWeaken readsNumber (read token h => h.left)) (Both readsPlus Trivial)))
    (read token some => List.appendNotNilRight spaces read some))

-- What the parser reads: one `Num` token and the number it carries.
def NumberToken (read: List (Parse.Located Token)) (value: Nat): Prop :=
  ∃ (token: Parse.Located Token) => read = [token] ∧ token.value = Num value

theorem numberOfNum ∀ (token: Parse.Located Token) (value: Nat)
    (selected: numberOf token = Some value):
    token.value = Num value :=
  match token with | { value = Num n, .. } => rewrite Option.someInjective selected

theorem readsOperand: Parse.Reads operand NumberToken :=
  Parse.readsWeaken (Parse.readsOne "a number" numberOf) (read value h =>
    match h with | Witness token (Both one selected) => Witness token (Both one (numberOfNum token value selected)))

--| A successful `Parse.tokens` of one operand: the lexer split the input into
--| tokens that each read a character, and the parser read exactly one, a
--| `Num` of the value.
theorem operandTokens ∀ (input: Text) (value: Nat)
    (parsed: toResult (() => Parse.tokens input lex operand) = Ok value):
    ∃ (read: List Char) => ∃ (tokens: List (Parse.Located Token)) => Parse.Each TokenRead read tokens
      ∧ NumberToken tokens value :=
  match Parse.tokensReads input lex operand
    (Parse.Each TokenRead)
    NumberToken
    value
    parsed
    (Parse.readsMany lexToken TokenRead readsLexToken)
    readsOperand with
    | Witness read (Witness ending (Witness tokens (Both split (Both lexed (Both ended operandRead))))) =>
      Witness read (Witness tokens (Both lexed operandRead))

-- Completeness: "7" lexes to one token, and the parser takes it.
theorem parsesSeven: toResult (() => Parse.tokens "7" lex operand) = Ok 7 :=
  Parse.runsTokens "7" lex operand
    [{ value = Num 7, offset = 0, length = 1 }]
    7
    byComputing
    (Parse.runsOne "a number" numberOf { value = Num 7, offset = 0, length = 1 } 7 [] byComputing)
