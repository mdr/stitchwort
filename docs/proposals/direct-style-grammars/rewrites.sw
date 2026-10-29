-- Evidence for docs/proposals/direct-style-grammars.md §5: three AoC
-- grammars written today's way, with three library combinators (`after`,
-- `before`, `between`), and with the expression `let` standing in for the
-- proposed `(a; b)` (drop each `let () :=` to get that form). Each version
-- gives the same values and the same error messages.
--
--   $ stitchwort test docs/proposals/direct-style-grammars/rewrites.sw

import Std (Fail, Int, List, Nat, Parse, Result, Text)
import Std.Parse (char, findAll, int, nat, natDigits, newline, oneOf, pick, text)

def lineResult (line: Text) (parser: () → {Parse} a): Result a Text := Fail.toResult (() => Parse.line line parser)

def allResult (input: Text) (parser: () → {Parse} a): Result a Text := Fail.toResult (() => Parse.all input parser)

-- The proposed combinators (§4.1).

-- `prefix`, then `parser`'s value: Lean's `string prefix *> parser`.
def after (prefix: Text) (parser: () → {Parse} a): {Parse} a :=
  text prefix
  parser()

-- `value`, then `suffix`: Lean's `value <* string suffix`. Meant for `|>`,
-- so that the value is computed (and its arguments run) first.
def before (value: a) (suffix: Text): {Parse} a :=
  text suffix
  value

-- `open`, `parser`'s value, then `close`.
def between (open: Text) (close: Text) (parser: () → {Parse} a): {Parse} a :=
  text open
  let value := parser()
  text close
  value

-- Day 3 (2024): "mul(44,46)".

type Instruction =
  | Mul (left: Nat) (right: Nat)
  | Do
  | Dont

def shortNumber(): {Parse} Nat := natDigits 1 3

def mulToday(): {Parse} Instruction :=
  text "mul("
  let left := shortNumber()
  char ','
  let right := shortNumber()
  char ')'
  Mul left right

def mulAfterBefore(): {Parse} Instruction := Mul (after "mul(" shortNumber) (after "," shortNumber) |> before ")"

def mulBetween(): {Parse} Instruction := between "mul(" ")" (() => Mul (shortNumber()) (after "," shortNumber))

-- `Mul (text "mul("; shortNumber()) (char ','; shortNumber()) |> before ")"`
-- once `;` sequences (§6).
def mulSemicolon(): {Parse} Instruction :=
  Mul (let () := text "mul("; shortNumber()) (let () := char ','; shortNumber()) |> before ")"

-- The whole of day 3's `instruction` in that form.
def instruction(): {Parse} Instruction :=
  oneOf [
    () => Mul (let () := text "mul("; shortNumber()) (let () := char ','; shortNumber()) |> before ")",
    () => pick [("do()", Do), ("don't()", Dont)]
  ]

test "day 3: instruction in context" :=
  allResult "xmul(2,4)%don't()_mul(5,5)+mul(32,64]do()mul(11,8)" (() => findAll instruction)
    == Ok [Mul 2 4, Dont, Mul 5 5, Do, Mul 11 8]

-- Every part a tuple item, matched against a pattern.
def mulTuple(): {Parse} Instruction :=
  let (_, left, _, right, _) := (text "mul(", shortNumber(), char ',', shortNumber(), char ')')
  Mul left right

test "day 3: the same value" :=
  [mulToday, mulAfterBefore, mulBetween, mulSemicolon, mulTuple].map (parser => lineResult "mul(44,46)" parser)
    == [Ok (Mul 44 46), Ok (Mul 44 46), Ok (Mul 44 46), Ok (Mul 44 46), Ok (Mul 44 46)]

test "day 3: the same errors" :=
  ["mul[1,2)", "mul(1;2)", "mul(1,2]", "mul(1234,5)"].map (line => [mulToday, mulAfterBefore, mulBetween, mulSemicolon, mulTuple].map (parser => lineResult line parser))
    == [
      List.replicate 5 (Err "column 1: expected 'mul(', got 'mul['"),
      List.replicate 5 (Err "column 6: expected ',', got ';'"),
      List.replicate 5 (Err "column 8: expected ')', got ']'"),
      List.replicate 5 (Err "column 5: expected a number of 1 to 3 digits, got '1'")
    ]

-- Day 14 (2024): "p=0,4 v=3,-3".

type Position = { x: Nat, y: Nat }

type Velocity = { x: Int, y: Int }

type Robot = { position: Position, velocity: Velocity }

def robotToday(): {Parse} Robot :=
  text "p="
  let x := nat()
  text ","
  let y := nat()
  text " v="
  let dx := int()
  text ","
  let dy := int()
  { position = { x, y }, velocity = { x = dx, y = dy } }

-- A record's fields run in the order they are written.
def robotAfter(): {Parse} Robot :=
  { position = ({ x = after "p=" nat, y = after "," nat }: Position), velocity = ({ x = after " v=" int, y = after "," int }: Velocity) }

def robotSemicolon(): {Parse} Robot := {
  position = ({ x = (let () := text "p="; nat()), y = (let () := char ','; nat()) }: Position),
  velocity = ({ x = (let () := text " v="; int()), y = (let () := char ','; int()) }: Velocity)
}

test "day 14: the same value" :=
  [robotToday, robotAfter, robotSemicolon].map (parser => lineResult "p=0,4 v=3,-3" parser)
    == List.replicate 3 (Ok ({ position = { x = 0, y = 4 }, velocity = { x = 3, y = -3 } }))

test "day 14: the same errors" :=
  [robotToday, robotAfter, robotSemicolon].map (parser => lineResult "p=0,4 w=3,-3" parser)
    == List.replicate 3 (Err "column 6: expected ' v=', got ' w='")

-- Day 13 (2024): "Button A: X+94, Y+34", twice, then "Prize: X=8400, Y=5400".

type Offset = { x: Int, y: Int }

type Machine = { buttonA: Offset, buttonB: Offset, prize: Offset }

def offsetToday (sign: Text): {Parse} Offset :=
  text "X${sign}"
  let x := nat()
  text ", Y${sign}"
  let y := nat()
  { x = x.toInt, y = y.toInt }

def offsetAfter (sign: Text): {Parse} Offset := { x = (after "X${sign}" nat).toInt, y = (after ", Y${sign}" nat).toInt }

def offsetSemicolon (sign: Text): {Parse} Offset :=
  { x = (let () := text "X${sign}"; nat().toInt), y = (let () := text ", Y${sign}"; nat().toInt) }

def machineToday(): {Parse} Machine :=
  text "Button A: "
  let buttonA := offsetToday "+"
  newline()
  text "Button B: "
  let buttonB := offsetToday "+"
  newline()
  text "Prize: "
  let prize := offsetToday "="
  { buttonA, buttonB, prize }

def machineAfter(): {Parse} Machine := {
  buttonA = after "Button A: " (() => offsetAfter "+"),
  buttonB = (let () := newline(); after "Button B: " (() => offsetAfter "+")),
  prize = (let () := newline(); after "Prize: " (() => offsetAfter "="))
}

def machineSemicolon(): {Parse} Machine := {
  buttonA = (let () := text "Button A: "; offsetSemicolon "+"),
  buttonB = (let () := newline(); let () := text "Button B: "; offsetSemicolon "+"),
  prize = (let () := newline(); let () := text "Prize: "; offsetSemicolon "=")
}

def machineText: Text := "Button A: X+94, Y+34\nButton B: X+22, Y+67\nPrize: X=8400, Y=5400"

test "day 13: the same value" :=
  [machineToday, machineAfter, machineSemicolon].map (parser => allResult machineText parser)
    == List.replicate 3 (Ok ({ buttonA = { x = 94, y = 34 }, buttonB = { x = 22, y = 67 }, prize = { x = 8400, y = 5400 } }))
