--| Times the toy's phases on a generated Sprig file: `stitchwort run
--| Toy.Timing.main -- PHASE COPIES` lays out COPIES copies of a sample of
--| every construct (about 400 characters each), then, by PHASE, stops
--| (`print`), lexes the printed text (`lex`), applies rule N to the tokens
--| (`settle`), parses it (`parse`), parses and runs the four passes (`tidy`)
--| or formats it again (`format`), and says how much it made. The toy has no clock, so
--| time it from outside and subtract the time of the phase before from each: print, lex, settle, parse, tidy, format.

namespace Toy.Timing
import Toy.Fmt (..)
import Toy.Syntax (..)
import Std (Fail, List, NonEmptyList, Option, Parse, Result, Text)

def main(): {IO} () :=
  let args := IO.args()
  let phase := args.head |> .getOrElse "print"
  let copies := args.drop 1 |> .head |> .flatMap Text.toNat |> .getOrElse 100
  let file: SourceFile := { declarations = List.range 0 copies |> .concatMap sample }
  let source := file.print defaultWidth
  IO.print "${copies} copies: ${source.length} characters; ${phase}: ${measure phase source}"

def measure (phase source: Text): Text := match phase with
  | "lex" =>
    match lex source with
      | Ok found => "${found.tokens.length} tokens"
      | Err message => message
  | "settle" =>
    match lex source with
      | Ok found => "${found.settled.tokens.length} settled tokens"
      | Err message => message
  | "tidy" =>
    match parse source with
      | Ok parsed => "${parsed.tidy.declarations.length} declarations"
      | Err message => message
  | "parse" =>
    match parse source with
      | Ok parsed => "${parsed.declarations.length} declarations"
      | Err message => message
  | "format" =>
    match format source defaultWidth with
      | Formatted text => if text == source then "unchanged" else "changed"
      | ParseError message => message
  | _ => "nothing more"

def none: Comments := Comments.none

def name (text: Text): Expr := Var text none

def plainLine (line: a): Spaced a := { blankBefore = False, line }

def var (text: Text): Expr := Var text none

def binary (operator: Operator) (left right: Expr): Expr := Binary operator none left right

def field (target: Expr) (named: Text): Expr := Field target none named none

def bare (value: Expr): Body := { statements = [plainLine (Bare value)] }

def spare (value: Expr): Expr := Bracketed none value none

--| A group of names sharing one type, with no comments.
def group (names: NonEmptyList Named) (typeName: Text): ParameterGroup := Typed names none (TypeName typeName none)

--| A function with a block, an `if`, operators and calls, and a long list:
--| about 450 characters printed. Sprig++'s constructs are at about the rates
--| of toy-plus-plus.md §6, per copy of 15 lines: typed groups on every
--| function (one of two names, one of one); `takes` on every second function;
--| a spare bracket pair on 4 lines and a trailing comma on 4 lines; and a
--| comment before a closer on every second copy (one in 30 lines).
def sample (index: Nat): List (Spaced Declaration) :=
  let suffix := "${index}"
  let parameters := [
    group { head = { name = "order", comments = none }, tail = [{ name = "items", comments = none }] } "Order",
    group { head = { name = "rates", comments = none }, tail = [] } "Rates"
  ]
  let takes := if index % 2 == 0 then Some none else None
  let endComment: Comments :=
    if index % 2 == 0 then { above = [{ text = "-- end of the names" }], after = None } else none
  let total := Function none "total${suffix}" none takes none parameters True none none {
    statements = [
      plainLine
        (Let none "base" none none (bare (Call (var "sum") none [name "order", spare (name "items")] True none))),
      plainLine
        (Let none "tax" none none
          (bare
            (binary Divide
              (spare (binary Times (var "base") (field (var "rates") "tax")))
              (NumberLiteral "100" none)))),
      {
        blankBefore = True,
        line = Bare
          (If none
            (spare (binary LessThan (field (var "rates") "threshold") (var "base")))
            none
            (bare
              (binary Minus
                (binary Plus (var "base") (var "tax"))
                (spare
                  (Call
                    (var "discount")
                    none
                    [name "order", Var "rates" { above = [], after = Some { text = "-- loyal" } }]
                    True
                    none))))
            none
            (bare (binary Plus (var "base") (var "tax"))))
      }
    ]
  }
  let names := ["alpha", "beta", "gamma", "delta", "epsilon", "zeta", "eta", "theta", "iota", "kappa"].map (word =>
    StringLiteral "\"${word}${suffix}\"" none)
  [
    plainLine (DeclarationNote { text = "-- Totals for one order." }),
    plainLine total,
    { blankBefore = True, line = Value none "names${suffix}" none none (bare (ListLiteral none names True endComment)) }
  ]
