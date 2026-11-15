--| Times the toy's phases on a generated Sprig file: `stitchwort run
--| Toy.Timing.main -- PHASE COPIES` lays out COPIES copies of a sample of
--| every construct (about 400 characters each), then, by PHASE, stops
--| (`print`), lexes the printed text (`lex`), parses it (`parse`) or formats
--| it again (`format`), and says how much it made. The toy has no clock, so
--| time it from outside and subtract `print`'s time from the others.

namespace Toy.Timing
import Toy.Fmt (..)
import Toy.Syntax (..)
import Std (Fail, List, Option, Parse, Result, Text)

def main(): {IO} () :=
  let args := IO.args()
  let phase := args.head |> .getOrElse "print"
  let copies := args.drop 1 |> .head |> .flatMap Text.toNat |> .getOrElse 100
  let file: SourceFile := { declarations = List.range 0 copies |> .concatMap sample }
  let source := (file.print defaultWidth).text
  IO.print "${copies} copies: ${source.length} characters; ${phase}: ${measure phase source}"

def measure (phase source: Text): Text := match phase with
  | "lex" =>
    match Fail.toResult (() => Parse.all source (() => lex source)) with
      | Ok tokens => "${tokens.length} tokens"
      | Err message => message
  | "parse" =>
    match parse source with
      | Ok parsed => "${parsed.declarations.length} declarations"
      | Err message => message
  | "format" =>
    match format source defaultWidth with
      | Ok printed => if printed.text == source then "unchanged" else "changed"
      | Err message => message
  | _ => "nothing more"

def name (text: Text): Item := { comments = [], value = Var text, trailing = None }

def plainLine (line: a): Spaced a := { blankBefore = False, line }

--| A function with a block, an `if`, operators and calls, and a long list:
--| about 400 characters printed.
def sample (index: Nat): List (Spaced Declaration) :=
  let suffix := "${index}"
  let total := Function "total${suffix}" ["order", "rates"] {
    statements = [
      plainLine (Let "base" { statements = [plainLine (Bare (Call (Var "sum") [name "order", name "items"]) None)] }),
      plainLine
        (Let "tax" {
          statements = [
            plainLine
              (Bare (Binary Divide (Binary Times (Var "base") (Field (Var "rates") "tax")) (NumberLiteral "100")) None)
          ]
        }),
      {
        blankBefore = True,
        line = Bare
          (If
            (Binary Less (Field (Var "rates") "threshold") (Var "base"))
            {
              statements = [
                plainLine
                  (Bare
                    (Binary Minus
                      (Binary Plus (Var "base") (Var "tax"))
                      (Call (Var "discount") [name "order", name "rates"]))
                    (Some { text = "-- loyal" }))
              ]
            }
            { statements = [plainLine (Bare (Binary Plus (Var "base") (Var "tax")) None)] })
          None
      }
    ]
  }
  let names := ["alpha", "beta", "gamma", "delta", "epsilon", "zeta", "eta", "theta", "iota", "kappa"].map (word =>
    { comments = [], value = StringLiteral "\"${word}${suffix}\"", trailing = None })
  [
    plainLine (DeclarationNote { text = "-- Totals for one order." }),
    plainLine total,
    { blankBefore = True, line = Value "names${suffix}" { statements = [plainLine (Bare (ListLiteral names) None)] } }
  ]
