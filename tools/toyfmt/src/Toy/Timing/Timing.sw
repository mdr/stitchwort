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
  let source := file.print defaultWidth
  IO.print "${copies} copies: ${source.length} characters; ${phase}: ${measure phase source}"

def measure (phase source: Text): Text := match phase with
  | "lex" =>
    match lex source with
      | Ok found => "${found.tokens.length} tokens"
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

--| A function with a block, an `if`, operators and calls, and a long list:
--| about 400 characters printed.
def sample (index: Nat): List (Spaced Declaration) :=
  let suffix := "${index}"
  let parameters := ["order", "rates"].map (text => Untyped { name = text, comments = none })
  let total := Function none "total${suffix}" none None none parameters False none none {
    statements = [
      plainLine (Let none "base" none none (bare (Call (var "sum") none [name "order", name "items"] False none))),
      plainLine
        (Let none "tax" none none
          (bare (binary Divide (binary Times (var "base") (field (var "rates") "tax")) (NumberLiteral "100" none)))),
      {
        blankBefore = True,
        line = Bare
          (If none
            (binary LessThan (field (var "rates") "threshold") (var "base"))
            none
            (bare
              (binary Minus
                (binary Plus (var "base") (var "tax"))
                (Call
                  (var "discount")
                  none
                  [name "order", Var "rates" { above = [], after = Some { text = "-- loyal" } }]
                  False
                  none)))
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
    { blankBefore = True, line = Value none "names${suffix}" none none (bare (ListLiteral none names False none)) }
  ]
