--| Prints a generated Sprig file to time the printer: `stitchwort run
--| Toy.Timing.main -- COPIES` lays out COPIES copies of a sample of every
--| construct and says how many characters it printed. Time it from outside
--| (the toy has no clock).

namespace Toy.Timing
import Toy.Fmt (..)
import Toy.Syntax (..)
import Std (List, Option, Text)

def main(): {IO} () :=
  let copies := IO.args().head |> .flatMap Text.toNat |> .getOrElse 100
  let file: SourceFile := { declarations = List.range 0 copies |> .concatMap sample }
  let printed := file.print defaultWidth
  IO.print "${copies} copies: ${printed.text.length} characters"

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
