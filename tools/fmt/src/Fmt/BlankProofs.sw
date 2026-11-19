--| The blanking steps as a pure function agree with their traversal steps (`Fmt.Walk`'s `Agrees`).
namespace Fmt.Proofs
import Fmt (..)
import Fmt.Walk (..)
import Std (Bool, Eq, Fail, List, Nat, Option, Result, Text)
import Syntax (..)

-- Declarations.

def blankPure: Pure := {
  expr = blankExpr,
  pattern = blankPattern,
  header = blankHeader,
  decl = blankDecl,
  fields = blankFields,
  attributes = blankAttributes,
  ruleSet = blankRuleSet
}

def blankAgrees: Agrees blankSteps blankPure := {
  expr = (z => byComputing),
  pattern = (z => byComputing),
  header = (z => byComputing),
  decl = (z => byComputing),
  fields = (z => byComputing),
  attributes = (z => byComputing),
  ruleSet = (z => byComputing)
}
