--| P4's traversal steps, and their pure form (`Fmt.Walk`'s `Agrees`).
namespace Fmt.MergeProofs
import Fmt (..)
import Fmt.Walk (..)
import Fmt.MeaningProofs (..)
import Std (Bool, Eq, Fail, List, Nat, Option, Result, Text)
import Syntax (..)

-- P4, and the four passes.

def mergeSteps: Steps := { Steps.keep | header = mergeHeader, expr = mergeBinding }

def mergePure: Pure := { Pure.keep | header = mergeHeader, expr = mergeBinding }

def mergeAgrees: Agrees mergeSteps mergePure := {
  expr = (z => byComputing),
  pattern = (z => byComputing),
  header = (z => byComputing),
  decl = (z => byComputing),
  fields = (z => byComputing),
  attributes = (z => byComputing),
  ruleSet = (z => byComputing)
}
