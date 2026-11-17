--| The one traversal `meaning` and all four passes share (Toy++ T5's
--| `Fmt/Traverse.sw`, at the real size). It rewrites bottom-up: what is
--| inside a node first, then the steps at the node.

namespace Fmt.Sketch
import Std (Bool, List, Option, Text)

--| Where an expression stands, as far as a pass needs to know: the two
--| places P3 drops a bracket pair, or anywhere else.
type Slot =
  --| The type after a row: `{Fail} (List Nat)`.
  | AfterRow
  --| The whole type of a parameter: `(h: (∀ …))`.
  | WholeType
  | Elsewhere

--| What a pass does at a node. A pass sets one field and leaves the
--| others at `Steps.keep`'s.
type Steps = {
  term: Slot → Expr → Expr,
  parameters: List Parameter → List Parameter,
  comma: Bool → Bool,
  declaration: Declaration → Declaration
}

def Steps.keep: Steps :=
  { term = (slot expr => expr), parameters = (found => found), comma = (flag => flag), declaration = (found => found) }

def Expr.traverse (expr: Expr) (steps: Steps) (slot: Slot): Expr := (steps.term) slot (expr.traverseInside steps)

def Expr.traverseInside (expr: Expr) (steps: Steps): Expr := match expr with
  | Token word => Token word
  | Pair open inner close => Pair open (inner.traverse steps Elsewhere) close
  | Commas kind open lead items trailingComma close =>
    Commas kind open (traverseLead steps lead) (traverseItems steps items) ((steps.comma) trailingComma) close
  | WithRow row result => WithRow (row.traverse steps Elsewhere) (result.traverse steps AfterRow)
  | Binding kind keyword parameters arrow body =>
    Binding kind keyword
      ((steps.parameters) (traverseParameters steps parameters))
      arrow
      (body.traverse steps Elsewhere)
  | Form kind parts => Form kind (traverseParts steps parts)
  | Local declaration => Local (declaration.traverse steps)

def traverseLead (steps: Steps): Option Lead → Option Lead
  | None => None
  | Some { base, bar } => Some { base = base.traverse steps Elsewhere, bar }

def traverseItems (steps: Steps): List Expr → List Expr
  | [] => []
  | [first, ..rest] => [first.traverse steps Elsewhere, ..traverseItems steps rest]

def traverseParts (steps: Steps): List Part → List Part
  | [] => []
  | [first, ..rest] => [first.traverse steps, ..traverseParts steps rest]

def Part.traverse (part: Part) (steps: Steps): Part := match part with
  | Piece word => Piece word
  | Sub expr => Sub (expr.traverse steps Elsewhere)
  | Bound parameter => Bound (parameter.traverse steps)
  | Line blankBefore line => Line blankBefore (line.traverse steps Elsewhere)

def traverseParameters (steps: Steps): List Parameter → List Parameter
  | [] => []
  | [first, ..rest] => [first.traverse steps, ..traverseParameters steps rest]

def Parameter.traverse (parameter: Parameter) (steps: Steps): Parameter := match parameter with
  | Group kind square open auto names colon annotation default close =>
    Group kind square open auto names colon (annotation.traverse steps WholeType) (traverseAssigned steps default) close
  | Matched pattern => Matched (pattern.traverse steps Elsewhere)
  | other => other

def traverseAssigned (steps: Steps): Option Assigned → Option Assigned
  | None => None
  | Some { assign, value } => Some { assign, value = value.traverse steps Elsewhere }

def Declaration.traverse (declaration: Declaration) (steps: Steps): Declaration := match declaration with
  | Headed kind attributes keywords name quantifier parameters rest =>
    (steps.declaration)
      (Headed kind
        (traverseItems steps attributes)
        keywords
        name
        quantifier
        ((steps.parameters) (traverseParameters steps parameters))
        (traverseParts steps rest))
  | Plain kind parts => (steps.declaration) (Plain kind (traverseParts steps parts))

def traverseDeclarations (steps: Steps): List Spaced → List Spaced
  | [] => []
  | [{ blankBefore, declaration }, ..rest] =>
    [{ blankBefore, declaration = declaration.traverse steps }, ..traverseDeclarations steps rest]

def SourceFile.traverse (file: SourceFile) (steps: Steps): SourceFile :=
  { declarations = traverseDeclarations steps file.declarations, end = file.end }
