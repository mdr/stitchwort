--| Superseded by the real `meaning`, `tools/fmt/src/Fmt/Meaning.sw`
--| (SW-3864, D3678), on the real tree and traversal; this one stays as the
--| sketch's fit check. The real one differs where the real passes do: P3
--| drops pairs along the whole left end of a row's result (into a left
--| operand, a chain's first operand, an application's head, a field
--| access's target), not only around the whole result, and around an
--| annotation's type; so the real `meaning` forgets those, keeps a pair
--| at an application's head unless it holds an atomic form, and keeps a
--| pair around a negative numeral. Groups split as here, and only those
--| P4 merges (no `instance`, no `∃`).
--|
--| What formatting must keep (self-hosted-fmt.md §3.4, D3635, D3643): a
--| file's tree in plain form, each freedom the formatter has set to one
--| spelling. Two files are the same program when their meanings are
--| equal.
--|
--| Nothing proves this definition right: the pass theorems are stated
--| against it, the fuzzer compares the compiler's hashes, and it is meant
--| to be read line by line. So it forgets only what a pass changes, and
--| where a pass changes it; everything else is the traversal with the
--| step that keeps (`traverseKeep`).

namespace Fmt.Sketch
import Std (Bool, List, Option, Text)

--| A plain tree is wrapped so that it can't be printed by mistake: its
--| grouping is in the tree, not in brackets.
type Meaning = { plain: SourceFile }

-- Freedom 1 (P3): a bracket pair after a row or around a parameter's
-- whole type.

--| Without the pairs around it that hold no comment. A pair that holds
--| one stays, with what is inside it as it is.
def Expr.unwrapped: Expr → Expr
  | Pair open inner close => if open.isNone && close.isNone then inner.unwrapped else Pair open inner close
  | other => other

--| A pair is forgotten only in the two places P3 drops one. Anywhere
--| else the compiler may read it (it reads the pair around an
--| application's head), so it stays.
def plainTerm (slot: Slot) (expr: Expr): Expr := match slot with
  | Elsewhere => expr
  | _ => expr.unwrapped

-- Freedom 2 (P4): how adjacent parameters are grouped.

--| The texts of an expression's tokens, in order.
def Expr.words: Expr → List Text
  | Token word => [word.text]
  | Pair _ inner _ => inner.words
  | Commas _ _ lead items _ _ => leadWords lead ++ itemsWords items
  | WithRow row result => row.words ++ result.words
  | Binding _ _ parameters _ body => parametersWords parameters ++ body.words
  | Form _ parts => partsWords parts
  | Local declaration => declaration.words

def leadWords: Option Lead → List Text
  | None => []
  | Some { base, .. } => base.words

def itemsWords: List Expr → List Text
  | [] => []
  | [first, ..rest] => first.words ++ itemsWords rest

def partsWords: List Part → List Text
  | [] => []
  | [Piece word, ..rest] => [word.text, ..partsWords rest]
  | [Sub expr, ..rest] => expr.words ++ partsWords rest
  | [Bound parameter, ..rest] => parameter.words ++ partsWords rest
  | [Line _ line, ..rest] => line.words ++ partsWords rest

def parametersWords: List Parameter → List Text
  | [] => []
  | [first, ..rest] => first.words ++ parametersWords rest

def Parameter.words: Parameter → List Text
  | Group _ _ _ _ names _ annotation default _ =>
    names.map (name => name.text) ++ annotation.words ++ assignedWords default
  | NoParameter _ _ => []
  | Bare name => [name.text]
  | Matched pattern => pattern.words

def assignedWords: Option Assigned → List Text
  | None => []
  | Some { value, .. } => value.words

def Declaration.words: Declaration → List Text
  | Headed _ attributes keywords name _ parameters rest =>
    itemsWords attributes
      ++ keywords.map (word => word.text)
      ++ [name.text]
      ++ parametersWords parameters
      ++ partsWords rest
  | Plain _ parts => partsWords parts

--| Whether the type names one of the group's names: `(x y: P x)` is not
--| `(x: P x) (y: P x)`, whose second type means the first `x`.
def mentions (annotation: Expr) (names: List Word): Bool :=
  names.any (name => annotation.words.any (word => word == name.text))

--| One group for each name, when the group is of the kind P4 makes: no
--| `auto`, no default, no comment on its brackets, names or colon, and a
--| type that names none of them. Any other group is kept whole.
def Parameter.split: Parameter → List Parameter
  | Group kind square open None names colon annotation None close =>
    if open.isNone
      && close.isNone
      && colon.isNone
      && names.all (name => name.comments.isNone)
      && !(mentions annotation names) then
      names.map (name => Group kind square Comments.none None [name] Comments.none annotation None Comments.none)
    else [Group kind square open None names colon annotation None close]
  | other => [other]

def splitGroups: List Parameter → List Parameter
  | [] => []
  | [first, ..rest] => first.split ++ splitGroups rest

-- Freedom 3 (P1): `∀` after a theorem's name.

def isRound: Parameter → Bool
  | Group _ square _ _ _ _ _ _ _ => !square
  | NoParameter _ _ => True
  | _ => False

def isResult: Part → Bool
  | Sub (Form ResultType _) => True
  | _ => False

--| Where P1 writes `∀`: a theorem with a parameter in round brackets and
--| a result type.
def wantsForall (kind: Kind) (parameters: List Parameter) (rest: List Part): Bool := match kind with
  | Theorem => parameters.any isRound && rest.any isResult
  | _ => False

--| `∀` is there wherever P1 would write it, with the comments it had if
--| it was written.
def plainDeclaration: Declaration → Declaration
  | Headed kind attributes keywords name quantifier parameters rest =>
    if wantsForall kind parameters rest then
      Headed kind attributes keywords name (Some (quantifier.getOrElse Comments.none)) parameters rest
    else Headed kind attributes keywords name quantifier parameters rest
  | other => other

-- Freedom 4 (P2): the comma before a closer is forgotten (`comma`
-- below). The other rows of §3.4's table need nothing here: rule N has
-- put each comment on its token before the tree is built, the tree keeps
-- a blank line as a flag, and a `"""` text's lines by value.

def plainSteps: Steps :=
  { term = plainTerm, parameters = splitGroups, comma = (flag => False), declaration = plainDeclaration }

def SourceFile.meaning (file: SourceFile): Meaning := { plain = file.traverse plainSteps }
