--| The lowering's three checks on what parsed (`crates/syntax/src/lower`),
--| as functions of the tree that `parseFile` calls on each declaration
--| once it has parsed: an or-pattern with a name bound in some
--| alternatives but not all (`E-OR-PATTERN-BINDS`), a header's parameter named twice
--| (`E-DUPLICATE-PARAMETER`), and an arm with `()`, a condition and no
--| body. The first two are checked by the traversal's steps, which fail at
--| the first node they refuse.

namespace Syntax
import Std (Bool, Fail, List, Option, Result, Text)

--| `E-OR-PATTERN-BINDS`'s message, as the Rust lowering's `unshared_name` words it.
def unsharedMessage (name binding lacking: Text): Text := "`${name}` is bound in `${binding}` but not in `${lacking}`"

--| Whether `message` is `unsharedMessage`'s.
def isUnsharedMessage (message: Text): Bool :=
  message.startsWith "`" && message.contains "` is bound in `" && message.contains "` but not in `"

def guardWithoutBody: Text := "an arm with `()` and no body can't have a condition"

--| The first of the lowering's errors in a declaration, if any.
def Decl.loweringError (decl: Decl): Option Text := match decl with
  | Definition _ header _ =>
    match duplicateParameter header with
      | Some message => Some message
      | None => traversalError decl
  | _ => traversalError decl

--| The first of the lowering's errors in an expression read on its own.
def Expr.loweringError (expr: Expr): Option Text := match Fail.toResult (() => expr.traverse checkSteps) with
  | Err message => Some message
  | Ok _ => None

def traversalError (decl: Decl): Option Text := match Fail.toResult (() => decl.traverse checkSteps) with
  | Err message => Some message
  | Ok _ => None

--| The lowering's checks as traversal steps.
def checkSteps: Steps := { Steps.keep | expr = checkExpr, pattern = checkPattern }

def checkPattern (pattern: Pattern): {Fail} Pattern := match pattern with
  | PatternOr first rest =>
    match unsharedName [first.boundNames, ..linkNames rest] with
      | Some { name, binding, lacking } =>
        Fail.fail (unsharedMessage name (alternativeShown first rest binding) (alternativeShown first rest lacking))
      | None => pattern
  | _ => pattern

--| The names each alternative after an or-pattern's first binds.
def linkNames: List (Word, Pattern) → List (List Text)
  | [] => []
  | [(bar, item), ..rest] => [item.boundNames, ..linkNames rest]

--| An or-pattern's alternative by its position, shown as in the message. Only shown for the message: showing every
--| alternative of every or-pattern would take time quadratic in their nesting.
def alternativeShown (first: Pattern) (rest: List (Word, Pattern)) (position: Nat): Text := match position with
  | Zero => first.shown
  | Succ after => linkShownAt after rest

def linkShownAt (position: Nat) (links: List (Word, Pattern)): Text := match links, position with
  | [], _ => ""
  | [(bar, item), .._], Zero => item.shown
  | [_, ..rest], Succ after => linkShownAt after rest

--| A name that one alternative of an or-pattern binds and another doesn't, with their positions.
type Unshared = { name: Text, binding: Nat, lacking: Nat }

--| The first name, taking the alternatives and then their names in order, that some alternative doesn't bind, with
--| the first such alternative: the arm's body is checked once per alternative, so each must bind every name the body
--| may use (D3694).
def unsharedName (alternatives: List (List Text)): Option Unshared := firstUnshared alternatives 0 alternatives

def firstUnshared (all: List (List Text)) (position: Nat): List (List Text) → Option Unshared
  | [] => None
  | [names, ..rest] =>
    match firstMissing all position names with
      | Some unshared => Some unshared
      | None => firstUnshared all (position + 1) rest

def firstMissing (all: List (List Text)) (position: Nat): List Text → Option Unshared
  | [] => None
  | [name, ..more] =>
    match all.findIndex (bound => !bound.contains name) with
      | Some lacking => Some { name, binding = position, lacking }
      | None => firstMissing all position more

def checkExpr (expr: Expr): {Fail} Expr := match expr with
  | Block first rest _ =>
    match localDuplicate [first, ..rest] with
      | Some message => Fail.fail message
      | None => expr
  | Match _ _ _ arms => if anyGuardWithoutBody arms then Fail.fail guardWithoutBody else expr
  | ClauseLambda keyword _ arms =>
    if keyword.text != "matches" && anyGuardWithoutBody arms then Fail.fail guardWithoutBody else expr
  | _ => expr

--| A local definition's parameter named twice. Checked once the block's
--| lines are traversed, so an error inside a local definition's body comes
--| first; the Rust lowering checks the header first (a file with both is
--| rare).
def localDuplicate: List Statement → Option Text
  | [] => None
  | [LocalDef _ header _, ..rest] =>
    match duplicateParameter header with
      | Some message => Some message
      | None => localDuplicate rest
  | [_, ..rest] => localDuplicate rest

def anyGuardWithoutBody: List Arm → Bool
  | [] => False
  | [{ bar, patterns, guard = Some _, body = None }, .._] => True
  | [_, ..rest] => anyGuardWithoutBody rest

--| `E-DUPLICATE-PARAMETER`: the header's parameters, and the implicit and
--| `auto` ones on the result type's spine, all have different names
--| (`check_duplicates`). The spine's own names may repeat each other, as
--| the Rust check only compares them with the header's.
def duplicateParameter (header: Header): Option Text :=
  let named := groupNames header.params
  match repeatedIn [] named with
    | Some name => Some (alreadyParameter name header.name)
    | None =>
      match spineRepeat named header.result with
        | Some name => Some (alreadyParameter name header.name)
        | None => None

def alreadyParameter (name: Text) (definition: Word): Text := "`${name}` is already a parameter of `${definition.text}`"

def groupNames: List Group → List Text
  | [] => []
  | [group, ..rest] => group.names.map (name => name.text) ++ groupNames rest

--| The first name that repeats one before it.
def repeatedIn (seen: List Text): List Text → Option Text
  | [] => None
  | [name, ..rest] => if seen.contains name then Some name else repeatedIn [name, ..seen] rest

--| The first implicit binder's name on `type`'s spine that is a header's
--| parameter.
def spineRepeat (header: List Text): Expr → Option Text
  | FunctionType binder _ result =>
    let clash :=
      if binder.implicit then binder.names.map (name => name.text) |> .find (name => header.contains name) else None
    match clash with
      | Some name => Some name
      | None => spineRepeat header result
  | Infix InfixArrow _ _ result => spineRepeat header result
  | _ => None

--| The names a pattern binds, left to right: its lowercase names and punned fields. An or-pattern binds its first
--| alternative's names, as the Rust lowering's `bound_names` does, since `unsharedName` checks that the others bind
--| the same.
def Pattern.boundNames: Pattern → List Text
  | PatternWord kind word => if kind == Lower && word.text != "Quot.mk" then [word.text] else []
  | PatternCtor _ arguments => namesOf arguments
  | PatternCtorFields _ fields | PatternRecord fields => fieldsNames fields
  | PatternTuple _ items _ _ => namesOf items
  | PatternList _ items _ tail _ => namesOf items ++ tailNames tail
  | PatternNamed _ _ _ value _ | PatternOr value _ | PatternParen _ value _ => value.boundNames
  | PatternNegative _ _ | PatternAbsurd _ _ => []
  | PatternAppend start _ rest => start.boundNames ++ rest.boundNames

def namesOf: List Pattern → List Text
  | [] => []
  | [first, ..rest] => first.boundNames ++ namesOf rest

def tailNames: Option (Word, Pattern) → List Text
  | Some (_, rest) => rest.boundNames
  | None => []

def fieldsNames: FieldsPattern → List Text
  | { open, fields, trailingComma, rest, close } => fieldNames fields

def fieldNames: List FieldPattern → List Text
  | [] => []
  | [{ name, value = Some (_, pattern) }, ..rest] => pattern.boundNames ++ fieldNames rest
  | [{ name, value = None }, ..rest] => [name.text, ..fieldNames rest]

--| A pattern as the formatter writes it: what the Rust message quotes from the source, for a formatted file.
def Pattern.shown: Pattern → Text
  | PatternWord _ word => word.text
  | PatternCtor name arguments => name.text ++ spacedShown arguments
  | PatternCtorFields name fields => "${name.text} ${fieldsShown fields}"
  | PatternRecord fields => fieldsShown fields
  | PatternTuple open items trailingComma close => open.text ++ commaShown items ++ commaIf trailingComma ++ close.text
  | PatternList open items trailingComma tail close =>
    open.text ++ commaShown items ++ commaIf trailingComma ++ tailShown (commaShown items == "") tail ++ close.text
  | PatternNamed open name colonEq value close => "${open.text}${name.text} ${colonEq.text} ${value.shown}${close.text}"
  | PatternOr first rest => first.shown ++ linksShown rest
  | PatternParen open inner close => open.text ++ inner.shown ++ close.text
  | PatternNegative minus number | PatternAbsurd minus number => minus.text ++ number.text
  | PatternAppend start operator rest => "${start.shown} ${operator.text} ${rest.shown}"

def commaIf (comma: Bool): Text := if comma then "," else ""

--| ` p` for each pattern.
def spacedShown: List Pattern → Text
  | [] => ""
  | [first, ..rest] => " " ++ first.shown ++ spacedShown rest

--| The patterns with `, ` between them.
def commaShown: List Pattern → Text
  | [] => ""
  | [first, ..rest] => first.shown ++ commasShown rest

def commasShown: List Pattern → Text
  | [] => ""
  | [first, ..rest] => ", " ++ first.shown ++ commasShown rest

--| A list pattern's `..rest`, after `, ` unless it comes first.
def tailShown (first: Bool): Option (Word, Pattern) → Text
  | Some (dots, rest) => (if first then "" else ", ") ++ dots.text ++ rest.shown
  | None => ""

def linksShown: List (Word, Pattern) → Text
  | [] => ""
  | [(bar, item), ..rest] => " ${bar.text} ${item.shown}" ++ linksShown rest

--| `{ a, b = p, .. }`, or `{}`.
def fieldsShown: FieldsPattern → Text
  | { open, fields, rest, close, .. } =>
    bracesAround open.text (fieldListShown fields ++ restShown (fieldListShown fields == "") rest) close.text

def bracesAround (open inside close: Text): Text := if inside == "" then open ++ close else "${open} ${inside} ${close}"

def fieldListShown: List FieldPattern → Text
  | [] => ""
  | [first, ..rest] => first.shown ++ fieldsAfterShown rest

def fieldsAfterShown: List FieldPattern → Text
  | [] => ""
  | [first, ..rest] => ", " ++ first.shown ++ fieldsAfterShown rest

def FieldPattern.shown: FieldPattern → Text
  | { name, value = Some (equals, pattern) } => "${name.text} ${equals.text} ${pattern.shown}"
  | { name, value = None } => name.text

def restShown (first: Bool): Option Word → Text
  | Some dots => (if first then "" else ", ") ++ dots.text
  | None => ""
