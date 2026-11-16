--| List items and arguments read backwards: `item` on the tokens of a
--| value, with or without its comma, gives the item with its comma's
--| comments. The pieces `ExpressionProofs.sw` builds lists and calls from.

namespace Toy.Syntax.Proofs
import Toy.Syntax (..)
import Std (Eq, List, Option, Parse, Text, Void)

--| Whether the sign `wanted` comes next: what `signInBrackets` reads.
def signAhead (wanted: Punctuation) (input: List (Parse.Located Token)): Bool := match input with
  | [token, .._] => (signIs wanted token.value.kind).isSome
  | [] => False

theorem runsSignThere ∀ (what: Text) (wanted: Punctuation)
    (token: Parse.Located Token) (rest: List (Parse.Located Token))
    (there: (signIs wanted token.value.kind).isSome = True):
    Parse.Runs (() => signInBrackets what wanted) [token] rest (Some (Layout.comments InBrackets token)) :=
  state starts honest =>
    let core :=
      Parse.runsMap
        (() => skip())
        (skipped => Some (Layout.comments InBrackets token))
        [token]
        rest
        ()
        (runsSkip token rest)
    match core state starts honest with | (m, ran, after) => (m, (rewrite starts, there then ran), after)

theorem signAbsentRun ∀ (what: Text) (wanted: Punctuation) (state: Parse.State (Parse.Located Token))
    (absent: signAhead wanted state.at.rest = False):
    Parse.runFrom state (() => (signInBrackets what wanted, Parse.mark()))
      = Ok (None, (state.note (Parse.Problem.Expected what)).at) :=
  match state with
    | { at = { rest = [], offset, left }, furthest, expected, messages } => byComputing
    | { at = { rest = [token, ..later], offset, left }, furthest, expected, messages } => rewrite absent

theorem runsSignAbsent ∀ (what: Text) (wanted: Punctuation) (rest: List (Parse.Located Token))
    (absent: signAhead wanted rest = False):
    Parse.Runs (() => signInBrackets what wanted) [] rest None :=
  state starts honest =>
    let same := Parse.noteAt state (Parse.Problem.Expected what)
    let run := signAbsentRun what wanted state (rewrite starts then absent)
    (state.at, (rewrite same at run then run), starts, (rewrite starts at honest then honest), byComputing)

--| `item` on a value with no comma after it: the last item of a list.
theorem runsItemLast ∀ (self: Layout → {Parse (Parse.Located Token)} Expr)
    (value: Expr) (tokens rest: List (Parse.Located Token))
    (runsValue: Parse.Runs (() => self InBrackets) tokens rest value)
    (noComma: signAhead Comma rest = False):
    Parse.Runs (() => item self) tokens rest ({ value, comma = Comments.none }, False) :=
  Parse.runsBind
    (() => self InBrackets)
    (value1 =>
      let comma := signInBrackets "','" Comma
      ({ value = value1, comma = comma.getOrElse Comments.none }, comma.isSome))
    tokens
    []
    tokens
    rest
    value
    ({ value, comma = Comments.none }, False)
    (List.appendNil tokens).flipped
    runsValue
    (Parse.runsMap
      (() => signInBrackets "','" Comma)
      (comma => ({ value, comma = comma.getOrElse Comments.none }, comma.isSome))
      []
      rest
      None
      (runsSignAbsent "','" Comma rest noComma))

--| `item` on a value and the comma after it: the item holds the comma's
--| comments.
theorem runsItemComma ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (value: Expr)
    (comma: Parse.Located Token) (tokens rest: List (Parse.Located Token))
    (runsValue: Parse.Runs (() => self InBrackets) tokens [comma, ..rest] value)
    (isComma: comma.value.kind = Sign Comma):
    Parse.Runs (() => item self) (tokens ++ [comma]) rest ({ value, comma = Layout.comments InBrackets comma }, True) :=
  Parse.runsBind
    (() => self InBrackets)
    (value1 =>
      let found := signInBrackets "','" Comma
      ({ value = value1, comma = found.getOrElse Comments.none }, found.isSome))
    tokens
    [comma]
    (tokens ++ [comma])
    rest
    value
    ({ value, comma = Layout.comments InBrackets comma }, True)
    byComputing
    runsValue
    (Parse.runsMap
      (() => signInBrackets "','" Comma)
      (found => ({ value, comma = found.getOrElse Comments.none }, found.isSome))
      [comma]
      rest
      (Some (Layout.comments InBrackets comma))
      (runsSignThere "','" Comma comma rest (rewrite isComma)))
