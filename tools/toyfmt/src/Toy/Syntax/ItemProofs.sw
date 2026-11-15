--| List items and arguments read backwards: `item` on the tokens of a
--| value, with or without its comma, gives the item with the comments the
--| tokens carry. The pieces `ExpressionProofs.sw` builds lists and calls
--| from.

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
    Parse.Runs (() => signInBrackets what wanted) [token] rest True :=
  state starts honest =>
    let core := Parse.runsMap (() => skip()) (skipped => True) [token] rest () (runsSkip token rest)
    match core state starts honest with
      | Witness m (Both ran after) => Witness m (Both (rewrite starts, there in ran) after)

theorem signAbsentRun ∀ (what: Text) (wanted: Punctuation) (state: Parse.State (Parse.Located Token))
    (absent: signAhead wanted state.at.rest = False):
    Parse.runFrom state (() => (signInBrackets what wanted, Parse.mark()))
      = Ok (False, (state.note (Parse.Problem.Expected what)).at) :=
  match state with
    | { at = { rest = [], offset, left }, furthest, expected, messages } => rfl
    | { at = { rest = [token, ..later], offset, left }, furthest, expected, messages } => rewrite absent in rfl

theorem runsSignAbsent ∀ (what: Text) (wanted: Punctuation) (rest: List (Parse.Located Token))
    (absent: signAhead wanted rest = False):
    Parse.Runs (() => signInBrackets what wanted) [] rest False :=
  state starts honest =>
    let same := Parse.noteAt state (Parse.Problem.Expected what)
    let run := signAbsentRun what wanted state (rewrite starts in absent)
    Witness state.at (Both (rewrite same at run in run) (Both starts (Both (rewrite starts at honest in honest) rfl)))

--| The trailing comment on the last of the tokens.
def lastComment (tokens: List (Parse.Located Token)): Option Comment :=
  tokens.last |> .map (token => token.value) |> .flatMap (token => token.trailing) |> .map (comment => comment.value)

--| `lastTrailing start`, from a state that has read `first` and `others`
--| since `start`: the comment on the last of them.
theorem runsLastTrailing ∀ (start: Parse.Mark (Parse.Located Token)) (now: Parse.State (Parse.Located Token))
    (first: Parse.Located Token) (others rest: List (Parse.Located Token))
    (from: start.rest = [first, ..others] ++ rest)
    (moved: now.at.offset = start.offset + others.length + 1):
    Parse.RunsFrom now (() => lastTrailing start) [] rest (lastComment [first, ..others]) :=
  Parse.runsFromMark now
    (finish =>
      Parse.lastRead start finish
        |> .map (token => token.value)
        |> .flatMap (token => token.trailing)
        |> .map (comment => comment.value))
    []
    rest
    (lastComment [first, ..others])
    (rewrite Parse.lastReadAfter start now.at first others rest from moved in Parse.runsPure _ rest now)

--| The trailing comment of an item or bare statement that is `value`, read
--| from `tokens`: none of its own for an `if`, else the comment on its last
--| token (as `trailingSince`).
def trailingFor (value: Expr) (tokens: List (Parse.Located Token)): Option Comment := match value with
  | If _ _ _ => None
  | _ => lastComment tokens

theorem runsTrailingSince ∀ (start: Parse.Mark (Parse.Located Token)) (now: Parse.State (Parse.Located Token))
    (value: Expr) (first: Parse.Located Token) (others rest: List (Parse.Located Token))
    (from: start.rest = [first, ..others] ++ rest)
    (moved: now.at.offset = start.offset + others.length + 1):
    Parse.RunsFrom now (() => trailingSince start value) [] rest (trailingFor value [first, ..others]) :=
  match value with
    | If condition whenTrue whenFalse => Parse.runsPure None rest now
    | Var name => runsLastTrailing start now first others rest from moved
    | NumberLiteral digits => runsLastTrailing start now first others rest from moved
    | StringLiteral written => runsLastTrailing start now first others rest from moved
    | Bracketed inner => runsLastTrailing start now first others rest from moved
    | ListLiteral items => runsLastTrailing start now first others rest from moved
    | Call callee arguments => runsLastTrailing start now first others rest from moved
    | Field target name => runsLastTrailing start now first others rest from moved
    | Negate operand => runsLastTrailing start now first others rest from moved
    | Binary operator left right => runsLastTrailing start now first others rest from moved

--| `item` on a value with no comma after it: the last item of a list.
theorem runsItemLast ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (value: Expr)
    (first: Parse.Located Token) (others rest: List (Parse.Located Token))
    (runsValue: Parse.Runs (() => self InBrackets) [first, ..others] rest value)
    (noComma: signAhead Comma rest = False):
    Parse.Runs (() => item self) [first, ..others] rest (
      { comments = commentsAbove [first, ..others], value, trailing = trailingFor value [first, ..others] },
      False
    ) :=
  state starts honest =>
    let above: commentsAbove state.at.rest = commentsAbove [first, ..others] := rewrite starts in rfl
    Parse.runsFromMark state
      (start =>
        let comments := commentsAbove start.rest
        let value := self InBrackets
        let comma := signInBrackets "','" Comma
        let trailing := if comma then lastTrailing start else trailingSince start value
        ({ comments, value, trailing }, comma))
      [first, ..others]
      rest
      ({ comments = commentsAbove [first, ..others], value, trailing = trailingFor value [first, ..others] }, False)
      (rewrite <- above in
        Parse.runsFromBind state
          (() => self InBrackets)
          (value1 =>
            let comma := signInBrackets "','" Comma
            let trailing := if comma then lastTrailing state.at else trailingSince state.at value1
            ({ comments = commentsAbove state.at.rest, value = value1, trailing }, comma))
          [first, ..others]
          []
          [first, ..others]
          rest
          value
          ({ comments = commentsAbove state.at.rest, value, trailing = trailingFor value [first, ..others] }, False)
          (Eq.sym (List.appendNil [first, ..others]))
          runsValue
          (middle atRest honest1 offset =>
            Parse.runsFromBind middle
              (() => signInBrackets "','" Comma)
              (comma =>
                let trailing := if comma then lastTrailing state.at else trailingSince state.at value
                ({ comments = commentsAbove state.at.rest, value, trailing }, comma))
              []
              []
              []
              rest
              False
              ({ comments = commentsAbove state.at.rest, value, trailing = trailingFor value [first, ..others] }, False)
              rfl
              (runsSignAbsent "','" Comma rest noComma)
              (middle2 atRest2 honest2 offset2 =>
                Parse.runsFromBindAt middle2
                  (() => trailingSince state.at value)
                  (trailing => ({ comments = commentsAbove state.at.rest, value, trailing }, False))
                  []
                  []
                  []
                  rest
                  (trailingFor value [first, ..others])
                  (
                    { comments = commentsAbove state.at.rest, value, trailing = trailingFor value [first, ..others] },
                    False
                  )
                  rfl
                  (runsTrailingSince state.at middle2 value first others rest starts (omega [offset, offset2]))
                  (middle3 atRest3 honest3 offset3 => Parse.runsPure _ rest middle3))))
      starts
      honest

theorem lastCommentAfter ∀ (first comma: Parse.Located Token) (others: List (Parse.Located Token)):
    lastComment [first, ..others ++ [comma]] = lastComment [comma] :=
  let last: ([first, ..others] ++ [comma]).last = Some comma := List.lastSnoc comma [first, ..others]
  rewrite last in rfl

--| `item` on a value and the comma after it: the comma is the item's last
--| token, so a comment after it is the item's.
theorem runsItemComma ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (value: Expr)
    (first comma: Parse.Located Token) (others rest: List (Parse.Located Token))
    (runsValue: Parse.Runs (() => self InBrackets) [first, ..others] [comma, ..rest] value)
    (isComma: comma.value.kind = Sign Comma):
    Parse.Runs (() => item self) ([first, ..others] ++ [comma]) rest (
      { comments = commentsAbove [first, ..others], value, trailing = lastComment [comma] },
      True
    ) :=
  state starts honest =>
    let above: commentsAbove state.at.rest = commentsAbove [first, ..others] := rewrite starts in rfl
    Parse.runsFromMark state
      (start =>
        let comments := commentsAbove start.rest
        let value := self InBrackets
        let comma := signInBrackets "','" Comma
        let trailing := if comma then lastTrailing start else trailingSince start value
        ({ comments, value, trailing }, comma))
      ([first, ..others] ++ [comma])
      rest
      ({ comments = commentsAbove [first, ..others], value, trailing = lastComment [comma] }, True)
      (rewrite <- above in
        Parse.runsFromBind state
          (() => self InBrackets)
          (value1 =>
            let comma := signInBrackets "','" Comma
            let trailing := if comma then lastTrailing state.at else trailingSince state.at value1
            ({ comments = commentsAbove state.at.rest, value = value1, trailing }, comma))
          [first, ..others]
          [comma]
          ([first, ..others] ++ [comma])
          rest
          value
          ({ comments = commentsAbove state.at.rest, value, trailing = lastComment [comma] }, True)
          rfl
          runsValue
          (middle atRest honest1 offset =>
            Parse.runsFromBind middle
              (() => signInBrackets "','" Comma)
              (comma1 =>
                let trailing := if comma1 then lastTrailing state.at else trailingSince state.at value
                ({ comments = commentsAbove state.at.rest, value, trailing }, comma1))
              [comma]
              []
              [comma]
              rest
              True
              ({ comments = commentsAbove state.at.rest, value, trailing = lastComment [comma] }, True)
              rfl
              (runsSignThere "','" Comma comma rest (rewrite isComma in rfl))
              (middle2 atRest2 honest2 offset2 =>
                Parse.runsFromBindAt middle2
                  (() => lastTrailing state.at)
                  (trailing => ({ comments = commentsAbove state.at.rest, value, trailing }, True))
                  []
                  []
                  []
                  rest
                  (lastComment [comma])
                  ({ comments = commentsAbove state.at.rest, value, trailing = lastComment [comma] }, True)
                  rfl
                  (rewrite <- lastCommentAfter first comma others in
                    runsLastTrailing state.at middle2 first
                      (others ++ [comma])
                      rest
                      starts
                      (omega [offset, offset2, List.lengthAppend others [comma]]))
                  (middle3 atRest3 honest3 offset3 => Parse.runsPure _ rest middle3))))
      starts
      honest
