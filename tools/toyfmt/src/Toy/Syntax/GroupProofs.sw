--| A function's parameter groups and their types read backwards: on the
--| tokens of a type, a group or a parameter list, the parser gives it,
--| as `BlockProofs.sw` does for bodies and declarations.

namespace Toy.Syntax.Proofs
import Toy.Syntax (..)
import Std (Bool, Eq, List, Option, Parse, Text, Void)

-- Types.

--| `tokens` spell the type `annotation` inside brackets: its name, or its
--| brackets around tokens that spell what is inside them, each token
--| holding the comments the tree gives it.
def SpelledType (annotation: TypeExpr) (tokens: List (Parse.Located Token)): Prop := match annotation with
  | TypeName text comments =>
    ∃ (token: Parse.Located Token) => tokens = [token]
      ∧ token.value.kind = Name text
      ∧ comments = Layout.comments InBrackets token
  | TypeBracketed open inner close =>
    ∃ (opener: Parse.Located Token) => ∃ (innerTokens: List (Parse.Located Token)) => ∃ (closer: Parse.Located Token) =>
      tokens = [opener, ..innerTokens ++ [closer]]
        ∧ opener.value.kind = Sign OpenParen
        ∧ open = Layout.comments InBrackets opener
        ∧ closer.value.kind = Sign CloseParen
        ∧ close = Layout.comments InBrackets closer
        ∧ SpelledType inner innerTokens

theorem runsTypeName ∀ (self: () → {Parse (Parse.Located Token)} TypeExpr) (token: Parse.Located Token)
    (text: Text) (rest: List (Parse.Located Token))
    (named: token.value.kind = Name text):
    Parse.Runs (() => typeRule self ()) [token] rest (TypeName text (Layout.comments InBrackets token)) :=
  state starts honest =>
    let core :=
      Parse.runsMap
        (() => skip())
        (skipped => TypeName text (Layout.comments InBrackets token))
        [token]
        rest
        ()
        (runsSkip token rest)
    match core state starts honest with | (m, ran, after) => (m, (rewrite starts, named then ran), after)

theorem runsTypeBracketed ∀ (self: () → {Parse (Parse.Located Token)} TypeExpr) (open close: Parse.Located Token)
    (innerTokens rest: List (Parse.Located Token)) (inner: TypeExpr)
    (opens: open.value.kind = Sign OpenParen)
    (closes: close.value.kind = Sign CloseParen)
    (runsInner: Parse.Runs (() => self ()) innerTokens [close, ..rest] inner):
    Parse.Runs
      (() => typeRule self ())
      [open, ..innerTokens ++ [close]]
      rest
      (TypeBracketed
        (Layout.comments InBrackets open)
        inner
        ((Layout.comments InBrackets close).closing inner.endsWithComment)) :=
  state starts honest =>
    let opened := Layout.comments InBrackets open
    let core :=
      Parse.runsBind
        (() => skip())
        (skipped =>
          let inner := self ()
          let close := sign InBrackets "')'" CloseParen
          TypeBracketed opened inner (close.closing inner.endsWithComment))
        [open]
        (innerTokens ++ [close])
        [open, ..innerTokens ++ [close]]
        rest
        ()
        (TypeBracketed opened inner ((Layout.comments InBrackets close).closing inner.endsWithComment))
        byComputing
        (runsSkip open ((innerTokens ++ [close]) ++ rest))
        (Parse.runsBind
          (() => self ())
          (inner =>
            let close := sign InBrackets "')'" CloseParen
            TypeBracketed opened inner (close.closing inner.endsWithComment))
          innerTokens
          [close]
          (innerTokens ++ [close])
          rest
          inner
          (TypeBracketed opened inner ((Layout.comments InBrackets close).closing inner.endsWithComment))
          byComputing
          runsInner
          (Parse.runsMap
            (() => sign InBrackets "')'" CloseParen)
            (closed => TypeBracketed opened inner (closed.closing inner.endsWithComment))
            [close]
            rest
            (Layout.comments InBrackets close)
            (runsSign InBrackets "')'" CloseParen close rest closes byComputing)))
    match core state starts honest with | (m, ran, others) => (m, (rewrite starts, opens then ran), others)

theorem bracketedShorter ∀ (open close: Parse.Located Token) (inner: List (Parse.Located Token)):
    inner.length < [open, ..inner ++ [close]].length :=
  let lengths := List.lengthAppend inner [close]
  arithmetic [lengths]

--| The parser reads back any type from tokens that spell it, whatever
--| follows: a type ends at its name or its `)`. The type's closing
--| brackets hold what rule N leaves on one (`ShapedType`), so the parser
--| keeps their comments as they are.
--|
--| By `Parse.runsRecursiveWith`: a name is one token, and a type in
--| brackets reads the shorter inner type with the nested parser.
theorem runsType ∀ (annotation: TypeExpr) (tokens rest: List (Parse.Located Token))
    (spelled: SpelledType annotation tokens)
    (shaped: ShapedType annotation):
    Parse.Runs (() => typeExpr()) tokens rest annotation :=
  Parse.runsRecursiveWith typeRule
    (unit read after found => SpelledType found read ∧ ShapedType found)
    (self unit read after found both nested =>
      match found, both, unit with
        | TypeName text comments, Both (Witness token (Both split (Both named commented))) _, () =>
          rewrite split, commented then runsTypeName self token text after named
        | TypeBracketed open inner close, Both
            (Witness opener
              (Witness innerTokens
                (Witness closer (Both split (Both opens (Both opened (Both closes (Both closed innerSpelled))))))))
            (Both innerShaped settled), () =>
          let settledClose: settledCloser inner.endsWithComment (Layout.comments InBrackets closer) = True :=
            rewrite <- closed then settled
          let ran :=
            runsTypeBracketed self opener closer innerTokens after inner opens closes
              (nested () innerTokens
                [closer, ..after]
                inner
                ((innerSpelled, innerShaped))
                (rewrite split then bracketedShorter opener closer innerTokens))
          rewrite split, opened, closed then
            (rewrite closingSame (Layout.comments InBrackets closer) inner.endsWithComment settledClose at ran then
              ran))
    ()
    tokens
    rest
    annotation
    ((spelled, shaped))

-- Groups.

def nameAhead (input: List (Parse.Located Token)): Bool := match input with
  | [token, .._] => (nameOf token.value.kind).isSome
  | [] => False

theorem nameNone ∀ (found: Option Text) (none: found.isSome = False): found = None := match found, none with
  | None, none => byComputing

theorem nameDeclines ∀ (input: List (Parse.Located Token))
    (absent: nameAhead input = False):
    Parse.Declines (() => name InBrackets) input :=
  match input, absent with
    | [], absent => Parse.declinesOneEnd "a name" (selectWithComments InBrackets nameOf)
    | [token, ..later], absent =>
      Parse.declinesOne "a name"
        (selectWithComments InBrackets nameOf)
        token
        later
        (rewrite nameNone (nameOf token.value.kind) absent)

theorem colonDeclines ∀ (input: List (Parse.Located Token))
    (absent: signAhead Colon input = False):
    Parse.Declines (() => sign InBrackets "':'" Colon) input :=
  match input, absent with
    | [], absent => Parse.declinesOneEnd "':'" (selectComments InBrackets (signIs Colon))
    | [token, ..later], absent =>
      Parse.declinesOne "':'"
        (selectComments InBrackets (signIs Colon))
        token
        later
        (rewrite noneOfNotSome (signIs Colon token.value.kind) absent)

--| The names of a group after its first, each one token.
def NameSteps: (steps: List (List (Parse.Located Token), (Text, Comments))) → Prop
  | [] => True
  | [(read, found), ..more] =>
    (∃ (token: Parse.Located Token) => ∃ (text: Text) => read = [token]
      ∧ token.value.kind = Name text
      ∧ found = (text, Layout.comments InBrackets token))
      ∧ NameSteps more

theorem nameRounds ∀ (steps: List (List (Parse.Located Token), (Text, Comments))) (rest: List (Parse.Located Token))
    (spelled: NameSteps steps)
    (ends: nameAhead rest = False):
    Parse.ManyRuns (() => name InBrackets) steps rest :=
  match steps, spelled with
    | [], spelled => nameDeclines rest ends
    | [(read, found), ..more], Both (Witness token (Witness text (Both split (Both named valued)))) later => (
      (rewrite split then (same => cases)),
      (rewrite split, valued then runsName InBrackets token text (Parse.joinReads more ++ rest) named byComputing),
      (nameRounds more rest later ends)
    )

--| A group's type: `:` and tokens that spell a type.
theorem runsTyping ∀ (colon: Parse.Located Token) (typeTokens rest: List (Parse.Located Token)) (annotation: TypeExpr)
    (isColon: colon.value.kind = Sign Colon)
    (spelled: SpelledType annotation typeTokens)
    (shaped: ShapedType annotation):
    Parse.Runs
      (() => Parse.optional typing)
      ([colon] ++ typeTokens)
      rest
      (Some (Layout.comments InBrackets colon, annotation)) :=
  let colonComments := Layout.comments InBrackets colon
  Parse.runsOptional typing
    ([colon] ++ typeTokens)
    rest
    (colonComments, annotation)
    (Parse.runsBind
      (() => sign InBrackets "':'" Colon)
      (colon1 =>
        let annotation1 := typeExpr()
        (colon1, annotation1))
      [colon]
      typeTokens
      ([colon] ++ typeTokens)
      rest
      colonComments
      (colonComments, annotation)
      byComputing
      (runsSign InBrackets "':'" Colon colon (typeTokens ++ rest) isColon byComputing)
      (Parse.runsMap
        (() => typeExpr())
        (annotation1 => (colonComments, annotation1))
        typeTokens
        rest
        annotation
        (runsType annotation typeTokens rest spelled shaped)))

--| No type: the next token is not `:`.
theorem runsNoTyping ∀ (rest: List (Parse.Located Token))
    (absent: signAhead Colon rest = False):
    Parse.Runs (() => Parse.optional typing) [] rest None :=
  Parse.declinesRuns typing rest
    (Parse.declinesBind
      (() => sign InBrackets "':'" Colon)
      (colon1 =>
        let annotation1 := typeExpr()
        (colon1, annotation1))
      rest
      (colonDeclines rest absent))

--| A group: its first name, the names after it, and what `typing`
--| reads; then the group `groupOf` makes of them.
theorem runsGroupWith ∀ (first: Parse.Located Token) (text: Text)
    (steps: List (List (Parse.Located Token), (Text, Comments))) (typingTokens rest: List (Parse.Located Token))
    (typed: Option (Comments, TypeExpr)) (group: ParameterGroup)
    (isName: first.value.kind = Name text)
    (spelled: NameSteps steps)
    (ends: nameAhead (typingTokens ++ rest) = False)
    (runsTyping: Parse.Runs (() => Parse.optional typing) typingTokens rest typed)
    (built: Parse.Runs
      (() => groupOf (text, Layout.comments InBrackets first) (Parse.stepValues steps) typed)
      []
      rest
      group):
    Parse.Runs (() => parameterGroup()) ([first] ++ Parse.joinReads steps ++ typingTokens) rest group :=
  let head := (text, Layout.comments InBrackets first)
  Parse.runsBind
    (() => name InBrackets)
    (first1 =>
      let others := Parse.many (() => name InBrackets)
      let typing1 := Parse.optional typing
      groupOf first1 others typing1)
    [first]
    (Parse.joinReads steps ++ typingTokens)
    ([first] ++ Parse.joinReads steps ++ typingTokens)
    rest
    head
    group
    byComputing
    (runsName InBrackets first text ((Parse.joinReads steps ++ typingTokens) ++ rest) isName byComputing)
    (Parse.runsBind
      (() => Parse.many (() => name InBrackets))
      (others =>
        let typing1 := Parse.optional typing
        groupOf head others typing1)
      (Parse.joinReads steps)
      typingTokens
      (Parse.joinReads steps ++ typingTokens)
      rest
      (Parse.stepValues steps)
      group
      byComputing
      (Parse.runsMany
        (() => name InBrackets)
        steps
        (typingTokens ++ rest)
        (nameRounds steps (typingTokens ++ rest) spelled ends))
      (Parse.runsBind
        (() => Parse.optional typing)
        (typing1 => groupOf head (Parse.stepValues steps) typing1)
        typingTokens
        []
        typingTokens
        rest
        typed
        group
        (List.appendNil typingTokens).flipped
        runsTyping
        built))

--| An untyped group: one name, then neither a name nor `:`.
theorem runsUntyped ∀ (first: Parse.Located Token) (text: Text) (rest: List (Parse.Located Token))
    (isName: first.value.kind = Name text)
    (endsNames: nameAhead rest = False)
    (endsGroup: signAhead Colon rest = False):
    Parse.Runs
      (() => parameterGroup())
      [first]
      rest
      (Untyped { name = text, comments = Layout.comments InBrackets first }) :=
  runsGroupWith first text [] [] rest None
    (Untyped { name = text, comments = Layout.comments InBrackets first })
    isName
    byComputing
    endsNames
    (runsNoTyping rest endsGroup)
    (Parse.runsPure (Untyped { name = text, comments = Layout.comments InBrackets first }) rest)

--| A typed group: its names, `:` and tokens that spell its type.
theorem runsTyped ∀ (first colon: Parse.Located Token) (text: Text)
    (steps: List (List (Parse.Located Token), (Text, Comments)))
    (typeTokens rest: List (Parse.Located Token)) (annotation: TypeExpr)
    (isName: first.value.kind = Name text)
    (spelled: NameSteps steps)
    (isColon: colon.value.kind = Sign Colon)
    (typeSpelled: SpelledType annotation typeTokens)
    (typeShaped: ShapedType annotation):
    Parse.Runs
      (() => parameterGroup())
      ([first] ++ Parse.joinReads steps ++ [colon, ..typeTokens])
      rest
      (Typed {
        head = { name = text, comments = Layout.comments InBrackets first },
        tail = (Parse.stepValues steps).map namedOf
      }
        (Layout.comments InBrackets colon)
        annotation) :=
  let group :=
    Typed {
      head = { name = text, comments = Layout.comments InBrackets first },
      tail = (Parse.stepValues steps).map namedOf
    }
      (Layout.comments InBrackets colon)
      annotation
  runsGroupWith first text steps
    ([colon] ++ typeTokens)
    rest
    (Some (Layout.comments InBrackets colon, annotation))
    group
    isName
    spelled
    (rewrite isColon)
    (runsTyping colon typeTokens rest annotation isColon typeSpelled typeShaped)
    (Parse.runsPure group rest)

-- Parameter lists.

--| The rounds of a parameter list after its first group: each a comma
--| and tokens the group parser reads, whatever follows them.
def ParameterSteps: (steps: List (List (Parse.Located Token), ParameterGroup))
      → (rest: List (Parse.Located Token))
      → Prop
  | [], rest => True
  | [(read, found), ..more], rest =>
    (∃ (comma: Parse.Located Token) => ∃ (groupTokens: List (Parse.Located Token)) => read = [comma, ..groupTokens]
      ∧ comma.value.kind = Sign Comma
      ∧ Parse.Runs (() => parameterGroup()) groupTokens (Parse.joinReads more ++ rest) found)
      ∧ ParameterSteps more rest

theorem parameterRounds ∀ (steps: List (List (Parse.Located Token), ParameterGroup)) (rest: List (Parse.Located Token))
    (spelled: ParameterSteps steps rest)
    (ends: signAhead Comma rest = False):
    Parse.ManyRuns parameterStep steps rest :=
  match steps, spelled with
    | [], spelled =>
      Parse.declinesBind (() => sign InBrackets "','" Comma) (comma => parameterGroup()) rest (commaDeclines rest ends)
    | [(read, found), ..more], Both (Witness comma (Witness groupTokens (Both split (Both isComma runsGroup)))) later =>
      (
        (rewrite split then (same => cases)),
        (rewrite split then
          Parse.runsBind
            (() => sign InBrackets "','" Comma)
            (comma1 => parameterGroup())
            [comma]
            groupTokens
            [comma, ..groupTokens]
            (Parse.joinReads more ++ rest)
            (Layout.comments InBrackets comma)
            found
            byComputing
            (runsSign InBrackets "','" Comma comma (groupTokens ++ (Parse.joinReads more ++ rest)) isComma byComputing)
            runsGroup),
        (parameterRounds more rest later ends)
      )

--| A function's parameters: a group, then a comma and a group any number
--| of times, up to a token that is no comma.
theorem runsParameters ∀ (firstTokens: List (Parse.Located Token)) (first: ParameterGroup)
    (steps: List (List (Parse.Located Token), ParameterGroup)) (rest: List (Parse.Located Token))
    (runsFirst: Parse.Runs (() => parameterGroup()) firstTokens (Parse.joinReads steps ++ rest) first)
    (spelled: ParameterSteps steps rest)
    (ends: signAhead Comma rest = False):
    Parse.Runs
      (() => Parse.optional parameterList)
      (firstTokens ++ Parse.joinReads steps)
      rest
      (Some (first, Parse.stepValues steps, False)) :=
  Parse.runsOptional parameterList
    (firstTokens ++ Parse.joinReads steps)
    rest
    (first, Parse.stepValues steps, False)
    (Parse.runsBind
      (() => parameterGroup())
      (first1 =>
        let others := Parse.many parameterStep
        let trailing := signInBrackets "','" Comma
        (first1, others, trailing.isSome))
      firstTokens
      (Parse.joinReads steps)
      (firstTokens ++ Parse.joinReads steps)
      rest
      first
      (first, Parse.stepValues steps, False)
      byComputing
      runsFirst
      (Parse.runsBind
        (() => Parse.many parameterStep)
        (others =>
          let trailing := signInBrackets "','" Comma
          (first, others, trailing.isSome))
        (Parse.joinReads steps)
        []
        (Parse.joinReads steps)
        rest
        (Parse.stepValues steps)
        (first, Parse.stepValues steps, False)
        (List.appendNil (Parse.joinReads steps)).flipped
        (Parse.runsMany parameterStep steps rest (parameterRounds steps rest spelled ends))
        (Parse.runsMap
          (() => signInBrackets "','" Comma)
          (trailing => (first, Parse.stepValues steps, trailing.isSome))
          []
          rest
          None
          (runsSignAbsent "','" Comma rest ends))))

--| No parameters: the next token is not a name.
theorem runsNoParameters ∀ (token: Parse.Located Token) (rest: List (Parse.Located Token))
    (notName: nameOf token.value.kind = None):
    Parse.Runs (() => Parse.optional parameterList) [] [token, ..rest] None :=
  Parse.declinesRuns parameterList
    [token, ..rest]
    (Parse.declinesBind
      (() => parameterGroup())
      (first =>
        let others := Parse.many parameterStep
        let trailing := signInBrackets "','" Comma
        (first, others, trailing.isSome))
      [token, ..rest]
      (Parse.declinesBind
        (() => name InBrackets)
        (first =>
          let others := Parse.many (() => name InBrackets)
          let typing1 := Parse.optional typing
          groupOf first others typing1)
        [token, ..rest]
        (Parse.declinesOne "a name" (selectWithComments InBrackets nameOf) token rest (rewrite notName))))
