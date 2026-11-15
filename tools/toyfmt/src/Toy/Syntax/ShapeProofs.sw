--| What the parser guarantees about its trees: every expression it gives
--| is of the shape `Shaped` describes (operators grouped by precedence, a
--| call's callee and a field's target postfix, `-` before an operand), so
--| the read-back theorems' `Shaped` hypothesis holds of every parsed tree
--| and needn't be checked; and every body ends in a statement, every
--| function's last parameter has no comma. Built from std's soundness lemmas
--| (`Parse.Reads`), `Parse.readsOperators` for the operator chains.

namespace Toy.Syntax.Proofs
import Toy.Syntax (..)
import Std.Parse.Associativity (LeftAssociative)
import Std (Bool, Eq, List, NonEmptyList, Option, Parse, Result, Text, Void)

--| Whenever `parser` succeeds, `holds` of its value (and it read a start
--| of the input, as every `Parse.Reads` says).
def Gives (parser: () → {Parse (Parse.Located Token)} a) (holds: a → Prop): Prop :=
  Parse.Reads parser (taken value => holds value)

theorem givesDone ∀ (x: a) (holds: a → Prop) (proved: holds x): Gives (() => x) holds := Parse.readsDone x _ proved

--| `p`, then `j` of its value.
theorem givesThen ∀ (p: () → {Parse (Parse.Located Token)} a) (j: a → {Parse (Parse.Located Token)} b)
    (first: a → Prop) (holds: b → Prop)
    (givesFirst: Gives p first)
    (rest: ∀ (v: a) => first v → Gives (() => j v) holds):
    Gives (() => j (p())) holds :=
  Parse.readsThenOf p j _ _ givesFirst (firstRead v facts => rest v facts)

theorem givesWeaken ∀ (p: () → {Parse (Parse.Located Token)} a) (holds weaker: a → Prop)
    (gives: Gives p holds) (implies: ∀ (value: a) => holds value → weaker value):
    Gives p weaker :=
  Parse.readsWeaken gives (taken value proved => implies value proved)

theorem givesSkip: Gives (() => skip()) (skipped => True) :=
  Parse.readsThenOf
    (() => Parse.next (token => True))
    (skipped => ()) _ _
    (Parse.readsNext (token => True))
    (firstRead skipped facts => Parse.readsDone () _ rfl)

--| A note, then a value.
theorem givesNoted ∀ (problem: Parse.Problem) (x: a) (holds: a → Prop) (proved: holds x):
    Gives
      (() =>
        Parse.note problem
        x)
      holds :=
  Parse.readsThenOf (() => Parse.note problem) (noted => x) _ _ (Parse.readsNote problem) (firstRead noted none =>
    Parse.readsDone x _ proved)

theorem givesSign ∀ (layout: Layout) (what: Text) (wanted: Punctuation):
    Gives (() => sign layout what wanted) (comments => True) :=
  Parse.readsWeaken (Parse.readsOne what (selectComments layout (signIs wanted))) (taken value found => rfl)

theorem givesKeyword ∀ (layout: Layout) (wanted: Keyword): Gives (() => keyword layout wanted) (comments => True) :=
  Parse.readsWeaken
    (Parse.readsOne "'${wanted.spelling}'" (selectComments layout (keywordIs wanted)))
    (taken value found => rfl)

theorem givesName ∀ (layout: Layout): Gives (() => name layout) (named => True) :=
  Parse.readsWeaken (Parse.readsOne "a name" (selectWithComments layout nameOf)) (taken value found => rfl)

theorem givesSignInBrackets ∀ (what: Text) (wanted: Punctuation):
    Gives (() => signInBrackets what wanted) (found => True) :=
  state value after honest h =>
    match e: state.at.rest with
      | [] => givesNoted (Parse.Problem.Expected what) None (found => True) rfl state value after honest h
      | [token, ..later] =>
        match isSign: (signIs wanted token.value.kind).isSome with
          | False => givesNoted (Parse.Problem.Expected what) None (found => True) rfl state value after honest h
          | True =>
            givesThen
              (() => skip())
              (skipped => Some (Layout.comments InBrackets token))
              (skipped => True)
              (found => True)
              givesSkip
              (skipped holds => givesDone _ _ rfl)
              state
              value
              after
              honest
              h

theorem givesMark: Gives (() => Parse.mark()) ((at: Parse.Mark (Parse.Located Token)) => True) :=
  Parse.readsWeaken Parse.readsMark (taken at none => rfl)

theorem givesExpected ∀ (what: Text) (holds: a → Prop): Gives (() => (Parse.expected what: a)) holds :=
  Parse.readsExpected what

--| What holds of an optional value: `holds`, if there is one.
def Perhaps (holds: a → Prop): Option a → Prop
  | None => True
  | Some value => holds value

theorem givesOptional ∀ (p: () → {Parse (Parse.Located Token)} a) (holds: a → Prop)
    (gives: Gives p holds):
    Gives (() => Parse.optional p) (Perhaps holds) :=
  Parse.readsWeaken (Parse.readsOptional gives) (taken value maybe =>
    match value, maybe with
      | Some found, proved => proved
      | None, none => rfl)

-- Items.

theorem shapedItemsAppend ∀ (front: List Item) (last: Item)
    (shaped: ShapedItems front)
    (lastShaped: Shaped last.value):
    ShapedItems (front ++ [last]) :=
  match front, shaped, last, lastShaped with
    | [], shaped, { value, comma }, lastShaped => Both lastShaped rfl
    | [{ value, comma }, ..rest], Both valueShaped restShaped, last, lastShaped =>
      Both valueShaped (shapedItemsAppend rest last restShaped lastShaped)

theorem shapedItemsReverse ∀ (found: List Item) (shaped: ShapedItems found): ShapedItems found.reverse :=
  match found, shaped with
    | [], shaped => rfl
    | [{ value, comma }, ..rest], Both valueShaped restShaped =>
      rewrite List.reverseCons ({ value, comma }: Item) rest in
        shapedItemsAppend rest.reverse { value, comma } (shapedItemsReverse rest restShaped) valueShaped

theorem bareLastAppend ∀ (front: List Item) (last: Item)
    (bare: last.comma = Comments.none):
    BareLastItem (front ++ [last]) :=
  match front, last, bare with
    | [], { value, comma }, bare => bare
    | [first], { value, comma }, bare => bare
    | [first, second, ..rest], last, bare => bareLastAppend [second, ..rest] last bare

--| The items found, newest first, in order: the last is the newest.
theorem bareLastReverse ∀ (found: List Item) (newest: Item)
    (bare: newest.comma = Comments.none):
    BareLastItem [newest, ..found].reverse :=
  rewrite List.reverseCons newest found in bareLastAppend found.reverse newest bare

--| An item of the parser's shape, with no comma's comments unless a comma
--| followed it.
def ShapedItem (read: (Item, Bool)): Prop := Shaped read.fst.value ∧ (read.snd = False → read.fst.comma = Comments.none)

theorem givesItem ∀ (self: Layout → {Parse (Parse.Located Token)} Expr)
    (nested: ∀ (inner: Layout) => Gives (() => self inner) Shaped):
    Gives (() => item self) ShapedItem :=
  givesThen
    (() => self InBrackets)
    (value =>
      let comma := signInBrackets "','" Comma
      ({ value, comma = comma.getOrElse Comments.none }, comma.isSome))
    Shaped
    ShapedItem
    (nested InBrackets)
    (value shaped =>
      givesThen
        (() => signInBrackets "','" Comma)
        (comma => ({ value, comma = comma.getOrElse Comments.none }, comma.isSome))
        (comma => True)
        ShapedItem
        (givesSignInBrackets "','" Comma)
        (comma found =>
          match comma with
            | Some comments => givesDone _ ShapedItem (Both shaped (never => Void.exfalso (Bool.trueNotFalse never)))
            | None => givesDone _ ShapedItem (Both shaped (none => rfl))))

--| Items of the parser's shape, the last with no comma's comments.
def ShapedList (items: List Item): Prop := ShapedItems items ∧ BareLastItem items

theorem givesItemsFrom ∀ (self: Layout → {Parse (Parse.Located Token)} Expr)
    (nested: ∀ (inner: Layout) => Gives (() => self inner) Shaped)
    (fuel: Nat) (found: List Item)
    (shaped: ShapedItems found):
    Gives (() => itemsFrom fuel self found) ShapedList :=
  match fuel with
    | Zero => givesDone [] ShapedList (Both rfl rfl)
    | Succ more =>
      givesThen
        (() => item self)
        (itemsAfter more self found)
        ShapedItem
        ShapedList
        (givesItem self nested)
        (read itemShaped =>
          match read, itemShaped with
            | ({ value, comma }, True), Both valueShaped bare =>
              givesItemsFrom self nested more [{ value, comma }, ..found] (Both valueShaped shaped)
            | ({ value, comma }, False), Both valueShaped bare =>
              givesDone _ ShapedList
                (Both
                  (shapedItemsReverse [{ value, comma }, ..found] (Both valueShaped shaped))
                  (bareLastReverse found { value, comma } (bare rfl))))

--| `items` gives items whose values are of the parser's shape, the last
--| with no comma's comments, when the nested parser does.
theorem givesItems ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (closer: Punctuation)
    (nested: ∀ (inner: Layout) => Gives (() => self inner) Shaped):
    Gives (() => items self closer) (found => ShapedList found.fst) :=
  Parse.readsThen (givesSignInBrackets "'${closer.spelling}'" closer) (firstRead closed facts =>
    match closed with
      | Some close => Parse.readsDone ([], close) _ (Both rfl rfl)
      | None =>
        givesThen
          (() => Parse.mark())
          (at =>
            let found := itemsFrom at.left self []
            let close := sign InBrackets "'${closer.spelling}'" closer
            (found, close))
          (at => True)
          (found => ShapedList found.fst)
          givesMark
          (at marked =>
            givesThen
              (() => itemsFrom at.left self [])
              (found =>
                let close := sign InBrackets "'${closer.spelling}'" closer
                (found, close))
              ShapedList
              (found => ShapedList found.fst)
              (givesItemsFrom self nested at.left [] rfl)
              (found shaped =>
                givesThen
                  (() => sign InBrackets "'${closer.spelling}'" closer)
                  (close => (found, close))
                  (close => True)
                  (found => ShapedList found.fst)
                  (givesSign InBrackets "'${closer.spelling}'" closer)
                  (close signed => givesDone _ _ shaped))))

-- Atoms and their calls and fields.

--| A postfix expression of the parser's shape: what `atom` and
--| `suffixesFrom` give.
def PostfixShaped (expr: Expr): Prop := expr.isPostfix = True ∧ Shaped expr

--| An operand of the parser's shape: what `operand` gives.
def OperandShaped (expr: Expr): Prop := expr.isOperand = True ∧ Shaped expr

theorem postfixIsOperand ∀ (expr: Expr) (postfix: expr.isPostfix = True): expr.isOperand = True := cases

theorem operandIsChain ∀ (expr: Expr) (operand: expr.isOperand = True): expr.isChain = True := cases

theorem operandLevel ∀ (expr: Expr) (isOperand: expr.isOperand = True): expr.chainLevel = 7 :=
  match expr, isOperand with
    | Var _ _, _ => rfl
    | NumberLiteral _ _, _ => rfl
    | StringLiteral _ _, _ => rfl
    | Bracketed _ _ _, _ => rfl
    | ListLiteral _ _ _, _ => rfl
    | Call _ _ _ _, _ => rfl
    | Field _ _ _ _, _ => rfl
    | Negate _ _, _ => rfl

theorem givesAtomOf ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (comments: Comments) (kind: Kind)
    (nested: ∀ (inner: Layout) => Gives (() => self inner) Shaped):
    Gives (() => atomOf self comments kind) PostfixShaped :=
  match kind with
    | Name text =>
      givesThen (() => skip()) (skipped => Var text comments) (skipped => True) PostfixShaped givesSkip (skipped done =>
        givesDone _ PostfixShaped (Both rfl rfl))
    | Number digits =>
      givesThen
        (() => skip())
        (skipped => NumberLiteral digits comments)
        (skipped => True)
        PostfixShaped
        givesSkip
        (skipped done => givesDone _ PostfixShaped (Both rfl rfl))
    | Str written =>
      givesThen
        (() => skip())
        (skipped => StringLiteral written comments)
        (skipped => True)
        PostfixShaped
        givesSkip
        (skipped done => givesDone _ PostfixShaped (Both rfl rfl))
    | Sign OpenParen =>
      givesThen
        (() => skip())
        (skipped =>
          let inner := self InBrackets
          let close := sign InBrackets "')'" CloseParen
          Bracketed comments inner close)
        (skipped => True)
        PostfixShaped
        givesSkip
        (skipped done =>
          givesThen
            (() => self InBrackets)
            (inner =>
              let close := sign InBrackets "')'" CloseParen
              Bracketed comments inner close)
            Shaped
            PostfixShaped
            (nested InBrackets)
            (inner shaped =>
              givesThen
                (() => sign InBrackets "')'" CloseParen)
                (close => Bracketed comments inner close)
                (close => True)
                PostfixShaped
                (givesSign InBrackets "')'" CloseParen)
                (close signed => givesDone _ PostfixShaped (Both rfl shaped))))
    | Sign OpenSquare => Parse.readsThen givesSkip (skipRead skipped done =>
      Parse.readsThen (givesItems self CloseSquare nested) (itemsRead pair shaped =>
        match pair, shaped with
          | (found, close), shaped => Parse.readsDone (ListLiteral comments found close) _ (Both rfl shaped)))
    | Sign CloseParen => givesExpected "an expression" PostfixShaped
    | Sign CloseSquare => givesExpected "an expression" PostfixShaped
    | Sign Comma => givesExpected "an expression" PostfixShaped
    | Sign Dot => givesExpected "an expression" PostfixShaped
    | Sign Defines => givesExpected "an expression" PostfixShaped
    | Reserved keyword => givesExpected "an expression" PostfixShaped
    | Op operator => givesExpected "an expression" PostfixShaped
    | Stray text => givesExpected "an expression" PostfixShaped

theorem givesAtom ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Gives (() => self inner) Shaped):
    Gives (() => atom self layout) PostfixShaped :=
  state value after honest h =>
    match e: state.at.rest with
      | [token, ..later] =>
        match allowed: layout.allows token with
          | True => givesAtomOf self (layout.comments token) token.value.kind nested state value after honest h

theorem givesCallAfter ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (target: Expr) (open: Comments)
    (nested: ∀ (inner: Layout) => Gives (() => self inner) Shaped)
    (shaped: PostfixShaped target):
    Gives (() => callAfter self target open) PostfixShaped :=
  Parse.readsThen givesSkip (skipRead skipped done =>
    Parse.readsThen (givesItems self CloseParen nested) (itemsRead pair itemsShaped =>
      match pair, itemsShaped with
        | (arguments, close), itemsShaped =>
          Parse.readsDone
            (Call target open arguments close) _
            (Both rfl (Both shaped.left (Both shaped.right itemsShaped)))))

theorem givesFieldAfter ∀ (layout: Layout) (target: Expr) (dot: Comments)
    (shaped: PostfixShaped target):
    Gives (() => fieldAfter layout target dot) PostfixShaped :=
  Parse.readsThen givesSkip (skipRead skipped done =>
    Parse.readsThen (givesName layout) (nameRead pair named =>
      match pair with
        | (text, nameComments) =>
          Parse.readsDone (Field target dot text nameComments) _ (Both rfl (Both shaped.left shaped.right))))

--| Where `suffixesFrom` stops: it notes what it expected and gives the
--| target.
theorem givesSuffixesStop ∀ (target: Expr)
    (shaped: PostfixShaped target):
    Gives
      (() =>
        Parse.note (Parse.Problem.Expected "'('")
        Parse.note (Parse.Problem.Expected "'.'")
        target)
      PostfixShaped :=
  givesThen
    (() => Parse.note (Parse.Problem.Expected "'('"))
    (noted =>
      Parse.note (Parse.Problem.Expected "'.'")
      target)
    (noted => True)
    PostfixShaped
    (Parse.readsWeaken (Parse.readsNote (Parse.Problem.Expected "'('")) (taken noted none => rfl))
    (noted done => givesNoted (Parse.Problem.Expected "'.'") target PostfixShaped shaped)

theorem givesSuffixesAfter ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout) (more: Nat)
    (target: Expr) (tried: () → {Parse (Parse.Located Token)} Expr)
    (shaped: PostfixShaped target)
    (givesTried: Gives tried PostfixShaped)
    (givesMore: ∀ (longer: Expr) => PostfixShaped longer
      → Gives (() => suffixesFrom more self layout longer) PostfixShaped):
    Gives (() => suffixesAfter more self layout target (Parse.optional tried)) PostfixShaped :=
  givesThen
    (() => Parse.optional tried)
    (suffixesAfter more self layout target)
    (Perhaps PostfixShaped)
    PostfixShaped
    (givesOptional tried PostfixShaped givesTried)
    (longer found =>
      match longer, found with
        | Some longer, found => givesMore longer found
        | None, found => givesDone target PostfixShaped shaped)

--| An atom's calls and fields keep it postfix and of the parser's shape.
theorem givesSuffixes ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Gives (() => self inner) Shaped)
    (fuel: Nat) (target: Expr)
    (shaped: PostfixShaped target):
    Gives (() => suffixesFrom fuel self layout target) PostfixShaped :=
  match fuel with
    | Zero => state value after honest h =>
      match e: state.at.rest with
        | [] => givesSuffixesStop target shaped state value after honest h
        | [token, ..later] =>
          match allowed: layout.allows token with
            | False => givesSuffixesStop target shaped state value after honest h
            | True =>
              match kind: token.value.kind with
                | Sign OpenParen => givesSuffixesStop target shaped state value after honest h
                | Sign Dot => givesSuffixesStop target shaped state value after honest h
                | Sign CloseParen => givesSuffixesStop target shaped state value after honest h
                | Sign OpenSquare => givesSuffixesStop target shaped state value after honest h
                | Sign CloseSquare => givesSuffixesStop target shaped state value after honest h
                | Sign Comma => givesSuffixesStop target shaped state value after honest h
                | Sign Defines => givesSuffixesStop target shaped state value after honest h
                | Name text => givesSuffixesStop target shaped state value after honest h
                | Number digits => givesSuffixesStop target shaped state value after honest h
                | Str written => givesSuffixesStop target shaped state value after honest h
                | Reserved keyword => givesSuffixesStop target shaped state value after honest h
                | Op operator => givesSuffixesStop target shaped state value after honest h
                | Stray text => givesSuffixesStop target shaped state value after honest h
    | Succ more => state value after honest h =>
      match e: state.at.rest with
        | [] => givesSuffixesStop target shaped state value after honest h
        | [token, ..later] =>
          match allowed: layout.allows token with
            | False => givesSuffixesStop target shaped state value after honest h
            | True =>
              match kind: token.value.kind with
                | Sign OpenParen =>
                  givesSuffixesAfter self layout more target
                    (() => callAfter self target (layout.comments token))
                    shaped
                    (givesCallAfter self target (layout.comments token) nested shaped)
                    (longer longerShaped => givesSuffixes self layout nested more longer longerShaped)
                    state
                    value
                    after
                    honest
                    h
                | Sign Dot =>
                  givesSuffixesAfter self layout more target
                    (() => fieldAfter layout target (layout.comments token))
                    shaped
                    (givesFieldAfter layout target (layout.comments token) shaped)
                    (longer longerShaped => givesSuffixes self layout nested more longer longerShaped)
                    state
                    value
                    after
                    honest
                    h
                | Sign CloseParen => givesSuffixesStop target shaped state value after honest h
                | Sign OpenSquare => givesSuffixesStop target shaped state value after honest h
                | Sign CloseSquare => givesSuffixesStop target shaped state value after honest h
                | Sign Comma => givesSuffixesStop target shaped state value after honest h
                | Sign Defines => givesSuffixesStop target shaped state value after honest h
                | Name text => givesSuffixesStop target shaped state value after honest h
                | Number digits => givesSuffixesStop target shaped state value after honest h
                | Str written => givesSuffixesStop target shaped state value after honest h
                | Reserved keyword => givesSuffixesStop target shaped state value after honest h
                | Op operator => givesSuffixesStop target shaped state value after honest h
                | Stray text => givesSuffixesStop target shaped state value after honest h

theorem givesPostfix ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Gives (() => self inner) Shaped):
    Gives (() => postfix self layout) PostfixShaped :=
  givesThen
    (() => Parse.note (Parse.Problem.Expected "an expression"))
    (noted =>
      let first := atom self layout
      suffixesFrom (Parse.mark().left + 1) self layout first)
    (noted => True)
    PostfixShaped
    (Parse.readsWeaken (Parse.readsNote (Parse.Problem.Expected "an expression")) (taken noted none => rfl))
    (noted done =>
      givesThen
        (() => atom self layout)
        (first => suffixesFrom (Parse.mark().left + 1) self layout first)
        PostfixShaped
        PostfixShaped
        (givesAtom self layout nested)
        (first shaped =>
          givesThen
            (() => Parse.mark())
            (at => suffixesFrom (at.left + 1) self layout first)
            (at => True)
            PostfixShaped
            givesMark
            (at marked => givesSuffixes self layout nested (at.left + 1) first shaped)))

--| `-`s before a postfix expression make an operand of the parser's shape.
theorem givesNegations ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Gives (() => self inner) Shaped) (fuel: Nat):
    Gives (() => negationsFrom fuel self layout) OperandShaped :=
  let plain: Gives (() => postfix self layout) OperandShaped :=
    givesWeaken
      (() => postfix self layout)
      PostfixShaped
      OperandShaped
      (givesPostfix self layout nested)
      (expr shaped => Both (postfixIsOperand expr shaped.left) shaped.right)
  match fuel with
    | Zero => state value after honest h => plain state value after honest h
    | Succ more => state value after honest h =>
      match e: state.at.rest with
        | [] => plain state value after honest h
        | [token, ..later] =>
          match minus: isMinus layout token with
            | False => plain state value after honest h
            | True =>
              givesThen
                (() => skip())
                (skipped => Negate (layout.comments token) (negationsFrom more self layout))
                (skipped => True)
                OperandShaped
                givesSkip
                (skipped done =>
                  givesThen
                    (() => negationsFrom more self layout)
                    (inner => Negate (layout.comments token) inner)
                    OperandShaped
                    OperandShaped
                    (givesNegations self layout nested more)
                    (inner shaped => givesDone _ OperandShaped (Both rfl (Both shaped.left shaped.right))))
                state
                value
                after
                honest
                h

theorem givesOperand ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Gives (() => self inner) Shaped):
    Gives (() => operand self layout) OperandShaped :=
  givesThen
    (() => Parse.mark())
    (at => negationsFrom (at.left + 1) self layout)
    (at => True)
    OperandShaped
    givesMark
    (at marked => givesNegations self layout nested (at.left + 1))

-- Operator chains.

--| What `Parse.operators` gives for operators of level `lowest` (counted
--| from 0) or tighter: a chain of the parser's shape whose outermost
--| operator, if it has one, is of such a level.
def Grouped (lowest: Nat) (expr: Expr): Prop :=
  Shaped expr ∧ expr.isChain = True ∧ (expr.isOperand = True ∨ lowest < expr.chainLevel)

--| What `Parse.operators` holds on its left while it reads operators of
--| levels `lowest` to `highest`: a chain whose outermost operator, if it
--| has one, is no looser than either.
def Chained (lowest highest: Nat) (expr: Expr): Prop :=
  Shaped expr ∧ expr.isChain = True ∧ (expr.isOperand = True ∨ (lowest < expr.chainLevel ∧ highest < expr.chainLevel))

--| What `operatorLevels` finds for a token, if anything: an operator's
--| `Binary`, at the place of its level, chaining from the left.
def OperatorShape: Option (Nat, Parse.Associativity, Expr → Expr → Expr) → Prop
  | None => True
  | Some (level, associativity, combine) =>
    ∃ (operator: Operator) => ∃ (comments: Comments) => combine = Binary operator comments
      ∧ operator.level = level + 1
      ∧ associativity = LeftAssociative

--| A token is an operator the layout allows, or no level takes it.
theorem operatorOfKinds ∀ (layout: Layout) (token: Parse.Located Token):
    (∀ (level: Nat) => operatorOf layout level token = None)
      ∨ (∃ (operator: Operator) => token.value.kind = Op operator ∧ layout.allows token = True) :=
  match kind: token.value.kind with
    | Op operator =>
      match allowed: layout.allows token with
        | True => Inr (Witness operator (Both rfl rfl))
        | False => Inl (level =>
          match same: operator.level == level with
            | True => rfl
            | False => rfl)
    | Name text => Inl (level => rfl)
    | Number digits => Inl (level => rfl)
    | Str written => Inl (level => rfl)
    | Reserved keyword => Inl (level => rfl)
    | Sign punctuation => Inl (level => rfl)
    | Stray text => Inl (level => rfl)

theorem operatorShape ∀ (layout: Layout) (token: Parse.Located Token):
    OperatorShape (Parse.operatorFrom token 0 (operatorLevels layout)) :=
  match operatorOfKinds layout token with
    | Inl none => rewrite none 1, none 2, none 3, none 4, none 5, none 6 in rfl
    | Inr (Witness operator (Both kind allowed)) =>
      rewrite operatorFound layout token operator kind allowed in
        Witness operator (Witness (layout.comments token) (Both rfl (Both (omega [(levelRange operator).left]) rfl)))

--| An operator read after a chain, with its right side grouped tighter,
--| makes a chain of the parser's shape.
theorem chainStep ∀ (layout: Layout) (lowest highest level: Nat) (associativity: Parse.Associativity)
    (combine: Expr → Expr → Expr) (item: Parse.Located Token) (left right: Expr)
    (found: Parse.operatorFrom item 0 (operatorLevels layout) = Some (level, associativity, combine))
    (above: lowest ≤ level)
    (below: level ≤ highest)
    (chained: Chained lowest highest left)
    (grouped: Grouped (Parse.nextLowest associativity level) right):
    Chained lowest level (combine left right) :=
  let shape := operatorShape layout item
  let known := rewrite found at shape in shape
  match known with
    | Witness operator (Witness comments (Both isBinary (Both level1 isLeft))) =>
      let groupedLeft: Grouped (level + 1) right := rewrite isLeft at grouped in grouped
      let leftBound: operator.level ≤ left.chainLevel := match chained.right.right with
        | Inl isOperand => omega [operandLevel left isOperand, (levelRange operator).right]
        | Inr both => omega [both.right, below, level1]
      let rightBound: operator.level < right.chainLevel := match groupedLeft.right.right with
        | Inl isOperand => omega [operandLevel right isOperand, (levelRange operator).right]
        | Inr low => omega [low, level1]
      rewrite isBinary in
        Both
          (Both leftBound
            (Both rightBound
              (Both chained.right.left (Both groupedLeft.right.left (Both chained.left groupedLeft.left)))))
          (Both rfl (Inr (Both (omega [above, level1]) (omega [level1]))))

--| An operator chain is of the parser's shape: grouped by precedence, each
--| level chaining from the left.
theorem givesChain ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Gives (() => self inner) Shaped):
    Gives (() => Parse.operators "an operator" (operatorLevels layout) (() => operand self layout)) Shaped :=
  Parse.readsWeaken
    (Parse.readsOperators "an operator"
      (operatorLevels layout)
      (() => operand self layout)
      OperandShaped
      Grouped
      Chained
      (givesOperand self layout nested)
      (lowest highest value isOperand =>
        Both isOperand.right (Both (operandIsChain value isOperand.left) (Inl isOperand.left)))
      (lowest highest value chained =>
        Both chained.left
          (Both chained.right.left
            (match chained.right.right with
              | Inl isOperand => Inl isOperand
              | Inr both => Inr both.left)))
      (chainStep layout))
    (taken value grouped => grouped.left)

-- Bodies and blocks.

--| A statement of the parser's shape that isn't a comment line.
def CodedShaped (line: Statement): Prop := ShapedStatement line ∧ Coded line

theorem givesBare ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Gives (() => self inner) Shaped):
    Gives (() => bareStatement self layout) CodedShaped :=
  givesThen (() => self layout) (value => Bare value) Shaped CodedShaped (nested layout) (value shaped =>
    givesDone _ CodedShaped (Both shaped rfl))

theorem givesInline ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Gives (() => self inner) Shaped):
    Gives (() => inlineBody self layout) ShapedBody :=
  givesThen
    (() => bareStatement self layout)
    (line => { statements = [{ blankBefore = False, line }] })
    CodedShaped
    ShapedBody
    (givesBare self layout nested)
    (line found => match found with | Both shaped coded => givesDone _ ShapedBody (Both (Both shaped rfl) coded))

theorem shapedLinesAppend ∀ (front back: List (Spaced Statement))
    (frontShaped: ShapedLines front)
    (backShaped: ShapedLines back):
    ShapedLines (front ++ back) :=
  match front, frontShaped with
    | [], frontShaped => backShaped
    | [{ blankBefore, line }, ..rest], Both lineShaped restShaped =>
      Both lineShaped (shapedLinesAppend rest back restShaped backShaped)

theorem shapedNotes ∀ (trivia: List Trivia) (found: (List (Spaced Statement), Bool))
    (shaped: ShapedLines found.fst):
    ShapedLines (trivia.foldLeft found (noteStep StatementNote)).fst :=
  match trivia with
    | [] => shaped
    | [BlankLine, ..rest] => shapedNotes rest (noteStep StatementNote found BlankLine) shaped
    | [OwnLine comment, ..rest] =>
      shapedNotes rest
        (noteStep StatementNote found (OwnLine comment))
        (shapedLinesAppend found.fst [{ blankBefore = found.snd, line = StatementNote comment }] shaped (Both rfl rfl))

--| A statement's lines, the notes above it and itself, are of the
--| parser's shape when it is.
theorem shapedNoted ∀ (above: List Trivia) (line: Statement)
    (shaped: ShapedStatement line):
    ShapedLines (notedStatement above line) :=
  let notesShaped: ShapedLines (spacedNotes StatementNote above).fst := shapedNotes above ([], False) rfl
  match found: spacedNotes StatementNote above with
    | (notes, blankBefore) => shapedLinesAppend notes [{ blankBefore, line }] notesShaped (Both shaped rfl)

theorem closedCons ∀ (first: Spaced Statement) (lines: List (Spaced Statement))
    (closed: ClosedLines lines):
    ClosedLines [first, ..lines] :=
  match lines, closed with
    | [], never => Void.exfalso (Bool.falseNotTrue never)
    | [next, ..more], closed => closed

--| Lines before lines that end in a statement end in it too.
theorem closedAppend ∀ (front back: List (Spaced Statement)) (closed: ClosedLines back): ClosedLines (front ++ back) :=
  match front with
    | [] => closed
    | [first, ..rest] => closedCons first (rest ++ back) (closedAppend rest back closed)

--| A statement's lines end in the statement, whatever notes are above
--| it.
theorem closedNoted ∀ (above: List Trivia) (line: Statement)
    (coded: Coded line):
    ClosedLines (notedStatement above line) :=
  match found: spacedNotes StatementNote above with
    | (notes, blankBefore) => closedAppend notes [{ blankBefore, line }] coded

theorem closedWithoutFirstBlank ∀ (lines: List (Spaced Statement))
    (closed: ClosedLines lines):
    ClosedLines (withoutFirstBlank lines) :=
  match lines, closed with
    | [], never => Void.exfalso (Bool.falseNotTrue never)
    | [{ blankBefore, line }], coded => coded
    | [{ blankBefore, line }, next, ..rest], closed => closed

theorem shapedWithoutFirstBlank ∀ (lines: List (Spaced Statement))
    (shaped: ShapedLines lines):
    ShapedLines (withoutFirstBlank lines) :=
  match lines, shaped with
    | [], shaped => rfl
    | [{ blankBefore, line }, ..rest], Both lineShaped restShaped => Both lineShaped restShaped

--| Lines of the parser's shape that end in a statement.
def ClosedShaped (lines: List (Spaced Statement)): Prop := ShapedLines lines ∧ ClosedLines lines

--| Each group of lines is of the parser's shape and ends in a statement.
def AllShaped: List (List (Spaced Statement)) → Prop
  | [] => True
  | [first, ..rest] => ClosedShaped first ∧ AllShaped rest

theorem eachShaped ∀ (values: List (List (Spaced Statement))) (taken: List (Parse.Located Token))
    (each: Parse.Each (read lines => ClosedShaped lines) taken values):
    AllShaped values :=
  match values, each with
    | [], each => rfl
    | [first, ..rest], Witness firstRead (Witness restRead (Both split (Both holds more))) =>
      Both holds (eachShaped rest restRead more)

theorem shapedConcat ∀ (groups: List (List (Spaced Statement))) (all: AllShaped groups): ShapedLines groups.concat :=
  match groups, all with
    | [], all => rfl
    | [first, ..rest], Both (Both firstShaped _) restShaped =>
      shapedLinesAppend first rest.concat firstShaped (shapedConcat rest restShaped)

--| Groups of lines that each end in a statement, one after another, end
--| in a statement.
theorem closedConcat ∀ (first: List (Spaced Statement)) (rest: List (List (Spaced Statement)))
    (all: AllShaped [first, ..rest]):
    ClosedLines [first, ..rest].concat :=
  match rest, all with
    | [], Both (Both _ closed) _ => rewrite List.appendNil first in closed
    | [second, ..more], Both _ others => closedAppend first [second, ..more].concat (closedConcat second more others)

theorem givesStatementLine ∀ (self: Layout → {Parse (Parse.Located Token)} Expr)
    (nested: ∀ (inner: Layout) => Gives (() => self inner) Shaped) (fuel: Nat)
    (givesBody: ∀ (inner: Layout) => Gives (() => bodyFuel fuel self inner) ShapedBody)
    (layout: Layout) (first: Parse.Located Token) (kind: Kind):
    Gives (() => statementLine fuel self layout first kind) CodedShaped :=
  match kind with
    | Reserved LetKeyword => Parse.readsThen givesSkip (skipRead skipped done =>
      Parse.readsThen (givesName layout) (nameRead pair named =>
        match pair with
          | (bound, nameComments) =>
            givesThen
              (() => sign layout "'='" Defines)
              (equals => Let (layout.comments first) bound nameComments equals (bodyFuel fuel self layout))
              (equals => True)
              CodedShaped
              (givesSign layout "'='" Defines)
              (equals signed =>
                givesThen
                  (() => bodyFuel fuel self layout)
                  (inner => Let (layout.comments first) bound nameComments equals inner)
                  ShapedBody
                  CodedShaped
                  (givesBody layout)
                  (inner shaped => givesDone _ CodedShaped (Both shaped rfl)))))
    | Reserved FnKeyword => givesBare self layout nested
    | Reserved IfKeyword => givesBare self layout nested
    | Reserved ThenKeyword => givesBare self layout nested
    | Reserved ElseKeyword => givesBare self layout nested
    | Name text => givesBare self layout nested
    | Number digits => givesBare self layout nested
    | Str written => givesBare self layout nested
    | Sign punctuation => givesBare self layout nested
    | Op operator => givesBare self layout nested
    | Stray text => givesBare self layout nested

theorem givesStatement ∀ (self: Layout → {Parse (Parse.Located Token)} Expr)
    (nested: ∀ (inner: Layout) => Gives (() => self inner) Shaped) (fuel: Nat)
    (givesBody: ∀ (inner: Layout) => Gives (() => bodyFuel fuel self inner) ShapedBody) (column: Nat):
    Gives (() => statement fuel self column) ClosedShaped :=
  state value after honest h =>
    match e: state.at.rest with
      | [first, ..later] =>
        match starts: first.value.startsLine && first.value.column == column with
          | True =>
            givesThen
              (() => statementLine fuel self (InStatement column first.offset) first first.value.kind)
              (line => notedStatement first.value.above line)
              CodedShaped
              ClosedShaped
              (givesStatementLine self nested fuel givesBody (InStatement column first.offset) first first.value.kind)
              (line found =>
                match found with
                  | Both shaped coded =>
                    givesDone _ ClosedShaped
                      (Both (shapedNoted first.value.above line shaped) (closedNoted first.value.above line coded)))
              state
              value
              after
              honest
              h

theorem givesBlock ∀ (self: Layout → {Parse (Parse.Located Token)} Expr)
    (nested: ∀ (inner: Layout) => Gives (() => self inner) Shaped) (fuel: Nat)
    (givesBody: ∀ (inner: Layout) => Gives (() => bodyFuel fuel self inner) ShapedBody) (column: Nat):
    Gives (() => block fuel self column) ShapedBody :=
  givesThen
    (() => Parse.many1 (() => statement fuel self column))
    (lines => { statements = lines.toList.concat |> withoutFirstBlank })
    (lines => AllShaped lines.toList)
    ShapedBody
    (Parse.readsWeaken
      (Parse.readsMany1
        (() => statement fuel self column)
        (read lines => ClosedShaped lines)
        (givesStatement self nested fuel givesBody column))
      (taken lines each => eachShaped lines.toList taken each))
    (lines all =>
      givesDone _ ShapedBody
        (Both
          (shapedWithoutFirstBlank lines.toList.concat (shapedConcat lines.toList all))
          (closedWithoutFirstBlank lines.toList.concat (closedConcat lines.head lines.tail all))))

--| A body, a block or one expression, holds expressions of the parser's
--| shape.
theorem givesBodyFuel ∀ (self: Layout → {Parse (Parse.Located Token)} Expr)
    (nested: ∀ (inner: Layout) => Gives (() => self inner) Shaped)
    (fuel: Nat) (layout: Layout):
    Gives (() => bodyFuel fuel self layout) ShapedBody :=
  match fuel with
    | Zero => state value after honest h => Void.exfalso (Result.errNotOk h)
    | Succ more => state value after honest h =>
      match layout with
        | InBrackets => givesInline self InBrackets nested state value after honest h
        | InStatement column start =>
          match e: state.at.rest with
            | [] => givesInline self (InStatement column start) nested state value after honest h
            | [token, ..later] =>
              match deeper: token.value.startsLine && token.value.column > column with
                | False => givesInline self (InStatement column start) nested state value after honest h
                | True =>
                  givesBlock self nested more
                    (inner => givesBodyFuel self nested more inner)
                    token.value.column
                    state
                    value
                    after
                    honest
                    h

theorem givesBody ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Gives (() => self inner) Shaped):
    Gives (() => body self layout) ShapedBody :=
  givesThen
    (() => Parse.mark())
    (at => bodyFuel (at.left + 1) self layout)
    (at => True)
    ShapedBody
    givesMark
    (at marked => givesBodyFuel self nested (at.left + 1) layout)

-- `if`, and the expression parser.

theorem givesElse ∀ (layout: Layout): Gives (() => elseKeyword layout) (comments => True) :=
  state value after honest h =>
    match e: state.at.rest with
      | [] => givesKeyword layout ElseKeyword state value after honest h
      | [token, ..later] =>
        match isElse: (keywordIs ElseKeyword token.value.kind).isSome with
          | False => givesKeyword layout ElseKeyword state value after honest h
          | True =>
            match allowed: layout.allowsElse token with
              | True =>
                givesThen
                  (() => skip())
                  (skipped => layout.comments token)
                  (skipped => True)
                  (comments => True)
                  givesSkip
                  (skipped done => givesDone _ _ rfl)
                  state
                  value
                  after
                  honest
                  h

--| One level of the expression parser gives an expression of the
--| parser's shape, given that `self` does for the expressions nested in it.
theorem givesExpressionRule ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Gives (() => self inner) Shaped):
    Gives (() => expressionRule self layout) Shaped :=
  state value after honest h =>
    match e: state.at.rest with
      | [] => givesChain self layout nested state value after honest h
      | [token, ..later] =>
        match found: isIf layout token with
          | False => givesChain self layout nested state value after honest h
          | True =>
            givesThen
              (() => skip())
              (skipped =>
                let condition := self layout
                let thenComments := keyword layout ThenKeyword
                let whenTrue := body self layout
                let elseComments := elseKeyword layout
                let whenFalse := body self layout
                If (layout.comments token) condition thenComments whenTrue elseComments whenFalse)
              (skipped => True)
              Shaped
              givesSkip
              (skipped done =>
                givesThen
                  (() => self layout)
                  (condition =>
                    let thenComments := keyword layout ThenKeyword
                    let whenTrue := body self layout
                    let elseComments := elseKeyword layout
                    let whenFalse := body self layout
                    If (layout.comments token) condition thenComments whenTrue elseComments whenFalse)
                  Shaped
                  Shaped
                  (nested layout)
                  (condition conditionShaped =>
                    givesThen
                      (() => keyword layout ThenKeyword)
                      (thenComments =>
                        let whenTrue := body self layout
                        let elseComments := elseKeyword layout
                        let whenFalse := body self layout
                        If (layout.comments token) condition thenComments whenTrue elseComments whenFalse)
                      (thenComments => True)
                      Shaped
                      (givesKeyword layout ThenKeyword)
                      (thenComments thenRead =>
                        givesThen
                          (() => body self layout)
                          (whenTrue =>
                            let elseComments := elseKeyword layout
                            let whenFalse := body self layout
                            If (layout.comments token) condition thenComments whenTrue elseComments whenFalse)
                          ShapedBody
                          Shaped
                          (givesBody self layout nested)
                          (whenTrue trueShaped =>
                            givesThen
                              (() => elseKeyword layout)
                              (elseComments =>
                                let whenFalse := body self layout
                                If (layout.comments token) condition thenComments whenTrue elseComments whenFalse)
                              (elseComments => True)
                              Shaped
                              (givesElse layout)
                              (elseComments elseRead =>
                                givesThen
                                  (() => body self layout)
                                  (whenFalse =>
                                    If (layout.comments token) condition thenComments whenTrue elseComments whenFalse)
                                  ShapedBody
                                  Shaped
                                  (givesBody self layout nested)
                                  (whenFalse falseShaped =>
                                    givesDone _ Shaped (Both conditionShaped (Both trueShaped falseShaped))))))))
              state
              value
              after
              honest
              h

--| Every expression the parser gives is of the parser's shape (`Shaped`):
--| whatever the tokens, if `expression` succeeds, its operators are
--| grouped by precedence and chain from the left, a call's callee and a
--| field's target are postfix expressions, and `-` stands before an
--| operand, in every nested expression and every block of an `if`.
theorem givesExpression ∀ (layout: Layout): Gives (() => expression layout) Shaped :=
  Parse.readsRecursiveWith expressionRule
    (inner taken expr => Shaped expr)
    (self nested argument => givesExpressionRule self argument nested)
    layout

-- Declarations and the file.

--| The last parameter has no comma after it, so its comma's comments are
--| none.
def BareLast: List Parameter → Prop
  | [] => True
  | [{ comma, .. }] => comma = Comments.none
  | [_, ..rest] => BareLast rest

theorem withCommasCons ∀ (first: (Text, Comments)) (others: List (Comments, (Text, Comments))):
    ∃ (head: Parameter) => ∃ (tail: List Parameter) => withCommas first others = [head, ..tail] :=
  match others with
    | [] => Witness _ (Witness [] rfl)
    | [(comma, next), ..rest] => Witness _ (Witness (withCommas next rest) rfl)

theorem withCommasBare ∀ (first: (Text, Comments)) (others: List (Comments, (Text, Comments))):
    BareLast (withCommas first others) :=
  match others with
    | [] => rfl
    | [(comma, next), ..rest] =>
      let bare := withCommasBare next rest
      match withCommasCons next rest with
        | Witness head (Witness tail same) => rewrite same in (rewrite same at bare in bare)

--| The parameters the parser builds end in one with no comma.
theorem parametersBare ∀ (found: Option ((Text, Comments), List (Comments, (Text, Comments)))):
    BareLast (parametersOf found) :=
  match found with
    | None => rfl
    | Some (first, others) => withCommasBare first others

--| Each expression in the declaration is of the parser's shape, and a
--| function's last parameter has no comma.
def ShapedDeclaration: Declaration → Prop
  | Function _ _ _ _ parameters _ _ found => BareLast parameters ∧ ShapedBody found
  | Value _ _ _ _ found => ShapedBody found
  | DeclarationNote _ => True

def ShapedDeclarations: List (Spaced Declaration) → Prop
  | [] => True
  | [{ line, .. }, ..rest] => ShapedDeclaration line ∧ ShapedDeclarations rest

--| Each expression in the file is of the parser's shape, each body ends
--| in a statement, and each function's last parameter has no comma.
def ShapedFile: SourceFile → Prop
  | { declarations } => ShapedDeclarations declarations

theorem givesParameterStep: Gives parameterStep (step => True) :=
  givesThen
    (() => sign InBrackets "','" Comma)
    (comma =>
      let named := name InBrackets
      (comma, named))
    (comma => True)
    (step => True)
    (givesSign InBrackets "','" Comma)
    (comma signed =>
      givesThen
        (() => name InBrackets)
        (named => (comma, named))
        (named => True)
        (step => True)
        (givesName InBrackets)
        (named done => givesDone _ _ rfl))

theorem givesParameterList: Gives parameterList (found => True) :=
  givesThen
    (() => name InBrackets)
    (first =>
      let others := Parse.many parameterStep
      (first, others))
    (first => True)
    (found => True)
    (givesName InBrackets)
    (first named =>
      givesThen
        (() => Parse.many parameterStep)
        (others => (first, others))
        (others => True)
        (found => True)
        (Parse.readsWeaken (Parse.readsMany parameterStep (read step => True) givesParameterStep) (taken others each =>
          rfl))
        (others done => givesDone _ _ rfl))

theorem givesParameters: Gives (() => parametersOf (Parse.optional parameterList)) BareLast :=
  givesThen
    (() => Parse.optional parameterList)
    (found => parametersOf found)
    (found => True)
    BareLast
    (Parse.readsWeaken (Parse.readsOptional givesParameterList) (taken found maybe => rfl))
    (found listed => givesDone _ BareLast (parametersBare found))

theorem givesFunctionLine ∀ (layout: Layout) (first: Parse.Located Token):
    Gives (() => functionLine layout first) ShapedDeclaration :=
  Parse.readsThen givesSkip (skipRead skipped done =>
    Parse.readsThen (givesName layout) (nameRead pair named =>
      match pair with
        | (declared, nameComments) =>
          givesThen
            (() => sign layout "'('" OpenParen)
            (open =>
              let parameters := parametersOf (Parse.optional parameterList)
              let close := sign InBrackets "')'" CloseParen
              let equals := sign layout "'='" Defines
              Function
                (layout.comments first)
                declared
                nameComments
                open
                parameters
                close
                equals
                (body expression layout))
            (open => True)
            ShapedDeclaration
            (givesSign layout "'('" OpenParen)
            (open opened =>
              givesThen
                (() => parametersOf (Parse.optional parameterList))
                (parameters =>
                  let close := sign InBrackets "')'" CloseParen
                  let equals := sign layout "'='" Defines
                  Function
                    (layout.comments first)
                    declared
                    nameComments
                    open
                    parameters
                    close
                    equals
                    (body expression layout))
                BareLast
                ShapedDeclaration
                givesParameters
                (parameters listed =>
                  givesThen
                    (() => sign InBrackets "')'" CloseParen)
                    (close =>
                      let equals := sign layout "'='" Defines
                      Function
                        (layout.comments first)
                        declared
                        nameComments
                        open
                        parameters
                        close
                        equals
                        (body expression layout))
                    (close => True)
                    ShapedDeclaration
                    (givesSign InBrackets "')'" CloseParen)
                    (close closed =>
                      givesThen
                        (() => sign layout "'='" Defines)
                        (equals =>
                          Function
                            (layout.comments first)
                            declared
                            nameComments
                            open
                            parameters
                            close
                            equals
                            (body expression layout))
                        (equals => True)
                        ShapedDeclaration
                        (givesSign layout "'='" Defines)
                        (equals signed =>
                          givesThen
                            (() => body expression layout)
                            (inner =>
                              Function (layout.comments first) declared nameComments open parameters close equals inner)
                            ShapedBody
                            ShapedDeclaration
                            (givesBody expression layout givesExpression)
                            (inner shaped => givesDone _ ShapedDeclaration (Both listed shaped))))))))

theorem givesValueLine ∀ (layout: Layout) (first: Parse.Located Token):
    Gives (() => valueLine layout first) ShapedDeclaration :=
  Parse.readsThen givesSkip (skipRead skipped done =>
    Parse.readsThen (givesName layout) (nameRead pair named =>
      match pair with
        | (declared, nameComments) =>
          givesThen
            (() => sign layout "'='" Defines)
            (equals => Value (layout.comments first) declared nameComments equals (body expression layout))
            (equals => True)
            ShapedDeclaration
            (givesSign layout "'='" Defines)
            (equals signed =>
              givesThen
                (() => body expression layout)
                (inner => Value (layout.comments first) declared nameComments equals inner)
                ShapedBody
                ShapedDeclaration
                (givesBody expression layout givesExpression)
                (inner shaped => givesDone _ ShapedDeclaration shaped))))

theorem givesDeclarationLine ∀ (layout: Layout) (first: Parse.Located Token):
    Gives (() => declarationLine layout first) ShapedDeclaration :=
  state value after honest h =>
    match kind: first.value.kind with
      | Reserved FnKeyword => givesFunctionLine layout first state value after honest h
      | Reserved LetKeyword => givesValueLine layout first state value after honest h

theorem declarationsAppend ∀ (front back: List (Spaced Declaration))
    (frontShaped: ShapedDeclarations front)
    (backShaped: ShapedDeclarations back):
    ShapedDeclarations (front ++ back) :=
  match front, frontShaped with
    | [], frontShaped => backShaped
    | [{ blankBefore, line }, ..rest], Both lineShaped restShaped =>
      Both lineShaped (declarationsAppend rest back restShaped backShaped)

theorem declarationNotes ∀ (trivia: List Trivia) (found: (List (Spaced Declaration), Bool))
    (shaped: ShapedDeclarations found.fst):
    ShapedDeclarations (trivia.foldLeft found (noteStep DeclarationNote)).fst :=
  match trivia with
    | [] => shaped
    | [BlankLine, ..rest] => declarationNotes rest (noteStep DeclarationNote found BlankLine) shaped
    | [OwnLine comment, ..rest] =>
      declarationNotes rest
        (noteStep DeclarationNote found (OwnLine comment))
        (declarationsAppend found.fst
          [{ blankBefore = found.snd, line = DeclarationNote comment }]
          shaped
          (Both rfl rfl))

theorem shapedNotedDeclaration ∀ (above: List Trivia) (line: Declaration)
    (shaped: ShapedDeclaration line):
    ShapedDeclarations (notedDeclaration above line) :=
  let notesShaped: ShapedDeclarations (spacedNotes DeclarationNote above).fst := declarationNotes above ([], False) rfl
  match found: spacedNotes DeclarationNote above with
    | (notes, blankBefore) => declarationsAppend notes [{ blankBefore, line }] notesShaped (Both shaped rfl)

theorem declarationsWithoutFirstBlank ∀ (lines: List (Spaced Declaration))
    (shaped: ShapedDeclarations lines):
    ShapedDeclarations (withoutFirstBlank lines) :=
  match lines, shaped with
    | [], shaped => rfl
    | [{ blankBefore, line }, ..rest], Both lineShaped restShaped => Both lineShaped restShaped

def AllDeclarations: List (List (Spaced Declaration)) → Prop
  | [] => True
  | [first, ..rest] => ShapedDeclarations first ∧ AllDeclarations rest

theorem eachDeclarations ∀ (values: List (List (Spaced Declaration))) (taken: List (Parse.Located Token))
    (each: Parse.Each (read lines => ShapedDeclarations lines) taken values):
    AllDeclarations values :=
  match values, each with
    | [], each => rfl
    | [first, ..rest], Witness firstRead (Witness restRead (Both split (Both holds more))) =>
      Both holds (eachDeclarations rest restRead more)

theorem declarationsConcat ∀ (groups: List (List (Spaced Declaration)))
    (all: AllDeclarations groups):
    ShapedDeclarations groups.concat :=
  match groups, all with
    | [], all => rfl
    | [first, ..rest], Both firstShaped restShaped =>
      declarationsAppend first rest.concat firstShaped (declarationsConcat rest restShaped)

theorem givesDeclaration: Gives declaration ShapedDeclarations := state value after honest h =>
  match e: state.at.rest with
    | [first, ..later] =>
      match starts: first.value.startsLine && first.value.column == 0 with
        | True =>
          givesThen
            (() => declarationLine (InStatement 0 first.offset) first)
            (parsed => notedDeclaration first.value.above parsed)
            ShapedDeclaration
            ShapedDeclarations
            (givesDeclarationLine (InStatement 0 first.offset) first)
            (parsed shaped => givesDone _ ShapedDeclarations (shapedNotedDeclaration first.value.above parsed shaped))
            state
            value
            after
            honest
            h

theorem shapedFileOf ∀ (declarations: List (Spaced Declaration)) (endTrivia: List Trivia)
    (shaped: ShapedDeclarations declarations):
    ShapedFile (fileOf declarations endTrivia) :=
  let notesShaped: ShapedDeclarations (spacedNotes DeclarationNote endTrivia).fst :=
    declarationNotes endTrivia ([], False) rfl
  match found: spacedNotes DeclarationNote endTrivia with
    | (endNotes, blank) =>
      declarationsWithoutFirstBlank
        (declarations ++ endNotes)
        (declarationsAppend declarations endNotes shaped notesShaped)

theorem givesFileEnd ∀ (declarations: List (Spaced Declaration)) (endTrivia: List Trivia)
    (shaped: ShapedDeclarations declarations):
    Gives (() => fileEnd declarations endTrivia) ShapedFile :=
  state value after honest h =>
    match e: state.at.rest with
      | [] =>
        givesDone
          (fileOf declarations endTrivia)
          ShapedFile
          (shapedFileOf declarations endTrivia shaped)
          state
          value
          after
          honest
          h
      | [token, ..later] =>
        match indented: token.value.startsLine && token.value.column > 0 with
          | False =>
            givesDone
              (fileOf declarations endTrivia)
              ShapedFile
              (shapedFileOf declarations endTrivia shaped)
              state
              value
              after
              honest
              h

theorem givesSourceFile ∀ (endTrivia: List Trivia): Gives (() => sourceFile endTrivia) ShapedFile :=
  givesThen
    (() => Parse.many declaration)
    (found => fileEnd found.concat endTrivia)
    AllDeclarations
    ShapedFile
    (Parse.readsWeaken
      (Parse.readsMany declaration (read lines => ShapedDeclarations lines) givesDeclaration)
      (taken found each => eachDeclarations found taken each))
    (found all => givesFileEnd found.concat endTrivia (declarationsConcat found all))

--| What the parser guarantees about its trees: in every file `parse`
--| gives, whatever the source, every expression is of the parser's shape
--| (`Shaped`: operators grouped by precedence and chaining from the left,
--| a call's callee and a field's target postfix, `-` before an operand),
--| in every declaration, block and branch; every body (after `=`, `then`
--| and `else`) ends in a statement, not a comment line (`ClosedLines`);
--| a function's last parameter has no comma's comments (`BareLast`), and
--| neither has the last item of a list or the last argument of a call
--| (`BareLastItem`).
--| So the read-back theorems' `Shaped` hypotheses hold of every parsed
--| tree, with no check at run time.
theorem parseShaped ∀ (source: Text) (file: SourceFile) (parsed: parse source = Ok file): ShapedFile file :=
  match lexed: lex source with
    | Ok tokens =>
      match whole: Parse.whole tokens.tokens (() => sourceFile tokens.endTrivia) with
        | Ok found =>
          let same: found = file := Result.okInjective parsed
          rewrite <- same in
            Parse.wholeReads tokens.tokens
              (() => sourceFile tokens.endTrivia)
              (taken value => ShapedFile value)
              found
              (givesSourceFile tokens.endTrivia)
              whole
