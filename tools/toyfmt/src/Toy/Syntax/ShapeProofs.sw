--| What the parser guarantees about its trees: every expression it gives
--| is of the shape `Shaped` describes (operators grouped by precedence, a
--| call's callee and a field's target postfix, `-` before an operand), so
--| the read-back theorems' `Shaped` hypothesis holds of every parsed tree
--| and needn't be checked. Built from std's soundness lemmas
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

theorem givesItem ∀ (self: Layout → {Parse (Parse.Located Token)} Expr)
    (nested: ∀ (inner: Layout) => Gives (() => self inner) Shaped):
    Gives (() => item self) (read => Shaped read.fst.value) :=
  givesThen
    (() => self InBrackets)
    (value =>
      let comma := signInBrackets "','" Comma
      ({ value, comma = comma.getOrElse Comments.none }, comma.isSome))
    Shaped
    (read => Shaped read.fst.value)
    (nested InBrackets)
    (value shaped =>
      givesThen
        (() => signInBrackets "','" Comma)
        (comma => ({ value, comma = comma.getOrElse Comments.none }, comma.isSome))
        (comma => True)
        (read => Shaped read.fst.value)
        (givesSignInBrackets "','" Comma)
        (comma found => givesDone _ _ shaped))

theorem givesItemsFrom ∀ (self: Layout → {Parse (Parse.Located Token)} Expr)
    (nested: ∀ (inner: Layout) => Gives (() => self inner) Shaped)
    (fuel: Nat) (found: List Item)
    (shaped: ShapedItems found):
    Gives (() => itemsFrom fuel self found) ShapedItems :=
  match fuel with
    | Zero => givesDone found.reverse ShapedItems (shapedItemsReverse found shaped)
    | Succ more =>
      givesThen
        (() => item self)
        (itemsAfter more self found)
        (read => Shaped read.fst.value)
        ShapedItems
        (givesItem self nested)
        (read valueShaped =>
          match read, valueShaped with
            | ({ value, comma }, True), valueShaped =>
              givesItemsFrom self nested more [{ value, comma }, ..found] (Both valueShaped shaped)
            | ({ value, comma }, False), valueShaped =>
              givesDone _ ShapedItems (shapedItemsReverse [{ value, comma }, ..found] (Both valueShaped shaped)))

--| `items` gives items whose values are of the parser's shape, when the
--| nested parser does.
theorem givesItems ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (closer: Punctuation)
    (nested: ∀ (inner: Layout) => Gives (() => self inner) Shaped):
    Gives (() => items self closer) (found => ShapedItems found.fst) :=
  Parse.readsThen (givesSignInBrackets "'${closer.spelling}'" closer) (firstRead closed facts =>
    match closed with
      | Some close => Parse.readsDone ([], close) _ rfl
      | None =>
        givesThen
          (() => Parse.mark())
          (at =>
            let found := itemsFrom at.left self []
            let close := sign InBrackets "'${closer.spelling}'" closer
            (found, close))
          (at => True)
          (found => ShapedItems found.fst)
          givesMark
          (at marked =>
            givesThen
              (() => itemsFrom at.left self [])
              (found =>
                let close := sign InBrackets "'${closer.spelling}'" closer
                (found, close))
              ShapedItems
              (found => ShapedItems found.fst)
              (givesItemsFrom self nested at.left [] rfl)
              (found shaped =>
                givesThen
                  (() => sign InBrackets "'${closer.spelling}'" closer)
                  (close => (found, close))
                  (close => True)
                  (found => ShapedItems found.fst)
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
