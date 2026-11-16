--| The parser copies the lexer's texts. Given tokens whose texts are the
--| lexer's (`Good`: each name a word that spells no keyword, each number
--| digits, each string closed, each comment a comment), every tree the
--| parser gives is `Lexical`: its names, numbers, strings and comments
--| are those tokens', and its bodies end in statements. So `LexicalFile`
--| holds of every parsed file (`parseLexical`), and a parsed file
--| printed at any width lexes to its pieces (`parsedPrintTokens`). Built
--| from std's `Parse.ReadsIn` under `Parse.Invariant.every`, soundness over items known to be good.

namespace Toy.Fmt.Proofs
import Toy.Doc (..)
import Toy.Doc.Proofs (..)
import Toy.Syntax (..)
import Toy.Syntax.Proofs (..)
import Toy.Fmt (..)
import Std.Parse.Associativity (LeftAssociative)
import Std (And, Bool, Eq, List, NonEmptyList, Option, Pair, Parse, Result, Text, Void)

--| A kind whose text is what the printer's rules need of it.
def GoodKind: Kind → Prop
  | Name text => IsName text
  | Number digits => IsDigits digits
  | Str written => IsString written
  | _ => True

--| A token with the lexer's texts: its kind's, and its comments'.
def Good (token: Parse.Located Token): Prop :=
  GoodKind token.value.kind ∧ FineTrivia token.value.above ∧ FineTrailing token.value.trailing

--| Given tokens that are all `Good`, whenever `parser` succeeds, `holds`
--| of its value.
def Fair (parser: () → {Parse (Parse.Located Token)} a) (holds: a → Prop): Prop :=
  Parse.ReadsIn (Parse.Invariant.every Good) parser (taken value => holds value)

theorem fairDone ∀ (x: a) (holds: a → Prop) (proved: holds x): Fair (() => x) holds := Parse.readsDone x _ proved

--| `p`, then `j` of its value.
theorem fairThen ∀ (p: () → {Parse (Parse.Located Token)} a) (j: a → {Parse (Parse.Located Token)} b)
    (first: a → Prop) (holds: b → Prop)
    (fairFirst: Fair p first)
    (rest: ∀ (v: a) => first v → Fair (() => j v) holds):
    Fair (() => j (p())) holds :=
  Parse.readsThenOf p j _ _ fairFirst (firstRead v facts => rest v facts)

--| What a parser gives from any tokens, it gives from good ones.
theorem fairOf ∀ (p: () → {Parse (Parse.Located Token)} a) (holds: a → Prop) (gives: Gives p holds): Fair p holds :=
  Parse.readsInOfReads gives

theorem fairSkip: Fair (() => skip()) (skipped => True) := fairOf _ _ givesSkip

theorem fairMark: Fair (() => Parse.mark()) ((at: Parse.Mark (Parse.Located Token)) => True) := fairOf _ _ givesMark

-- A token's comments, as the tree keeps them.

theorem fineAbove ∀ (trivia: List Trivia) (fine: FineTrivia trivia): FineAbove (ownLineComments trivia) :=
  match trivia, fine with
    | [], _ => rfl
    | [OwnLine comment, ..rest], Both isComment others => Both isComment (fineAbove rest others)
    | [BlankLine, ..rest], others => fineAbove rest others

theorem fineAfter ∀ (trailing: Option (Parse.Located Comment))
    (fine: FineTrailing trailing):
    FineAfter (trailing.map (comment => comment.value)) :=
  match trailing, fine with
    | None, _ => rfl
    | Some comment, isComment => isComment

--| The comments the tree keeps of a good token are comments.
theorem fineComments ∀ (layout: Layout) (token: Parse.Located Token) (good: Good token): Fine (layout.comments token) :=
  match layout with
    | InBrackets => Both (fineAbove token.value.above good.right.left) (fineAfter token.value.trailing good.right.right)
    | InStatement column start =>
      match same: token.offset == start with
        | True => Both rfl (fineAfter token.value.trailing good.right.right)
        | False => Both (fineAbove token.value.above good.right.left) (fineAfter token.value.trailing good.right.right)

theorem selectedComments ∀ (layout: Layout) (select: Kind → Option a) (token: Parse.Located Token) (comments: Comments)
    (selected: selectComments layout select token = Some comments):
    comments = layout.comments token :=
  match allowed: layout.allows token with
    | True =>
      match found: select token.value.kind with
        | Some value => Eq.sym (Option.someInjective selected)

--| A sign's comments are comments.
theorem fairSign ∀ (layout: Layout) (what: Text) (wanted: Punctuation): Fair (() => sign layout what wanted) Fine :=
  Parse.readsWeaken (Parse.readsOneEvery what (selectComments layout (signIs wanted))) (taken value found =>
    match found with
      | Witness token (Both single (Both good selected)) =>
        rewrite selectedComments layout (signIs wanted) token value selected in fineComments layout token good)

theorem fairKeyword ∀ (layout: Layout) (wanted: Keyword): Fair (() => keyword layout wanted) Fine :=
  Parse.readsWeaken
    (Parse.readsOneEvery "'${wanted.spelling}'" (selectComments layout (keywordIs wanted)))
    (taken value found =>
      match found with
        | Witness token (Both single (Both good selected)) =>
          rewrite selectedComments layout (keywordIs wanted) token value selected in fineComments layout token good)

--| A name and its comments, as the tree keeps them.
def FineNamed (named: (Text, Comments)): Prop := IsName named.fst ∧ Fine named.snd

theorem selectedName ∀ (layout: Layout) (token: Parse.Located Token) (named: (Text, Comments))
    (goodKind: GoodKind token.value.kind)
    (fine: Fine (layout.comments token))
    (selected: selectWithComments layout nameOf token = Some named):
    FineNamed named :=
  match allowed: layout.allows token with
    | True =>
      match kind: token.value.kind with
        | Name text => rewrite <- Option.someInjective selected in Both goodKind fine

theorem fairName ∀ (layout: Layout): Fair (() => name layout) FineNamed :=
  Parse.readsWeaken (Parse.readsOneEvery "a name" (selectWithComments layout nameOf)) (taken value found =>
    match found with
      | Witness token (Both single (Both good selected)) =>
        selectedName layout token value good.left (fineComments layout token good) selected)

theorem fairSignInBrackets ∀ (what: Text) (wanted: Punctuation):
    Fair (() => signInBrackets what wanted) (Perhaps Fine) :=
  Parse.readsInOfRuns (total state value after fine honest h =>
    match e: state.at.rest with
      | [] =>
        fairOf _ _
          (givesNoted (Parse.Problem.Expected what) None (Perhaps Fine) rfl)
          state.at
          fine
          total
          state
          value
          after
          rfl
          honest
          h
      | [token, ..later] =>
        match isSign: (signIs wanted token.value.kind).isSome with
          | False =>
            fairOf _ _
              (givesNoted (Parse.Problem.Expected what) None (Perhaps Fine) rfl)
              state.at
              fine
              total
              state
              value
              after
              rfl
              honest
              h
          | True =>
            fairThen
              (() => skip())
              (skipped => Some (Layout.comments InBrackets token))
              (skipped => True)
              (Perhaps Fine)
              fairSkip
              (skipped holds => fairDone _ (Perhaps Fine) (fineComments InBrackets token fine.holds.left))
              state.at
              fine
              total
              state
              value
              after
              rfl
              honest
              h)

-- Items.

theorem lexicalItemsAppend ∀ (front: List Item) (last: Item)
    (lexical: LexicalItems front)
    (lastLexical: Lexical last.value)
    (lastFine: Fine last.comma):
    LexicalItems (front ++ [last]) :=
  match front, lexical, last, lastLexical, lastFine with
    | [], lexical, { value, comma }, lastLexical, lastFine => Both lastLexical (Both lastFine rfl)
    | [{ value, comma }, ..rest], Both valueLexical (Both commaFine restLexical), last, lastLexical, lastFine =>
      Both valueLexical (Both commaFine (lexicalItemsAppend rest last restLexical lastLexical lastFine))

theorem lexicalItemsReverse ∀ (found: List Item) (lexical: LexicalItems found): LexicalItems found.reverse :=
  match found, lexical with
    | [], lexical => rfl
    | [{ value, comma }, ..rest], Both valueLexical (Both commaFine restLexical) =>
      rewrite List.reverseCons ({ value, comma }: Item) rest in
        lexicalItemsAppend rest.reverse { value, comma } (lexicalItemsReverse rest restLexical) valueLexical commaFine

--| An item whose value and comma's comments are the lexer's.
def LexicalItem (item: Item): Prop := Lexical item.value ∧ Fine item.comma

theorem fairItem ∀ (self: Layout → {Parse (Parse.Located Token)} Expr)
    (nested: ∀ (inner: Layout) => Fair (() => self inner) Lexical):
    Fair (() => item self) (read => LexicalItem read.fst) :=
  fairThen
    (() => self InBrackets)
    (value =>
      let comma := signInBrackets "','" Comma
      ({ value, comma = comma.getOrElse Comments.none }, comma.isSome))
    Lexical
    (read => LexicalItem read.fst)
    (nested InBrackets)
    (value lexical =>
      fairThen
        (() => signInBrackets "','" Comma)
        (comma => ({ value, comma = comma.getOrElse Comments.none }, comma.isSome))
        (Perhaps Fine)
        (read => LexicalItem read.fst)
        (fairSignInBrackets "','" Comma)
        (comma found =>
          match comma, found with
            | Some comments, fine => fairDone _ _ (Both lexical fine)
            | None, none => fairDone _ _ (Both lexical (Both rfl rfl))))

theorem fairItemsFrom ∀ (self: Layout → {Parse (Parse.Located Token)} Expr)
    (nested: ∀ (inner: Layout) => Fair (() => self inner) Lexical)
    (fuel: Nat) (found: List Item)
    (lexical: LexicalItems found):
    Fair (() => itemsFrom fuel self found) LexicalItems :=
  match fuel with
    | Zero => fairDone [] LexicalItems rfl
    | Succ more =>
      fairThen
        (() => item self)
        (itemsAfter more self found)
        (read => LexicalItem read.fst)
        LexicalItems
        (fairItem self nested)
        (read itemLexical =>
          match read, itemLexical with
            | ({ value, comma }, True), Both valueLexical commaFine =>
              fairItemsFrom self nested more [{ value, comma }, ..found] (Both valueLexical (Both commaFine lexical))
            | ({ value, comma }, False), Both valueLexical commaFine =>
              fairDone _ LexicalItems
                (lexicalItemsReverse [{ value, comma }, ..found] (Both valueLexical (Both commaFine lexical))))

--| Items and the closing bracket's comments, all the lexer's.
def LexicalList (found: (List Item, Comments)): Prop := LexicalItems found.fst ∧ Fine found.snd

--| `items` gives items whose texts are the lexer's, when the nested
--| parser does.
theorem fairItems ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (closer: Punctuation)
    (nested: ∀ (inner: Layout) => Fair (() => self inner) Lexical):
    Fair (() => items self closer) LexicalList :=
  Parse.readsThen (fairSignInBrackets "'${closer.spelling}'" closer) (firstRead closed facts =>
    match closed, facts with
      | Some close, fine => Parse.readsDone ([], close) _ (Both rfl fine)
      | None, none =>
        fairThen
          (() => Parse.mark())
          (at =>
            let found := itemsFrom at.left self []
            let close := sign InBrackets "'${closer.spelling}'" closer
            (found, close))
          (at => True)
          LexicalList
          fairMark
          (at marked =>
            fairThen
              (() => itemsFrom at.left self [])
              (found =>
                let close := sign InBrackets "'${closer.spelling}'" closer
                (found, close))
              LexicalItems
              LexicalList
              (fairItemsFrom self nested at.left [] rfl)
              (found lexical =>
                fairThen
                  (() => sign InBrackets "'${closer.spelling}'" closer)
                  (close => (found, close))
                  Fine
                  LexicalList
                  (fairSign InBrackets "'${closer.spelling}'" closer)
                  (close fine => fairDone _ LexicalList (Both lexical fine)))))

-- Atoms and their calls and fields.

theorem fairExpected ∀ (what: Text) (holds: a → Prop): Fair (() => (Parse.expected what: a)) holds :=
  fairOf _ _ (givesExpected what holds)

theorem fairAtomOf ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (comments: Comments) (kind: Kind)
    (nested: ∀ (inner: Layout) => Fair (() => self inner) Lexical)
    (fine: Fine comments)
    (goodKind: GoodKind kind):
    Fair (() => atomOf self comments kind) Lexical :=
  match kind, goodKind with
    | Name text, isName =>
      fairThen (() => skip()) (skipped => Var text comments) (skipped => True) Lexical fairSkip (skipped done =>
        fairDone _ Lexical (Both isName fine))
    | Number digits, isDigits =>
      fairThen
        (() => skip())
        (skipped => NumberLiteral digits comments)
        (skipped => True)
        Lexical
        fairSkip
        (skipped done => fairDone _ Lexical (Both isDigits fine))
    | Str written, isString =>
      fairThen
        (() => skip())
        (skipped => StringLiteral written comments)
        (skipped => True)
        Lexical
        fairSkip
        (skipped done => fairDone _ Lexical (Both isString fine))
    | Sign OpenParen, _ =>
      fairThen
        (() => skip())
        (skipped =>
          let inner := self InBrackets
          let close := sign InBrackets "')'" CloseParen
          Bracketed comments inner close)
        (skipped => True)
        Lexical
        fairSkip
        (skipped done =>
          fairThen
            (() => self InBrackets)
            (inner =>
              let close := sign InBrackets "')'" CloseParen
              Bracketed comments inner close)
            Lexical
            Lexical
            (nested InBrackets)
            (inner lexical =>
              fairThen
                (() => sign InBrackets "')'" CloseParen)
                (close => Bracketed comments inner close)
                Fine
                Lexical
                (fairSign InBrackets "')'" CloseParen)
                (close closeFine => fairDone _ Lexical (Both fine (Both lexical closeFine)))))
    | Sign OpenSquare, _ => Parse.readsThen fairSkip (skipRead skipped done =>
      Parse.readsThen (fairItems self CloseSquare nested) (itemsRead pair lexical =>
        match pair, lexical with
          | (found, close), Both itemsLexical closeFine =>
            Parse.readsDone (ListLiteral comments found close) _ (Both fine (Both itemsLexical closeFine))))
    | Sign CloseParen, _ => fairExpected "an expression" Lexical
    | Sign CloseSquare, _ => fairExpected "an expression" Lexical
    | Sign Comma, _ => fairExpected "an expression" Lexical
    | Sign Dot, _ => fairExpected "an expression" Lexical
    | Sign Defines, _ => fairExpected "an expression" Lexical
    | Reserved keyword, _ => fairExpected "an expression" Lexical
    | Op operator, _ => fairExpected "an expression" Lexical
    | Stray text, _ => fairExpected "an expression" Lexical

theorem fairAtom ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Fair (() => self inner) Lexical):
    Fair (() => atom self layout) Lexical :=
  Parse.readsInOfRuns (total state value after fine honest h =>
    match e: state.at.rest with
      | [token, ..later] =>
        match allowed: layout.allows token with
          | True =>
            fairAtomOf self
              (layout.comments token)
              token.value.kind
              nested
              (fineComments layout token fine.holds.left)
              fine.holds.left.left
              state.at
              fine
              total
              state
              value
              after
              rfl
              honest
              h)

theorem fairCallAfter ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (target: Expr) (open: Comments)
    (nested: ∀ (inner: Layout) => Fair (() => self inner) Lexical)
    (lexical: Lexical target)
    (fine: Fine open):
    Fair (() => callAfter self target open) Lexical :=
  Parse.readsThen fairSkip (skipRead skipped done =>
    Parse.readsThen (fairItems self CloseParen nested) (itemsRead pair itemsLexical =>
      match pair, itemsLexical with
        | (arguments, close), Both argumentsLexical closeFine =>
          Parse.readsDone
            (Call target open arguments close) _
            (Both lexical (Both fine (Both argumentsLexical closeFine)))))

theorem fairFieldAfter ∀ (layout: Layout) (target: Expr) (dot: Comments)
    (lexical: Lexical target)
    (fine: Fine dot):
    Fair (() => fieldAfter layout target dot) Lexical :=
  Parse.readsThen fairSkip (skipRead skipped done =>
    Parse.readsThen (fairName layout) (nameRead pair named =>
      match pair, named with
        | (text, nameComments), Both isName nameFine =>
          Parse.readsDone (Field target dot text nameComments) _ (Both lexical (Both fine (Both isName nameFine)))))

--| Where `suffixesFrom` stops: it notes what it expected and gives the
--| target.
theorem fairSuffixesStop ∀ (target: Expr)
    (lexical: Lexical target):
    Fair
      (() =>
        Parse.note (Parse.Problem.Expected "'('")
        Parse.note (Parse.Problem.Expected "'.'")
        target)
      Lexical :=
  fairThen
    (() => Parse.note (Parse.Problem.Expected "'('"))
    (noted =>
      Parse.note (Parse.Problem.Expected "'.'")
      target)
    (noted => True)
    Lexical
    (Parse.readsInOfReads
      (Parse.readsWeaken (Parse.readsNote (Parse.Problem.Expected "'('")) (taken noted none => rfl)))
    (noted done => fairOf _ _ (givesNoted (Parse.Problem.Expected "'.'") target Lexical lexical))

theorem fairSuffixesAfter ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout) (more: Nat)
    (target: Expr) (tried: () → {Parse (Parse.Located Token)} Expr)
    (lexical: Lexical target)
    (fairTried: Fair tried Lexical)
    (fairMore: ∀ (longer: Expr) => Lexical longer → Fair (() => suffixesFrom more self layout longer) Lexical):
    Fair (() => suffixesAfter more self layout target (Parse.optional tried)) Lexical :=
  fairThen
    (() => Parse.optional tried)
    (suffixesAfter more self layout target)
    (Perhaps Lexical)
    Lexical
    (Parse.readsWeaken (Parse.readsOptional fairTried) (taken value maybe =>
      match value, maybe with
        | Some found, proved => proved
        | None, none => rfl))
    (longer found =>
      match longer, found with
        | Some longer, found => fairMore longer found
        | None, found => fairDone target Lexical lexical)

--| An atom's calls and fields keep the lexer's texts.
theorem fairSuffixes ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Fair (() => self inner) Lexical)
    (fuel: Nat) (target: Expr)
    (lexical: Lexical target):
    Fair (() => suffixesFrom fuel self layout target) Lexical :=
  match fuel with
    | Zero => Parse.readsInOfRuns (total state value after fine honest h =>
      match e: state.at.rest with
        | [] => fairSuffixesStop target lexical state.at fine total state value after rfl honest h
        | [token, ..later] =>
          match allowed: layout.allows token with
            | False => fairSuffixesStop target lexical state.at fine total state value after rfl honest h
            | True =>
              let stop := fairSuffixesStop target lexical state.at fine total state value after rfl honest
              match kind: token.value.kind with
                | Sign OpenParen => stop h
                | Sign Dot => stop h
                | Sign CloseParen => stop h
                | Sign OpenSquare => stop h
                | Sign CloseSquare => stop h
                | Sign Comma => stop h
                | Sign Defines => stop h
                | Name text => stop h
                | Number digits => stop h
                | Str written => stop h
                | Reserved keyword => stop h
                | Op operator => stop h
                | Stray text => stop h)
    | Succ more => Parse.readsInOfRuns (total state value after fine honest h =>
      match e: state.at.rest with
        | [] => fairSuffixesStop target lexical state.at fine total state value after rfl honest h
        | [token, ..later] =>
          let commentsFine: Fine (layout.comments token) := fineComments layout token fine.holds.left
          match allowed: layout.allows token with
            | False => fairSuffixesStop target lexical state.at fine total state value after rfl honest h
            | True =>
              let stop := fairSuffixesStop target lexical state.at fine total state value after rfl honest
              let call :=
                fairSuffixesAfter self layout more target
                  (() => callAfter self target (layout.comments token))
                  lexical
                  (fairCallAfter self target (layout.comments token) nested lexical commentsFine)
                  (longer longerLexical => fairSuffixes self layout nested more longer longerLexical)
                  state.at
                  fine
                  total
                  state
                  value
                  after
                  rfl
                  honest
              let field :=
                fairSuffixesAfter self layout more target
                  (() => fieldAfter layout target (layout.comments token))
                  lexical
                  (fairFieldAfter layout target (layout.comments token) lexical commentsFine)
                  (longer longerLexical => fairSuffixes self layout nested more longer longerLexical)
                  state.at
                  fine
                  total
                  state
                  value
                  after
                  rfl
                  honest
              match kind: token.value.kind with
                | Sign OpenParen => call h
                | Sign Dot => field h
                | Sign CloseParen => stop h
                | Sign OpenSquare => stop h
                | Sign CloseSquare => stop h
                | Sign Comma => stop h
                | Sign Defines => stop h
                | Name text => stop h
                | Number digits => stop h
                | Str written => stop h
                | Reserved keyword => stop h
                | Op operator => stop h
                | Stray text => stop h)

theorem fairPostfix ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Fair (() => self inner) Lexical):
    Fair (() => postfix self layout) Lexical :=
  fairThen
    (() => Parse.note (Parse.Problem.Expected "an expression"))
    (noted =>
      let first := atom self layout
      suffixesFrom (Parse.mark().left + 1) self layout first)
    (noted => True)
    Lexical
    (Parse.readsInOfReads
      (Parse.readsWeaken (Parse.readsNote (Parse.Problem.Expected "an expression")) (taken noted none => rfl)))
    (noted done =>
      fairThen
        (() => atom self layout)
        (first => suffixesFrom (Parse.mark().left + 1) self layout first)
        Lexical
        Lexical
        (fairAtom self layout nested)
        (first lexical =>
          fairThen
            (() => Parse.mark())
            (at => suffixesFrom (at.left + 1) self layout first)
            (at => True)
            Lexical
            fairMark
            (at marked => fairSuffixes self layout nested (at.left + 1) first lexical)))

--| `-`s before a postfix expression keep the lexer's texts.
theorem fairNegations ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Fair (() => self inner) Lexical) (fuel: Nat):
    Fair (() => negationsFrom fuel self layout) Lexical :=
  match fuel with
    | Zero => Parse.readsInOfRuns (total state value after fine honest h =>
      fairPostfix self layout nested state.at fine total state value after rfl honest h)
    | Succ more => Parse.readsInOfRuns (total state value after fine honest h =>
      match e: state.at.rest with
        | [] => fairPostfix self layout nested state.at fine total state value after rfl honest h
        | [token, ..later] =>
          match minus: isMinus layout token with
            | False => fairPostfix self layout nested state.at fine total state value after rfl honest h
            | True =>
              fairThen
                (() => skip())
                (skipped => Negate (layout.comments token) (negationsFrom more self layout))
                (skipped => True)
                Lexical
                fairSkip
                (skipped done =>
                  fairThen
                    (() => negationsFrom more self layout)
                    (inner => Negate (layout.comments token) inner)
                    Lexical
                    Lexical
                    (fairNegations self layout nested more)
                    (inner lexical => fairDone _ Lexical (Both (fineComments layout token fine.holds.left) lexical)))
                state.at
                fine
                total
                state
                value
                after
                rfl
                honest
                h)

theorem fairOperand ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Fair (() => self inner) Lexical):
    Fair (() => operand self layout) Lexical :=
  fairThen
    (() => Parse.mark())
    (at => negationsFrom (at.left + 1) self layout)
    (at => True)
    Lexical
    fairMark
    (at marked => fairNegations self layout nested (at.left + 1))

-- Operator chains.

--| What `operatorLevels` finds for a token, if anything: a `Binary` that
--| holds the token's comments.
def OperatorCarries (layout: Layout) (token: Parse.Located Token):
    Option (Nat, Parse.Associativity, Expr → Expr → Expr) → Prop
  | None => True
  | Some (level, associativity, combine) => ∃ (operator: Operator) => combine = Binary operator (layout.comments token)

theorem operatorCarries ∀ (layout: Layout) (token: Parse.Located Token):
    OperatorCarries layout token (Parse.operatorFrom token 0 (operatorLevels layout)) :=
  match operatorOfKinds layout token with
    | Inl none => rewrite none 1, none 2, none 3, none 4, none 5, none 6 in rfl
    | Inr (Witness operator (Both kind allowed)) =>
      rewrite operatorFound layout token operator kind allowed in Witness operator rfl

--| An operator read between two expressions with the lexer's texts makes
--| one: its comments are its token's.
theorem lexicalStep ∀ (layout: Layout) (lowest highest level: Nat) (associativity: Parse.Associativity)
    (combine: Expr → Expr → Expr) (item: Parse.Located Token) (left right: Expr)
    (good: Good item)
    (found: Parse.operatorFrom item 0 (operatorLevels layout) = Some (level, associativity, combine))
    (above: lowest ≤ level)
    (below: level ≤ highest)
    (leftLexical: Lexical left)
    (rightLexical: Lexical right):
    Lexical (combine left right) :=
  let carried := operatorCarries layout item
  let known := rewrite found at carried in carried
  match known with
    | Witness operator isBinary =>
      rewrite isBinary in Both (fineComments layout item good) (Both leftLexical rightLexical)

--| An operator chain keeps the lexer's texts.
theorem fairChain ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Fair (() => self inner) Lexical):
    Fair (() => Parse.operators "an operator" (operatorLevels layout) (() => operand self layout)) Lexical :=
  Parse.readsOperatorsEvery "an operator"
    (operatorLevels layout)
    (() => operand self layout)
    Lexical
    (lowest expr => Lexical expr)
    (lowest highest expr => Lexical expr)
    (fairOperand self layout nested)
    (lowest highest value lexical => lexical)
    (lowest highest value lexical => lexical)
    (lexicalStep layout)

theorem fineCleared ∀ (comments: Comments) (fine: Fine comments): Fine { comments | above = [] } := Both rfl fine.right

--| Clearing the comments above the first token keeps the lexer's texts.
theorem lexicalCleared ∀ (expr: Expr) (lexical: Lexical expr): Lexical expr.withoutFirstAbove :=
  match expr, lexical with
    | Var name comments, Both isName fine => Both isName (fineCleared comments fine)
    | NumberLiteral digits comments, Both isDigits fine => Both isDigits (fineCleared comments fine)
    | StringLiteral written comments, Both isString fine => Both isString (fineCleared comments fine)
    | Bracketed open inner close, Both fine others => Both (fineCleared open fine) others
    | ListLiteral open items close, Both fine others => Both (fineCleared open fine) others
    | Call callee open arguments close, Both lexicalCallee others => Both (lexicalCleared callee lexicalCallee) others
    | Field target dot name nameComments, Both lexicalTarget others => Both (lexicalCleared target lexicalTarget) others
    | Negate minus operand, Both fine others => Both (fineCleared minus fine) others
    | Binary operator sign left right, Both fine (Both lexicalLeft lexicalRight) =>
      Both fine (Both (lexicalCleared left lexicalLeft) lexicalRight)
    | If ifComments condition thenComments whenTrue elseComments whenFalse, Both fine others =>
      Both (fineCleared ifComments fine) others

theorem lexicalHeaded ∀ (layout: Layout) (expr: Expr) (lexical: Lexical expr): Lexical (layout.headed expr) :=
  match layout with
    | InBrackets => lexical
    | InStatement column start => lexicalCleared expr lexical

-- Bodies and blocks.

--| A statement with the lexer's texts that isn't a comment line.
def CodedLexical (line: Statement): Prop := LexicalStatement line ∧ Coded line

theorem fairBare ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Fair (() => self inner) Lexical):
    Fair (() => bareStatement self layout) CodedLexical :=
  fairThen
    (() => self layout)
    (value => Bare (layout.headed value))
    Lexical
    CodedLexical
    (nested layout)
    (value lexical => fairDone _ CodedLexical (Both (lexicalHeaded layout value lexical) rfl))

theorem fairInline ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Fair (() => self inner) Lexical):
    Fair (() => inlineBody self layout) LexicalBody :=
  fairThen
    (() => bareStatement self layout)
    (line => { statements = [{ blankBefore = False, line }] })
    CodedLexical
    LexicalBody
    (fairBare self layout nested)
    (line found => match found with | Both lexical coded => fairDone _ LexicalBody (Both (Both lexical rfl) coded))

theorem lexicalLinesAppend ∀ (front back: List (Spaced Statement))
    (frontLexical: LexicalLines front)
    (backLexical: LexicalLines back):
    LexicalLines (front ++ back) :=
  match front, frontLexical with
    | [], frontLexical => backLexical
    | [{ blankBefore, line }, ..rest], Both lineLexical restLexical =>
      Both lineLexical (lexicalLinesAppend rest back restLexical backLexical)

theorem lexicalNotes ∀ (trivia: List Trivia) (found: (List (Spaced Statement), Bool))
    (fine: FineTrivia trivia)
    (lexical: LexicalLines found.fst):
    LexicalLines (trivia.foldLeft found (noteStep StatementNote)).fst :=
  match trivia, fine with
    | [], _ => lexical
    | [BlankLine, ..rest], others => lexicalNotes rest (noteStep StatementNote found BlankLine) others lexical
    | [OwnLine comment, ..rest], Both isComment others =>
      lexicalNotes rest
        (noteStep StatementNote found (OwnLine comment))
        others
        (lexicalLinesAppend found.fst
          [{ blankBefore = found.snd, line = StatementNote comment }]
          lexical
          (Both isComment rfl))

--| A statement's lines, the notes above it and itself, have the lexer's
--| texts when it has and the trivia above it are the lexer's.
theorem lexicalNoted ∀ (above: List Trivia) (line: Statement)
    (fine: FineTrivia above)
    (lexical: LexicalStatement line):
    LexicalLines (notedStatement above line) :=
  let notesLexical: LexicalLines (spacedNotes StatementNote above).fst := lexicalNotes above ([], False) fine rfl
  match found: spacedNotes StatementNote above with
    | (notes, blankBefore) => lexicalLinesAppend notes [{ blankBefore, line }] notesLexical (Both lexical rfl)

theorem lexicalWithoutFirstBlank ∀ (lines: List (Spaced Statement))
    (lexical: LexicalLines lines):
    LexicalLines (withoutFirstBlank lines) :=
  match lines, lexical with
    | [], lexical => rfl
    | [{ blankBefore, line }, ..rest], Both lineLexical restLexical => Both lineLexical restLexical

--| Lines with the lexer's texts that end in a statement.
def ClosedLexical (lines: List (Spaced Statement)): Prop := LexicalLines lines ∧ ClosedLines lines

def AllLexical: List (List (Spaced Statement)) → Prop
  | [] => True
  | [first, ..rest] => ClosedLexical first ∧ AllLexical rest

theorem eachLexical ∀ (values: List (List (Spaced Statement))) (taken: List (Parse.Located Token))
    (each: Parse.Each (read lines => ClosedLexical lines) taken values):
    AllLexical values :=
  match values, each with
    | [], each => rfl
    | [first, ..rest], Witness firstRead (Witness restRead (Both split (Both holds more))) =>
      Both holds (eachLexical rest restRead more)

theorem lexicalConcat ∀ (groups: List (List (Spaced Statement))) (all: AllLexical groups): LexicalLines groups.concat :=
  match groups, all with
    | [], all => rfl
    | [first, ..rest], Both (Both firstLexical _) restLexical =>
      lexicalLinesAppend first rest.concat firstLexical (lexicalConcat rest restLexical)

theorem closedGroups ∀ (first: List (Spaced Statement)) (rest: List (List (Spaced Statement)))
    (all: AllLexical [first, ..rest]):
    ClosedLines [first, ..rest].concat :=
  match rest, all with
    | [], Both (Both _ closed) _ => rewrite List.appendNil first in closed
    | [second, ..more], Both _ others => closedAppend first [second, ..more].concat (closedGroups second more others)

theorem fairStatementLine ∀ (self: Layout → {Parse (Parse.Located Token)} Expr)
    (nested: ∀ (inner: Layout) => Fair (() => self inner) Lexical) (fuel: Nat)
    (fairBody: ∀ (inner: Layout) => Fair (() => bodyFuel fuel self inner) LexicalBody)
    (layout: Layout) (first: Parse.Located Token) (kind: Kind)
    (fine: Fine (layout.comments first)):
    Fair (() => statementLine fuel self layout first kind) CodedLexical :=
  match kind with
    | Reserved LetKeyword => Parse.readsThen fairSkip (skipRead skipped done =>
      Parse.readsThen (fairName layout) (nameRead pair named =>
        match pair, named with
          | (bound, nameComments), Both isName nameFine =>
            fairThen
              (() => sign layout "'='" Defines)
              (equals => Let (layout.comments first) bound nameComments equals (bodyFuel fuel self layout))
              Fine
              CodedLexical
              (fairSign layout "'='" Defines)
              (equals equalsFine =>
                fairThen
                  (() => bodyFuel fuel self layout)
                  (inner => Let (layout.comments first) bound nameComments equals inner)
                  LexicalBody
                  CodedLexical
                  (fairBody layout)
                  (inner lexical =>
                    fairDone _ CodedLexical
                      (Both (Both fine (Both isName (Both nameFine (Both equalsFine lexical)))) rfl)))))
    | Reserved FnKeyword => fairBare self layout nested
    | Reserved IfKeyword => fairBare self layout nested
    | Reserved ThenKeyword => fairBare self layout nested
    | Reserved ElseKeyword => fairBare self layout nested
    | Name text => fairBare self layout nested
    | Number digits => fairBare self layout nested
    | Str written => fairBare self layout nested
    | Sign punctuation => fairBare self layout nested
    | Op operator => fairBare self layout nested
    | Stray text => fairBare self layout nested

theorem fairStatement ∀ (self: Layout → {Parse (Parse.Located Token)} Expr)
    (nested: ∀ (inner: Layout) => Fair (() => self inner) Lexical) (fuel: Nat)
    (fairBody: ∀ (inner: Layout) => Fair (() => bodyFuel fuel self inner) LexicalBody) (column: Nat):
    Fair (() => statement fuel self column) ClosedLexical :=
  Parse.readsInOfRuns (total state value after fine honest h =>
    match e: state.at.rest with
      | [first, ..later] =>
        match starts: first.value.startsLine && first.value.column == column with
          | True =>
            fairThen
              (() => statementLine fuel self (InStatement column first.offset) first first.value.kind)
              (line => notedStatement first.value.above line)
              CodedLexical
              ClosedLexical
              (fairStatementLine self nested fuel fairBody
                (InStatement column first.offset)
                first
                first.value.kind
                (fineComments (InStatement column first.offset) first fine.holds.left))
              (line found =>
                match found with
                  | Both lexical coded =>
                    fairDone _ ClosedLexical
                      (Both
                        (lexicalNoted first.value.above line fine.holds.left.right.left lexical)
                        (closedNoted first.value.above line coded)))
              state.at
              fine
              total
              state
              value
              after
              rfl
              honest
              h)

theorem fairBlock ∀ (self: Layout → {Parse (Parse.Located Token)} Expr)
    (nested: ∀ (inner: Layout) => Fair (() => self inner) Lexical) (fuel: Nat)
    (fairBody: ∀ (inner: Layout) => Fair (() => bodyFuel fuel self inner) LexicalBody) (column: Nat):
    Fair (() => block fuel self column) LexicalBody :=
  fairThen
    (() => Parse.many1 (() => statement fuel self column))
    (lines => { statements = lines.toList.concat |> withoutFirstBlank })
    (lines => AllLexical lines.toList)
    LexicalBody
    (Parse.readsWeaken
      (Parse.readsMany1
        (() => statement fuel self column)
        (taken lines => ClosedLexical lines)
        (fairStatement self nested fuel fairBody column))
      (taken lines each => eachLexical lines.toList taken each))
    (lines all =>
      fairDone _ LexicalBody
        (Both
          (lexicalWithoutFirstBlank lines.toList.concat (lexicalConcat lines.toList all))
          (closedWithoutFirstBlank lines.toList.concat (closedGroups lines.head lines.tail all))))

--| A body, a block or one expression, keeps the lexer's texts and ends
--| in a statement.
theorem fairBodyFuel ∀ (self: Layout → {Parse (Parse.Located Token)} Expr)
    (nested: ∀ (inner: Layout) => Fair (() => self inner) Lexical)
    (fuel: Nat) (layout: Layout):
    Fair (() => bodyFuel fuel self layout) LexicalBody :=
  match fuel with
    | Zero => Parse.readsInOfRuns (total state value after fine honest h => Void.exfalso (Result.errNotOk h))
    | Succ more => Parse.readsInOfRuns (total state value after fine honest h =>
      match layout with
        | InBrackets => fairInline self InBrackets nested state.at fine total state value after rfl honest h
        | InStatement column start =>
          match e: state.at.rest with
            | [] => fairInline self (InStatement column start) nested state.at fine total state value after rfl honest h
            | [token, ..later] =>
              match deeper: token.value.startsLine && token.value.column > column with
                | False =>
                  fairInline self (InStatement column start) nested state.at fine total state value after rfl honest h
                | True =>
                  fairBlock self nested more
                    (inner => fairBodyFuel self nested more inner)
                    token.value.column
                    state.at
                    fine
                    total
                    state
                    value
                    after
                    rfl
                    honest
                    h)

theorem fairBody ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Fair (() => self inner) Lexical):
    Fair (() => body self layout) LexicalBody :=
  fairThen
    (() => Parse.mark())
    (at => bodyFuel (at.left + 1) self layout)
    (at => True)
    LexicalBody
    fairMark
    (at marked => fairBodyFuel self nested (at.left + 1) layout)

-- `if`, and the expression parser.

theorem fairElse ∀ (layout: Layout): Fair (() => elseKeyword layout) Fine :=
  Parse.readsInOfRuns (total state value after fine honest h =>
    match e: state.at.rest with
      | [] => fairKeyword layout ElseKeyword state.at fine total state value after rfl honest h
      | [token, ..later] =>
        match isElse: (keywordIs ElseKeyword token.value.kind).isSome with
          | False => fairKeyword layout ElseKeyword state.at fine total state value after rfl honest h
          | True =>
            match allowed: layout.allowsElse token with
              | True =>
                fairThen
                  (() => skip())
                  (skipped => layout.comments token)
                  (skipped => True)
                  Fine
                  fairSkip
                  (skipped done => fairDone _ Fine (fineComments layout token fine.holds.left))
                  state.at
                  fine
                  total
                  state
                  value
                  after
                  rfl
                  honest
                  h)

--| One level of the expression parser keeps the lexer's texts, given
--| that `self` does for the expressions nested in it.
theorem fairExpressionRule ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Fair (() => self inner) Lexical):
    Fair (() => expressionRule self layout) Lexical :=
  Parse.readsInOfRuns (total state value after fine honest h =>
    match e: state.at.rest with
      | [] => fairChain self layout nested state.at fine total state value after rfl honest h
      | [token, ..later] =>
        let ifFine: Fine (layout.comments token) := fineComments layout token fine.holds.left
        match found: isIf layout token with
          | False => fairChain self layout nested state.at fine total state value after rfl honest h
          | True =>
            fairThen
              (() => skip())
              (skipped =>
                let condition := self layout
                let thenComments := keyword layout ThenKeyword
                let whenTrue := body self layout
                let elseComments := elseKeyword layout
                let whenFalse := body self layout
                If (layout.comments token) condition thenComments whenTrue elseComments whenFalse)
              (skipped => True)
              Lexical
              fairSkip
              (skipped done =>
                fairThen
                  (() => self layout)
                  (condition =>
                    let thenComments := keyword layout ThenKeyword
                    let whenTrue := body self layout
                    let elseComments := elseKeyword layout
                    let whenFalse := body self layout
                    If (layout.comments token) condition thenComments whenTrue elseComments whenFalse)
                  Lexical
                  Lexical
                  (nested layout)
                  (condition conditionLexical =>
                    fairThen
                      (() => keyword layout ThenKeyword)
                      (thenComments =>
                        let whenTrue := body self layout
                        let elseComments := elseKeyword layout
                        let whenFalse := body self layout
                        If (layout.comments token) condition thenComments whenTrue elseComments whenFalse)
                      Fine
                      Lexical
                      (fairKeyword layout ThenKeyword)
                      (thenComments thenFine =>
                        fairThen
                          (() => body self layout)
                          (whenTrue =>
                            let elseComments := elseKeyword layout
                            let whenFalse := body self layout
                            If (layout.comments token) condition thenComments whenTrue elseComments whenFalse)
                          LexicalBody
                          Lexical
                          (fairBody self layout nested)
                          (whenTrue trueLexical =>
                            fairThen
                              (() => elseKeyword layout)
                              (elseComments =>
                                let whenFalse := body self layout
                                If (layout.comments token) condition thenComments whenTrue elseComments whenFalse)
                              Fine
                              Lexical
                              (fairElse layout)
                              (elseComments elseFine =>
                                fairThen
                                  (() => body self layout)
                                  (whenFalse =>
                                    If (layout.comments token) condition thenComments whenTrue elseComments whenFalse)
                                  LexicalBody
                                  Lexical
                                  (fairBody self layout nested)
                                  (whenFalse falseLexical =>
                                    fairDone _ Lexical
                                      (Both ifFine
                                        (Both conditionLexical
                                          (Both thenFine (Both trueLexical (Both elseFine falseLexical)))))))))))
              state.at
              fine
              total
              state
              value
              after
              rfl
              honest
              h)

--| Every expression the parser gives from good tokens has the lexer's
--| texts: each name, number, string and comment in it is a token's, and
--| each body of an `if` ends in a statement.
theorem fairExpression ∀ (layout: Layout): Fair (() => expression layout) Lexical :=
  Parse.readsRecursiveWith expressionRule
    (inner taken expr => Lexical expr)
    (self nested argument => fairExpressionRule self argument nested)
    layout

-- Declarations and the file.

--| A comma's comments and the parameter after it.
def FineStep (step: (Comments, (Text, Comments))): Prop := Fine step.fst ∧ FineNamed step.snd

def AllSteps: List (Comments, (Text, Comments)) → Prop
  | [] => True
  | [step, ..rest] => FineStep step ∧ AllSteps rest

theorem eachSteps ∀ (values: List (Comments, (Text, Comments))) (taken: List (Parse.Located Token))
    (each: Parse.Each (read step => FineStep step) taken values):
    AllSteps values :=
  match values, each with
    | [], each => rfl
    | [first, ..rest], Witness firstRead (Witness restRead (Both split (Both holds more))) =>
      Both holds (eachSteps rest restRead more)

theorem fairParameterStep: Fair parameterStep FineStep :=
  fairThen
    (() => sign InBrackets "','" Comma)
    (comma =>
      let named := name InBrackets
      (comma, named))
    Fine
    FineStep
    (fairSign InBrackets "','" Comma)
    (comma commaFine =>
      fairThen
        (() => name InBrackets)
        (named => (comma, named))
        FineNamed
        FineStep
        (fairName InBrackets)
        (named isNamed => fairDone _ FineStep (Both commaFine isNamed)))

--| A first parameter and the commas and parameters after it.
def FineList (found: ((Text, Comments), List (Comments, (Text, Comments)))): Prop :=
  FineNamed found.fst ∧ AllSteps found.snd

theorem fairParameterList: Fair parameterList FineList :=
  fairThen
    (() => name InBrackets)
    (first =>
      let others := Parse.many parameterStep
      (first, others))
    FineNamed
    FineList
    (fairName InBrackets)
    (first named =>
      fairThen
        (() => Parse.many parameterStep)
        (others => (first, others))
        AllSteps
        FineList
        (Parse.readsWeaken
          (Parse.readsMany parameterStep (taken step => FineStep step) fairParameterStep)
          (taken others each => eachSteps others taken each))
        (others steps => fairDone _ FineList (Both named steps)))

theorem lexicalWithCommas ∀ (first: (Text, Comments)) (others: List (Comments, (Text, Comments)))
    (named: FineNamed first)
    (steps: AllSteps others):
    LexicalParameters (withCommas first others) :=
  match others, steps with
    | [], _ => Both named.left (Both named.right (Both (Both rfl rfl) rfl))
    | [(comma, next), ..rest], Both (Both commaFine nextNamed) more =>
      Both named.left (Both named.right (Both commaFine (lexicalWithCommas next rest nextNamed more)))

theorem fairParameters: Fair (() => parametersOf (Parse.optional parameterList)) LexicalParameters :=
  fairThen
    (() => Parse.optional parameterList)
    (found => parametersOf found)
    (Perhaps FineList)
    LexicalParameters
    (Parse.readsWeaken (Parse.readsOptional fairParameterList) (taken value maybe =>
      match value, maybe with
        | Some found, proved => proved
        | None, none => rfl))
    (found listed =>
      match found, listed with
        | None, _ => fairDone _ LexicalParameters rfl
        | Some (first, others), Both named steps =>
          fairDone _ LexicalParameters (lexicalWithCommas first others named steps))

theorem fairFunctionLine ∀ (layout: Layout) (first: Parse.Located Token)
    (fine: Fine (layout.comments first)):
    Fair (() => functionLine layout first) LexicalDeclaration :=
  Parse.readsThen fairSkip (skipRead skipped done =>
    Parse.readsThen (fairName layout) (nameRead pair named =>
      match pair, named with
        | (declared, nameComments), Both isName nameFine =>
          fairThen
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
            Fine
            LexicalDeclaration
            (fairSign layout "'('" OpenParen)
            (open openFine =>
              fairThen
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
                LexicalParameters
                LexicalDeclaration
                fairParameters
                (parameters listed =>
                  fairThen
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
                    Fine
                    LexicalDeclaration
                    (fairSign InBrackets "')'" CloseParen)
                    (close closeFine =>
                      fairThen
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
                        Fine
                        LexicalDeclaration
                        (fairSign layout "'='" Defines)
                        (equals equalsFine =>
                          fairThen
                            (() => body expression layout)
                            (inner =>
                              Function (layout.comments first) declared nameComments open parameters close equals inner)
                            LexicalBody
                            LexicalDeclaration
                            (fairBody expression layout fairExpression)
                            (inner lexical =>
                              fairDone _ LexicalDeclaration
                                (Both fine
                                  (Both isName
                                    (Both nameFine
                                      (Both openFine (Both listed (Both closeFine (Both equalsFine lexical))))))))))))))

theorem fairValueLine ∀ (layout: Layout) (first: Parse.Located Token)
    (fine: Fine (layout.comments first)):
    Fair (() => valueLine layout first) LexicalDeclaration :=
  Parse.readsThen fairSkip (skipRead skipped done =>
    Parse.readsThen (fairName layout) (nameRead pair named =>
      match pair, named with
        | (declared, nameComments), Both isName nameFine =>
          fairThen
            (() => sign layout "'='" Defines)
            (equals => Value (layout.comments first) declared nameComments equals (body expression layout))
            Fine
            LexicalDeclaration
            (fairSign layout "'='" Defines)
            (equals equalsFine =>
              fairThen
                (() => body expression layout)
                (inner => Value (layout.comments first) declared nameComments equals inner)
                LexicalBody
                LexicalDeclaration
                (fairBody expression layout fairExpression)
                (inner lexical =>
                  fairDone _ LexicalDeclaration (Both fine (Both isName (Both nameFine (Both equalsFine lexical))))))))

theorem fairDeclarationLine ∀ (layout: Layout) (first: Parse.Located Token)
    (fine: Fine (layout.comments first)):
    Fair (() => declarationLine layout first) LexicalDeclaration :=
  Parse.readsInOfRuns (total state value after fits honest h =>
    match kind: first.value.kind with
      | Reserved FnKeyword => fairFunctionLine layout first fine state.at fits total state value after rfl honest h
      | Reserved LetKeyword => fairValueLine layout first fine state.at fits total state value after rfl honest h)

theorem lexicalDeclarationsAppend ∀ (front back: List (Spaced Declaration))
    (frontLexical: LexicalDeclarations front)
    (backLexical: LexicalDeclarations back):
    LexicalDeclarations (front ++ back) :=
  match front, frontLexical with
    | [], frontLexical => backLexical
    | [{ blankBefore, line }, ..rest], Both lineLexical restLexical =>
      Both lineLexical (lexicalDeclarationsAppend rest back restLexical backLexical)

theorem lexicalDeclarationNotes ∀ (trivia: List Trivia) (found: (List (Spaced Declaration), Bool))
    (fine: FineTrivia trivia)
    (lexical: LexicalDeclarations found.fst):
    LexicalDeclarations (trivia.foldLeft found (noteStep DeclarationNote)).fst :=
  match trivia, fine with
    | [], _ => lexical
    | [BlankLine, ..rest], others =>
      lexicalDeclarationNotes rest (noteStep DeclarationNote found BlankLine) others lexical
    | [OwnLine comment, ..rest], Both isComment others =>
      lexicalDeclarationNotes rest
        (noteStep DeclarationNote found (OwnLine comment))
        others
        (lexicalDeclarationsAppend found.fst
          [{ blankBefore = found.snd, line = DeclarationNote comment }]
          lexical
          (Both isComment rfl))

theorem lexicalNotedDeclaration ∀ (above: List Trivia) (line: Declaration)
    (fine: FineTrivia above)
    (lexical: LexicalDeclaration line):
    LexicalDeclarations (notedDeclaration above line) :=
  let notesLexical: LexicalDeclarations (spacedNotes DeclarationNote above).fst :=
    lexicalDeclarationNotes above ([], False) fine rfl
  match found: spacedNotes DeclarationNote above with
    | (notes, blankBefore) => lexicalDeclarationsAppend notes [{ blankBefore, line }] notesLexical (Both lexical rfl)

theorem lexicalDeclarationsWithoutFirstBlank ∀ (lines: List (Spaced Declaration))
    (lexical: LexicalDeclarations lines):
    LexicalDeclarations (withoutFirstBlank lines) :=
  match lines, lexical with
    | [], lexical => rfl
    | [{ blankBefore, line }, ..rest], Both lineLexical restLexical => Both lineLexical restLexical

def AllLexicalDeclarations: List (List (Spaced Declaration)) → Prop
  | [] => True
  | [first, ..rest] => LexicalDeclarations first ∧ AllLexicalDeclarations rest

theorem eachLexicalDeclarations ∀ (values: List (List (Spaced Declaration))) (taken: List (Parse.Located Token))
    (each: Parse.Each (read lines => LexicalDeclarations lines) taken values):
    AllLexicalDeclarations values :=
  match values, each with
    | [], each => rfl
    | [first, ..rest], Witness firstRead (Witness restRead (Both split (Both holds more))) =>
      Both holds (eachLexicalDeclarations rest restRead more)

theorem lexicalDeclarationsConcat ∀ (groups: List (List (Spaced Declaration)))
    (all: AllLexicalDeclarations groups):
    LexicalDeclarations groups.concat :=
  match groups, all with
    | [], all => rfl
    | [first, ..rest], Both firstLexical restLexical =>
      lexicalDeclarationsAppend first rest.concat firstLexical (lexicalDeclarationsConcat rest restLexical)

theorem fairDeclaration: Fair declaration LexicalDeclarations :=
  Parse.readsInOfRuns (total state value after fine honest h =>
    match e: state.at.rest with
      | [first, ..later] =>
        match starts: first.value.startsLine && first.value.column == 0 with
          | True =>
            fairThen
              (() => declarationLine (InStatement 0 first.offset) first)
              (parsed => notedDeclaration first.value.above parsed)
              LexicalDeclaration
              LexicalDeclarations
              (fairDeclarationLine
                (InStatement 0 first.offset)
                first
                (fineComments (InStatement 0 first.offset) first fine.holds.left))
              (parsed lexical =>
                fairDone _ LexicalDeclarations
                  (lexicalNotedDeclaration first.value.above parsed fine.holds.left.right.left lexical))
              state.at
              fine
              total
              state
              value
              after
              rfl
              honest
              h)

theorem lexicalFileOf ∀ (declarations: List (Spaced Declaration)) (endTrivia: List Trivia)
    (fine: FineTrivia endTrivia)
    (lexical: LexicalDeclarations declarations):
    LexicalFile (fileOf declarations endTrivia) :=
  let notesLexical: LexicalDeclarations (spacedNotes DeclarationNote endTrivia).fst :=
    lexicalDeclarationNotes endTrivia ([], False) fine rfl
  match found: spacedNotes DeclarationNote endTrivia with
    | (endNotes, blank) =>
      lexicalDeclarationsWithoutFirstBlank
        (declarations ++ endNotes)
        (lexicalDeclarationsAppend declarations endNotes lexical notesLexical)

theorem fairFileEnd ∀ (declarations: List (Spaced Declaration)) (endTrivia: List Trivia)
    (fine: FineTrivia endTrivia)
    (lexical: LexicalDeclarations declarations):
    Fair (() => fileEnd declarations endTrivia) LexicalFile :=
  Parse.readsInOfRuns (total state value after fits honest h =>
    match e: state.at.rest with
      | [] =>
        fairDone
          (fileOf declarations endTrivia)
          LexicalFile
          (lexicalFileOf declarations endTrivia fine lexical)
          state.at
          fits
          total
          state
          value
          after
          rfl
          honest
          h
      | [token, ..later] =>
        match indented: token.value.startsLine && token.value.column > 0 with
          | False =>
            fairDone
              (fileOf declarations endTrivia)
              LexicalFile
              (lexicalFileOf declarations endTrivia fine lexical)
              state.at
              fits
              total
              state
              value
              after
              rfl
              honest
              h)

--| The file the parser gives from good tokens and end trivia has the
--| lexer's texts.
theorem fairSourceFile ∀ (endTrivia: List Trivia)
    (fine: FineTrivia endTrivia):
    Fair (() => sourceFile endTrivia) LexicalFile :=
  fairThen
    (() => Parse.many declaration)
    (found => fileEnd found.concat endTrivia)
    AllLexicalDeclarations
    LexicalFile
    (Parse.readsWeaken
      (Parse.readsMany declaration (taken lines => LexicalDeclarations lines) fairDeclaration)
      (taken found each => eachLexicalDeclarations found taken each))
    (found all => fairFileEnd found.concat endTrivia fine (lexicalDeclarationsConcat found all))

-- From the source.

theorem goodKind ∀ (kind: Kind) (fine: FineKind kind): GoodKind kind := match kind, fine with
  | Name text, isName => isName
  | Number digits, isDigits => isDigits
  | Str written, read => stringReadClosed written read
  | Reserved keyword, _ => rfl
  | Sign punctuation, _ => rfl
  | Op operator, _ => rfl
  | Stray text, _ => rfl

--| The lexer's tokens are good ones.
theorem goodTokens ∀ (tokens: List (Parse.Located Token)) (fine: FineTokens tokens): List.All Good tokens :=
  match tokens, fine with
    | [], _ => ()
    | [token, ..rest], Both (Both kind (Both above trailing)) others =>
      Both (Both (goodKind token.value.kind kind) (Both above trailing)) (goodTokens rest others)

--| What the parser guarantees about its trees' texts: in every file
--| `parse` gives, whatever the source, every name is a word that spells
--| no keyword, every number is digits, every string is closed by its
--| second quote whatever follows, every comment is `--` and the rest of
--| its line, and every body ends in a statement (`LexicalFile`). So the
--| printer's lexing theorems hold of every parsed tree, with no check at
--| run time.
theorem parseLexical ∀ (source: Text) (file: SourceFile) (parsed: parse source = Ok file): LexicalFile file :=
  match lexed: lex source with
    | Ok tokens =>
      match whole: Parse.whole tokens.tokens (() => sourceFile tokens.endTrivia) with
        | Ok found =>
          let same: found = file := Result.okInjective parsed
          let texts := lexTexts source tokens lexed
          rewrite <- same in
            Parse.wholeReadsIn tokens.tokens
              (() => sourceFile tokens.endTrivia)
              (taken value => LexicalFile value)
              found
              (fairSourceFile tokens.endTrivia texts.right)
              { holds = goodTokens tokens.tokens texts.left }
              whole
