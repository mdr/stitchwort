--| The walk for `formatKeepsComments`'s parser half: one lemma per parser
--| function, saying that the value it gives holds the comments of the
--| tokens it read (the specs are in CarryProofs.sw). A function that
--| looks at the next token and then skips it is proved from the mark it
--| looked at (`Parse.readsInPeek`, `skipStarted`, `skipOnto`); the others
--| are chains of `andThen` steps ended by `lastly` or `ontoDone`.

namespace Toy.Fmt.Carry
import Toy.Fmt (..)
import Toy.Fmt.Proofs (OperatorCarries, operatorCarries, selectedComments)
import Toy.Syntax (..)
import Toy.Syntax.Proofs (..)
import Std (And, Bool, Empty, Eq, List, Nat, NonEmptyList, Option, Pair, Parse, Result, Text, Void)

-- Shorthands for the chain lemmas.

--| The last step, where the value is a pure function of what it gave.
theorem lastly ∀ [inv: Parse.Invariant Tok] [p: () → {Parse Tok} a] [f: a → b] [first: a → List Comment]
    [measure: b → List Comment] [extra: b → Prop] [layout: Layout] [before: List Comment → List Comment]
    (readsLast: Parse.ReadsIn inv p (Inner layout first)) (holds: ∀ (v: a) => extra (f v))
    (same: ∀ (v: a) => measure (f v) = before (first v)):
    Parse.ReadsIn inv (() => f (p())) (Onto layout before measure extra) :=
  Parse.readsThen readsLast (read v carried =>
    Parse.readsDone
      (f v) _
      (rewrite List.appendNil read then
        (
          (holds v),
          (past =>
            calc measure (f v)
              _ = before (first v) := same v
              _ = before (allCarried read) := Eq.cong before (carried past))
        )))

--| A whole chain, with nothing more to say of its value.
theorem innerOf ∀ [inv: Parse.Invariant Tok] [p: () → {Parse Tok} a] [measure: a → List Comment] [layout: Layout]
    (onto: Parse.ReadsIn inv p (Onto layout (later => later) measure (found => True))):
    Parse.ReadsIn inv p (Inner layout measure) :=
  Parse.readsWeaken onto (read value both => both.right)

--| A chain whose steps so far add `other`, where `before` is wanted.
theorem ontoBefore ∀ [inv: Parse.Invariant Tok] [p: () → {Parse Tok} a] [measure: a → List Comment] [extra: a → Prop]
    [layout: Layout] [before other: List Comment → List Comment]
    (reads: Parse.ReadsIn inv p (Onto layout other measure extra))
    (same: ∀ (later: List Comment) => other later = before later):
    Parse.ReadsIn inv p (Onto layout before measure extra) :=
  Parse.readsWeaken reads (read value onto =>
    (
      onto.left,
      (past =>
        calc measure value
          _ = other (allCarried read) := onto.right past
          _ = before (allCarried read) := same (allCarried read))
    ))

theorem inBrackets ∀ [inv: Parse.Invariant Tok] [p: () → {Parse Tok} a] [measure: a → List Comment] (layout: Layout)
    (reads: Parse.ReadsIn inv p (Inner InBrackets measure)):
    Parse.ReadsIn inv p (Inner layout measure) :=
  Parse.readsWeaken reads (bracketsInner layout)

theorem innerExpr ∀ [inv: Parse.Invariant Tok] [p: () → {Parse Tok} Expr] (layout: Layout)
    (reads: Parse.ReadsIn inv p (ExprSpec layout)):
    Parse.ReadsIn inv p (Inner layout Expr.comments) :=
  Parse.readsWeaken reads (exprInner layout)

--| `skipStarted` for an expression whose first token is `token`.
theorem skipExpr ∀ [inv: Parse.Invariant Tok] [j: () → {Parse Tok} Expr] (layout: Layout) (start: Parse.Mark Tok)
    (token: Tok) (later: List Tok)
    (fine: Parse.Fits Tok inv [token, ..later])
    (shape: start.rest = [token, ..later])
    (allowed: layout.allows token = True)
    (rest: ∀ (done: ()) => Parse.ReadsIn inv
      (() => j done)
      (Onto layout (more => layout.kept token ++ more) Expr.comments (found =>
        found.firstAbove = (layout.comments token).above))):
    Parse.ReadsAt start (() => j (skip())) (ExprSpec layout) :=
  readsAtWeaken (skipStarted layout start token later fine shape rest) (startedExpr layout token allowed)

--| `skipStarted` for anything else read from its layout's first token.
theorem skipOpened ∀ [inv: Parse.Invariant Tok] [j: () → {Parse Tok} b] [measure: b → List Comment] (layout: Layout)
    (start: Parse.Mark Tok) (token: Tok) (later: List Tok)
    (fine: Parse.Fits Tok inv [token, ..later])
    (shape: start.rest = [token, ..later])
    (rest: ∀ (done: ()) => Parse.ReadsIn inv
      (() => j done)
      (Onto layout (more => layout.kept token ++ more) measure (found => True))):
    Parse.ReadsAt start (() => j (skip())) (Opened layout measure) :=
  readsAtWeaken (skipStarted layout start token later fine shape rest) (startedOpened layout token)

--| `skipStarted` for a token read after its layout's first.
theorem skipInner ∀ [inv: Parse.Invariant Tok] [j: () → {Parse Tok} b] [measure: b → List Comment] (layout: Layout)
    (start: Parse.Mark Tok) (token: Tok) (later: List Tok)
    (fine: Parse.Fits Tok inv [token, ..later])
    (shape: start.rest = [token, ..later])
    (rest: ∀ (done: ()) => Parse.ReadsIn inv
      (() => j done)
      (Onto layout (more => layout.kept token ++ more) measure (found => True))):
    Parse.ReadsAt start (() => j (skip())) (Inner layout measure) :=
  readsAtWeaken (skipStarted layout start token later fine shape rest) (startedInner layout token)

-- Tokens.

theorem innerSign ∀ (layout: Layout) (what: Text) (wanted: Punctuation):
    Parse.ReadsIn Lexer (() => sign layout what wanted) (Inner layout Comments.all) :=
  Parse.readsWeaken (Parse.readsOne what (selectComments layout (signIs wanted))) (taken value found =>
    match found with
      | (token, single, selected) =>
        rewrite single then
          innerOne
            [measure := Comments.all]
            layout
            token
            value
            (Eq.cong Comments.all (selectedComments layout (signIs wanted) token value selected)))

theorem innerKeyword ∀ (layout: Layout) (wanted: Keyword):
    Parse.ReadsIn Lexer (() => keyword layout wanted) (Inner layout Comments.all) :=
  Parse.readsWeaken
    (Parse.readsOne "'${wanted.spelling}'" (selectComments layout (keywordIs wanted)))
    (taken value found =>
      match found with
        | (token, single, selected) =>
          rewrite single then
            innerOne
              [measure := Comments.all]
              layout
              token
              value
              (Eq.cong Comments.all (selectedComments layout (keywordIs wanted) token value selected)))

def namedComments (named: (Text, Comments)): List Comment := named.snd.all

theorem selectedNamed ∀ (layout: Layout) (token: Tok) (named: (Text, Comments))
    (selected: selectWithComments layout nameOf token = Some named):
    named.snd = layout.comments token :=
  match allowed: layout.allows token with
    | True =>
      match kind: token.value.kind with
        | Name text => rewrite <- Option.someInjective selected then byComputing

theorem innerName ∀ (layout: Layout): Parse.ReadsIn Lexer (() => name layout) (Inner layout namedComments) :=
  Parse.readsWeaken (Parse.readsOne "a name" (selectWithComments layout nameOf)) (taken value found =>
    match found with
      | (token, single, selected) =>
        rewrite single then
          innerOne
            [measure := namedComments]
            layout
            token
            value
            (Eq.cong Comments.all (selectedNamed layout token value selected)))

def optionComments: Option Comments → List Comment
  | Some comments => comments.all
  | None => []

--| A note, then a value that holds no comments.
theorem innerNoted ∀ [measure: a → List Comment] (layout: Layout) (problem: Parse.Problem) (x: a)
    (none: measure x = []):
    Parse.ReadsIn Lexer
      (() =>
        Parse.note problem
        x)
      (Inner layout measure) :=
  Parse.readsThen (Parse.readsNote problem) (noted done nothing =>
    Parse.readsDone x _ (rewrite nothing then (past => none)))

--| `signInBrackets` where the sign is next: it is read.
theorem innerSignTaken ∀ (start: Parse.Mark Tok) (token: Tok) (later: List Tok)
    (fine: Parse.Fits Tok Lexer [token, ..later])
    (shape: start.rest = [token, ..later]):
    Parse.ReadsAt start
      (() =>
        skip()
        Some (Layout.comments InBrackets token))
      (Inner InBrackets optionComments) :=
  skipInner InBrackets start token later fine shape (done =>
    ontoDone byComputing (List.appendNil (Layout.kept InBrackets token)).flipped)

--| `signInBrackets` holds the sign's comments if it read it, else none.
--|
--| Proof idea: from the mark where it looks. A sign seen there is the
--| token `skip` reads (`innerSignTaken`); otherwise it only notes what it
--| expected.
theorem innerSignInBrackets ∀ (what: Text) (wanted: Punctuation):
    Parse.ReadsIn Lexer (() => signInBrackets what wanted) (Inner InBrackets optionComments) :=
  Parse.readsInPeek _ _ (start fine =>
    match e: start.rest with
      | [] =>
        innerNoted
          [measure := optionComments]
          InBrackets
          (Parse.Problem.Expected what)
          None
          byComputing
          start
          (rewrite e then fine)
      | [token, ..later] =>
        match isSign: (signIs wanted token.value.kind).isSome with
          | False =>
            innerNoted
              [measure := optionComments]
              InBrackets
              (Parse.Problem.Expected what)
              None
              byComputing
              start
              (rewrite e then fine)
          | True => innerSignTaken start token later fine e)

-- Items.

def itemComments (item: Item): List Comment := item.value.comments ++ item.comma.all

def readItemComments (read: (Item, Bool)): List Comment := itemComments read.fst

theorem innerItem ∀ (self: Layout → {Parse Tok} Expr)
    (nested: ∀ (inner: Layout) => Parse.ReadsIn Lexer (() => self inner) (ExprSpec inner)):
    Parse.ReadsIn Lexer (() => item self) (Inner InBrackets readItemComments) :=
  innerOf
    (andThen (innerExpr InBrackets (nested InBrackets)) (value =>
      lastly (innerSignInBrackets "','" Comma) (comma => byComputing) (comma =>
        match comma with
          | Some comments => byComputing
          | None => byComputing)))

theorem itemsOne ∀ (item: Item): itemsComments [item] = itemComments item := match item with
  | { value, comma } => Eq.cong ((later: List Comment) => value.comments ++ later) (List.appendNil comma.all)

theorem itemsCommentsAppend ∀ (first second: List Item):
    itemsComments (first ++ second) = itemsComments first ++ itemsComments second :=
  match first with
    | [] => byComputing
    | [{ value, comma }, ..rest] =>
      calc itemsComments ([{ value, comma }, ..rest] ++ second)
        _ = value.comments ++ (comma.all ++ (itemsComments rest ++ itemsComments second)) :=
          Eq.cong ((later: List Comment) => value.comments ++ (comma.all ++ later)) (itemsCommentsAppend rest second)
        _ = value.comments ++ ((comma.all ++ itemsComments rest) ++ itemsComments second) :=
          Eq.cong
            ((later: List Comment) => value.comments ++ later)
            (List.appendAssoc comma.all (itemsComments rest) (itemsComments second)).flipped
        _ = (value.comments ++ (comma.all ++ itemsComments rest)) ++ itemsComments second :=
          (List.appendAssoc value.comments (comma.all ++ itemsComments rest) (itemsComments second)).flipped

--| What one more item adds to those found, which are newest first.
theorem itemsReverseCons ∀ (found: List Item) (item: Item) (later: List Comment):
    itemsComments [item, ..found].reverse ++ later = itemsComments found.reverse ++ (itemComments item ++ later) :=
  calc itemsComments [item, ..found].reverse ++ later
    _ = itemsComments (found.reverse ++ [item]) ++ later :=
      Eq.cong ((items: List Item) => itemsComments items ++ later) (List.reverseCons item found)
    _ = (itemsComments found.reverse ++ itemsComments [item]) ++ later :=
      Eq.cong ((front: List Comment) => front ++ later) (itemsCommentsAppend found.reverse [item])
    _ = itemsComments found.reverse ++ (itemsComments [item] ++ later) :=
      List.appendAssoc (itemsComments found.reverse) (itemsComments [item]) later
    _ = itemsComments found.reverse ++ (itemComments item ++ later) :=
      Eq.cong ((one: List Comment) => itemsComments found.reverse ++ (one ++ later)) (itemsOne item)

theorem ontoItemsFrom ∀ (self: Layout → {Parse Tok} Expr)
    (nested: ∀ (inner: Layout) => Parse.ReadsIn Lexer (() => self inner) (ExprSpec inner))
    (fuel: Nat) (found: List Item):
    Parse.ReadsIn Lexer
      (() => itemsFrom fuel self found)
      (Onto InBrackets (later => itemsComments found.reverse ++ later) itemsComments (items => True)) :=
  match fuel with
    | Zero => Parse.readsFatal _ _
    | Succ more => andThen (innerItem self nested) (read =>
      match read with
        | (item, True) =>
          ontoBefore (ontoItemsFrom self nested more [item, ..found]) (later => itemsReverseCons found item later)
        | (item, False) =>
          ontoDone byComputing
            (Eq.trans
              (List.appendNil (itemsComments [item, ..found].reverse)).flipped
              (itemsReverseCons found item [])))

--| Items and their closing bracket's comments.
def closedComments (found: (List Item, Comments)): List Comment := itemsComments found.fst ++ found.snd.all

theorem innerItems ∀ (self: Layout → {Parse Tok} Expr) (closer: Punctuation)
    (nested: ∀ (inner: Layout) => Parse.ReadsIn Lexer (() => self inner) (ExprSpec inner)):
    Parse.ReadsIn Lexer (() => items self closer) (Inner InBrackets closedComments) :=
  innerOf
    (andThen (innerSignInBrackets "'${closer.spelling}'" closer) (closed =>
      match closed with
        | Some close => ontoDone byComputing (List.appendNil close.all).flipped
        | None => Parse.readsWithMark _ _ (at fine =>
          andThen (innerOf (ontoItemsFrom self nested at.left [])) (found =>
            lastly (innerSign InBrackets "'${closer.spelling}'" closer) (close => byComputing) (close =>
              byComputing)))))

-- Atoms and their calls and fields.

--| The atom whose first token, `token`, was seen at `start`.
--|
--| Proof idea: by the token's kind. Each atom skips that very token
--| (`skipExpr`), then reads what is inside its brackets, if it has any,
--| as a chain; the other kinds fail.
theorem exprAtomOf ∀ (self: Layout → {Parse Tok} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Parse.ReadsIn Lexer (() => self inner) (ExprSpec inner))
    (start: Parse.Mark Tok) (token: Tok) (later: List Tok)
    (fine: Parse.Fits Tok Lexer [token, ..later])
    (shape: start.rest = [token, ..later])
    (allowed: layout.allows token = True):
    Parse.ReadsAt start (() => atomOf self (layout.comments token) token.value.kind) (ExprSpec layout) :=
  match kind: token.value.kind with
    | Name text => skipExpr layout start token later fine shape allowed (done =>
      ontoDone byComputing (List.appendNil (layout.kept token)).flipped)
    | Number digits => skipExpr layout start token later fine shape allowed (done =>
      ontoDone byComputing (List.appendNil (layout.kept token)).flipped)
    | Str written => skipExpr layout start token later fine shape allowed (done =>
      ontoDone byComputing (List.appendNil (layout.kept token)).flipped)
    | Sign OpenParen => skipExpr layout start token later fine shape allowed (done =>
      andThen (Parse.readsWeaken (nested InBrackets) (exprBrackets layout)) (inner =>
        lastly (inBrackets layout (innerSign InBrackets "')'" CloseParen)) (close => byComputing) (close =>
          byComputing)))
    | Sign OpenSquare => skipExpr layout start token later fine shape allowed (done =>
      lastly
        (inBrackets layout (innerItems self CloseSquare nested))
        (pair =>
          match pair with
            | (found, close) => byComputing)
        (pair =>
          match pair with
            | (found, close) => byComputing))
    | Sign CloseParen => Parse.readsExpected "an expression" start (rewrite shape then fine)
    | Sign CloseSquare => Parse.readsExpected "an expression" start (rewrite shape then fine)
    | Sign Comma => Parse.readsExpected "an expression" start (rewrite shape then fine)
    | Sign Dot => Parse.readsExpected "an expression" start (rewrite shape then fine)
    | Sign Defines => Parse.readsExpected "an expression" start (rewrite shape then fine)
    | Reserved keyword => Parse.readsExpected "an expression" start (rewrite shape then fine)
    | Op operator => Parse.readsExpected "an expression" start (rewrite shape then fine)
    | Stray text => Parse.readsExpected "an expression" start (rewrite shape then fine)

theorem exprAtom ∀ (self: Layout → {Parse Tok} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Parse.ReadsIn Lexer (() => self inner) (ExprSpec inner)):
    Parse.ReadsIn Lexer (() => atom self layout) (ExprSpec layout) :=
  Parse.readsInPeek _ _ (start fine =>
    match e: start.rest with
      | [] => Parse.readsExpected "an expression" start (rewrite e then fine)
      | [token, ..later] =>
        match allowed: layout.allows token with
          | True => exprAtomOf self layout nested start token later fine e allowed
          | False => Parse.readsExpected "an expression" start (rewrite e then fine))

--| What a call or field adds to `target`: its tokens' comments after
--| `target`'s, and nothing above the first token.
def Grows (layout: Layout) (target: Expr): List Tok → Expr → Prop :=
  Onto layout (later => target.comments ++ later) Expr.comments (longer => longer.firstAbove = target.firstAbove)

theorem growsNothing ∀ (layout: Layout) (target: Expr): Grows layout target [] target :=
  (byComputing, (past => (List.appendNil target.comments).flipped))

theorem growsThen ∀ (layout: Layout) (target longer: Expr) (first: List Tok)
    (grew: Grows layout target first longer)
    (read: List Tok) (value: Expr)
    (more: Grows layout longer read value):
    Grows layout target (first ++ read) value :=
  (
    (Eq.trans more.left grew.left),
    (past =>
      calc value.comments
        _ = longer.comments ++ allCarried read := more.right (List.allAppendRight layout.past first read past)
        _ = (target.comments ++ allCarried first) ++ allCarried read :=
          Eq.cong
            ((front: List Comment) => front ++ allCarried read)
            (grew.right (List.allAppendLeft layout.past first read past))
        _ = target.comments ++ (allCarried first ++ allCarried read) :=
          List.appendAssoc target.comments (allCarried first) (allCarried read)
        _ = target.comments ++ allCarried (first ++ read) :=
          Eq.cong ((back: List Comment) => target.comments ++ back) (allCarriedAppend first read).flipped)
  )

theorem growsCall ∀ (self: Layout → {Parse Tok} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Parse.ReadsIn Lexer (() => self inner) (ExprSpec inner))
    (target: Expr) (start: Parse.Mark Tok) (token: Tok) (later: List Tok)
    (fine: Parse.Fits Tok Lexer [token, ..later])
    (shape: start.rest = [token, ..later]):
    Parse.ReadsAt start (() => callAfter self target (layout.comments token)) (Grows layout target) :=
  skipOnto layout start token later fine shape (done =>
    lastly
      (inBrackets layout (innerItems self CloseParen nested))
      (pair => match pair with | (arguments, close) => byComputing)
      (pair => match pair with | (arguments, close) => byComputing))

theorem growsField ∀ (layout: Layout) (target: Expr) (start: Parse.Mark Tok) (token: Tok) (later: List Tok)
    (fine: Parse.Fits Tok Lexer [token, ..later])
    (shape: start.rest = [token, ..later]):
    Parse.ReadsAt start (() => fieldAfter layout target (layout.comments token)) (Grows layout target) :=
  skipOnto layout start token later fine shape (done =>
    lastly (innerName layout) (pair => match pair with | (named, nameComments) => byComputing) (pair =>
      match pair with | (named, nameComments) => byComputing))

--| Where `suffixesFrom` stops: it notes what it expected and gives the
--| target.
theorem growsStop ∀ (layout: Layout) (target: Expr):
    Parse.ReadsIn Lexer
      (() =>
        Parse.note (Parse.Problem.Expected "'('")
        Parse.note (Parse.Problem.Expected "'.'")
        target)
      (Grows layout target) :=
  Parse.readsThen (Parse.readsNote (Parse.Problem.Expected "'('")) (noted done none =>
    Parse.readsThen (Parse.readsNote (Parse.Problem.Expected "'.'")) (notedToo doneToo noneToo =>
      Parse.readsDone target _ (rewrite none, noneToo then growsNothing layout target)))

--| What `suffixesFrom` makes of the token it sees next at a layout.
def suffixNext (layout: Layout) (seen: Option Tok): (Kind, Comments) := match seen with
  | Some token if layout.allows token => (token.value.kind, layout.comments token)
  | _ => (Stray "", Comments.none)

--| What `suffixesFrom` sees first, as a fact about the mark it looks from.
--|
--| Proof idea: by what is left at the mark and whether the layout allows
--| the next token; each case is a value that read nothing.
theorem suffixNextAt ∀ (layout: Layout) (start: Parse.Mark Tok):
    Parse.ReadsAt start
      (() =>
        match peek() with
          | Some token if layout.allows token => (token.value.kind, layout.comments token)
          | _ => (Stray "", Comments.none))
      (read seen => read = [] ∧ seen = suffixNext layout start.rest.head) :=
  readsAtPeek _
    (read seen => read = [] ∧ seen = suffixNext layout start.rest.head)
    start
    (match e: start.rest with
      | [] =>
        readsAtDone start
          (Stray "", Comments.none)
          (read seen => read = [] ∧ seen = suffixNext layout None)
          ((byComputing, byComputing))
      | [token, ..later] =>
        match allowed: layout.allows token with
          | True =>
            readsAtDone start
              (token.value.kind, layout.comments token)
              (read seen => read = [] ∧ seen = (token.value.kind, layout.comments token))
              ((byComputing, byComputing))
          | False =>
            readsAtDone start
              (Stray "", Comments.none)
              (read seen => read = [] ∧ seen = (Stray "", Comments.none))
              ((byComputing, byComputing)))

--| A call or field tried after `target`, then the rest of the loop.
theorem growsTried ∀ (self: Layout → {Parse Tok} Expr) (layout: Layout) (more: Nat) (target: Expr)
    (tried: () → {Parse Tok} Expr) (at: Parse.Mark Tok)
    (fine: Parse.Fits Tok Lexer at.rest)
    (readsTried: Parse.ReadsAt at tried (Grows layout target))
    (onward: ∀ (longer: Expr) => Parse.ReadsIn Lexer
      (() => suffixesFrom more self layout longer)
      (Grows layout longer)):
    Parse.ReadsAt at (() => suffixesAfter more self layout target (Parse.optional tried)) (Grows layout target) :=
  Parse.readsAtThen (readsAtOptional readsTried) (read longer after starts maybe =>
    match longer, maybe with
      | Some longer, grew =>
        readsAtWeaken (onward longer after (fine.after starts)) (growsThen layout target longer read grew)
      | None, none => readsAtDone after target _ (rewrite none then growsNothing layout target))

--| An atom's calls and fields add their tokens' comments.
--|
--| Proof idea: induction on the fuel, from the mark where the next token
--| is seen. A `(` or `.` there is tried under `optional`: read, it is that
--| very token (`skipOnto`) and the loop goes on from the longer target
--| (`growsThen`); not read, nothing was.
theorem growsSuffixes ∀ (self: Layout → {Parse Tok} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Parse.ReadsIn Lexer (() => self inner) (ExprSpec inner))
    (fuel: Nat) (target: Expr):
    Parse.ReadsIn Lexer (() => suffixesFrom fuel self layout target) (Grows layout target) :=
  start fine =>
    Parse.readsAtThen (suffixNextAt layout start) (read seen at starts facts =>
      let same: start.rest = at.rest := rewrite facts.left at starts then starts
      let fineAt: Parse.Fits Tok Lexer at.rest := fine.after starts
      rewrite facts.left, facts.right, same then
        (match e: at.rest with
          | [] =>
            match fuel with
              | Zero => growsStop layout target at (rewrite e then fineAt)
              | Succ more => growsStop layout target at (rewrite e then fineAt)
          | [token, ..later] =>
            match allowed: layout.allows token with
              | False =>
                match fuel with
                  | Zero => growsStop layout target at (rewrite e then fineAt)
                  | Succ more => growsStop layout target at (rewrite e then fineAt)
              | True =>
                match fuel with
                  | Zero => growsStop layout target at (rewrite e then fineAt)
                  | Succ more =>
                    match kind: token.value.kind with
                      | Sign OpenParen =>
                        growsTried self layout more target
                          (() => callAfter self target (layout.comments token))
                          at
                          (rewrite e then fineAt)
                          (growsCall self layout nested target at token later fineAt e)
                          (longer => growsSuffixes self layout nested more longer)
                      | Sign Dot =>
                        growsTried self layout more target
                          (() => fieldAfter layout target (layout.comments token))
                          at
                          (rewrite e then fineAt)
                          (growsField layout target at token later fineAt e)
                          (longer => growsSuffixes self layout nested more longer)
                      | Sign CloseParen => growsStop layout target at (rewrite e then fineAt)
                      | Sign OpenSquare => growsStop layout target at (rewrite e then fineAt)
                      | Sign CloseSquare => growsStop layout target at (rewrite e then fineAt)
                      | Sign Comma => growsStop layout target at (rewrite e then fineAt)
                      | Sign Defines => growsStop layout target at (rewrite e then fineAt)
                      | Name text => growsStop layout target at (rewrite e then fineAt)
                      | Number digits => growsStop layout target at (rewrite e then fineAt)
                      | Str written => growsStop layout target at (rewrite e then fineAt)
                      | Reserved keyword => growsStop layout target at (rewrite e then fineAt)
                      | Op operator => growsStop layout target at (rewrite e then fineAt)
                      | Stray text => growsStop layout target at (rewrite e then fineAt)))

--| An atom, then its calls and fields, is an expression read at `layout`.
--|
--| Proof idea: the suffixes add their tokens' comments after the atom's
--| and leave its first token's alone, and all their tokens come after
--| the layout's first.
theorem exprGrows ∀ (layout: Layout) (first: Expr) (firstRead: List Tok)
    (spec: ExprSpec layout firstRead first)
    (read: List Tok) (value: Expr)
    (grew: Grows layout first read value):
    ExprSpec layout (firstRead ++ read) value :=
  match firstRead, spec with
    | [], never => never.impossible
    | [head, ..tail], known => (
      known.left,
      (Eq.trans grew.left known.right.left),
      (past =>
        calc value.comments
          _ = first.comments ++ allCarried read := grew.right (List.allAppendRight layout.past tail read past)
          _ = (layout.kept head ++ allCarried tail) ++ allCarried read :=
            Eq.cong
              ((front: List Comment) => front ++ allCarried read)
              (known.right.right (List.allAppendLeft layout.past tail read past))
          _ = layout.kept head ++ (allCarried tail ++ allCarried read) :=
            List.appendAssoc (layout.kept head) (allCarried tail) (allCarried read)
          _ = layout.kept head ++ allCarried (tail ++ read) :=
            Eq.cong ((back: List Comment) => layout.kept head ++ back) (allCarriedAppend tail read).flipped)
    )

theorem exprPostfix ∀ (self: Layout → {Parse Tok} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Parse.ReadsIn Lexer (() => self inner) (ExprSpec inner)):
    Parse.ReadsIn Lexer (() => postfix self layout) (ExprSpec layout) :=
  Parse.readsThen (Parse.readsNote (Parse.Problem.Expected "an expression")) (noted done none =>
    Parse.readsThen (exprAtom self layout nested) (atomRead first spec =>
      Parse.readsWithMark _ _ (at fine =>
        Parse.readsWeaken (growsSuffixes self layout nested (at.left + 1) first) (read value grew =>
          rewrite none then exprGrows layout first atomRead spec read value grew))))

--| A `-` seen next, then the operand: `Negate` holds the token's comments.
theorem exprNegated ∀ (layout: Layout) (inner: () → {Parse Tok} Expr) (start: Parse.Mark Tok)
    (token: Tok) (later: List Tok)
    (fine: Parse.Fits Tok Lexer [token, ..later])
    (shape: start.rest = [token, ..later])
    (allowed: layout.allows token = True)
    (readsInner: Parse.ReadsIn Lexer inner (ExprSpec layout)):
    Parse.ReadsAt start
      (() =>
        skip()
        Negate (layout.comments token) (inner()))
      (ExprSpec layout) :=
  skipExpr layout start token later fine shape allowed (done =>
    lastly (innerExpr layout readsInner) (operand => byComputing) (operand => byComputing))

--| `-`s before a postfix expression: each holds its token's comments.
--|
--| Proof idea: induction on the fuel, from the mark where the next token is
--| seen: a `-` there is the token skipped (`exprNegated`), and the rest is
--| the operand by induction; anything else is a postfix expression.
theorem exprNegations ∀ (self: Layout → {Parse Tok} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Parse.ReadsIn Lexer (() => self inner) (ExprSpec inner)) (fuel: Nat):
    Parse.ReadsIn Lexer (() => negationsFrom fuel self layout) (ExprSpec layout) :=
  Parse.readsInPeek [t := Parse.Located Token] _ _ (start fine =>
    match fuel with
      | Zero => exprPostfix self layout nested start fine
      | Succ more =>
        match e: start.rest with
          | [] => exprPostfix self layout nested start (rewrite e then fine)
          | [token, ..later] =>
            match minus: isMinus layout token with
              | False => exprPostfix self layout nested start (rewrite e then fine)
              | True =>
                exprNegated layout
                  (() => negationsFrom more self layout)
                  start
                  token
                  later
                  fine
                  e
                  (Bool.andLeft [a := layout.allows token] minus)
                  (exprNegations self layout nested more))

theorem exprOperand ∀ (self: Layout → {Parse Tok} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Parse.ReadsIn Lexer (() => self inner) (ExprSpec inner)):
    Parse.ReadsIn Lexer (() => operand self layout) (ExprSpec layout) :=
  Parse.readsWithMark _ _ (at fine => exprNegations self layout nested (at.left + 1))

-- Operator chains.

--| Two sides joined by an operator's token: the left side's comments,
--| the token's, then the right side's, whose tokens all come after the
--| layout's first.
--|
--| Proof idea: the left side opens the layout, so its spec gives its
--| comments as kept; the operator's token and the right side's tokens all
--| come after the first, so each holds every comment (`keptPast`,
--| `exprInner`), and the sums join by associativity.
theorem exprBinary ∀ (layout: Layout) (operator: Operator) (item: Tok) (leftRead rightRead: List Tok) (left right: Expr)
    (leftSpec: ExprSpec layout leftRead left)
    (rightSpec: ExprSpec layout rightRead right):
    ExprSpec layout (leftRead ++ [item, ..rightRead]) (Binary operator (layout.comments item) left right) :=
  match leftRead, leftSpec with
    | [], never => never.impossible
    | [head, ..tail], known => (
      known.left,
      known.right.left,
      (past =>
        let tailPast := List.allAppendLeft layout.past tail [item, ..rightRead] past
        let restPast: List.All layout.past [item, ..rightRead] :=
          List.allAppendRight layout.past tail [item, ..rightRead] past
        calc (Binary operator (layout.comments item) left right).comments
          _ = (layout.kept head ++ allCarried tail) ++ (layout.kept item ++ right.comments) :=
            Eq.cong
              ((front: List Comment) => front ++ (layout.kept item ++ right.comments))
              (known.right.right tailPast)
          _ = (layout.kept head ++ allCarried tail) ++ (item.value.comments ++ right.comments) :=
            Eq.cong
              ((sign: List Comment) => (layout.kept head ++ allCarried tail) ++ (sign ++ right.comments))
              (keptPast layout item restPast.left)
          _ = (layout.kept head ++ allCarried tail) ++ allCarried [item, ..rightRead] :=
            Eq.cong
              ((back: List Comment) => (layout.kept head ++ allCarried tail) ++ (item.value.comments ++ back))
              (exprInner layout rightRead right rightSpec restPast.right)
          _ = layout.kept head ++ (allCarried tail ++ allCarried [item, ..rightRead]) :=
            List.appendAssoc (layout.kept head) (allCarried tail) (allCarried [item, ..rightRead])
          _ = layout.kept head ++ allCarried (tail ++ [item, ..rightRead]) :=
            Eq.cong
              ((back: List Comment) => layout.kept head ++ back)
              (allCarriedAppend tail [item, ..rightRead]).flipped)
    )

theorem exprJoins ∀ (layout: Layout): OperatorJoins (operatorLevels layout) (ExprSpec layout) :=
  level associativity combine item leftRead rightRead left right found leftSpec rightSpec =>
    let carried := operatorCarries layout item
    let known := rewrite found at carried then carried
    match known with
      | Witness operator isBinary =>
        rewrite isBinary then exprBinary layout operator item leftRead rightRead left right leftSpec rightSpec

theorem exprChain ∀ (self: Layout → {Parse Tok} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Parse.ReadsIn Lexer (() => self inner) (ExprSpec inner)):
    Parse.ReadsIn Lexer
      (() => Parse.operators "an operator" (operatorLevels layout) (() => operand self layout))
      (ExprSpec layout) :=
  readsOperatorsRead "an operator"
    (operatorLevels layout)
    (() => operand self layout)
    (ExprSpec layout)
    (exprOperand self layout nested)
    (exprJoins layout)

-- Lines, and the notes above them.

--| The comments of a list's lines.
def spacedComments (measure: a → List Comment) (lines: List (Spaced a)): List Comment :=
  lines.flatMap (spaced => measure spaced.line)

theorem flatMapAppend ∀ (f: a → List b) (first second: List a):
    (first ++ second).flatMap f = first.flatMap f ++ second.flatMap f :=
  match first with
    | [] => byComputing
    | [head, ..tail] =>
      calc ([head, ..tail] ++ second).flatMap f
        _ = f head ++ (tail.flatMap f ++ second.flatMap f) :=
          Eq.cong ((back: List b) => f head ++ back) (flatMapAppend f tail second)
        _ = (f head ++ tail.flatMap f) ++ second.flatMap f :=
          (List.appendAssoc (f head) (tail.flatMap f) (second.flatMap f)).flipped

theorem flatMapConcat ∀ (f: a → List b) (groups: List (List a)):
    groups.concat.flatMap f = groups.flatMap (group => group.flatMap f) :=
  match groups with
    | [] => byComputing
    | [group, ..rest] =>
      calc ([group, ..rest]).concat.flatMap f
        _ = group.flatMap f ++ rest.concat.flatMap f := flatMapAppend f group rest.concat
        _ = group.flatMap f ++ rest.flatMap (group => group.flatMap f) :=
          Eq.cong ((back: List b) => group.flatMap f ++ back) (flatMapConcat f rest)

theorem linesFlat ∀ (lines: List (Spaced Statement)): linesComments lines = spacedComments Statement.comments lines :=
  match lines with
    | [] => byComputing
    | [{ blankBefore, line }, ..rest] => Eq.cong ((back: List Comment) => line.comments ++ back) (linesFlat rest)

theorem unblankedSame ∀ (measure: a → List Comment) (lines: List (Spaced a)):
    spacedComments measure (withoutFirstBlank lines) = spacedComments measure lines :=
  match lines with
    | [] => byComputing
    | [{ blankBefore, line }, ..rest] => byComputing

--| One more note among those found adds its comment.
theorem snocNote ∀ [note: Comment → a] (measure: a → List Comment)
    (noted: ∀ (comment: Comment) => measure (note comment) = [comment])
    (found: (List (Spaced a), Bool)) (comment: Comment):
    spacedComments measure (noteStep note found (OwnLine comment)).fst
      = spacedComments measure found.fst ++ [comment] :=
  calc spacedComments measure (found.fst ++ [{ blankBefore = found.snd, line = note comment }])
    _ = spacedComments measure found.fst ++ spacedComments measure [{ blankBefore = found.snd, line = note comment }] :=
      flatMapAppend (spaced => measure spaced.line) found.fst [{ blankBefore = found.snd, line = note comment }]
    _ = spacedComments measure found.fst ++ [comment] :=
      Eq.cong
        ((back: List Comment) => spacedComments measure found.fst ++ back)
        (Eq.trans (List.appendNil (measure (note comment))) (noted comment))

--| The note lines made of trivia hold its comments.
theorem notesFold ∀ [note: Comment → a] (measure: a → List Comment)
    (noted: ∀ (comment: Comment) => measure (note comment) = [comment])
    (trivia: List Trivia) (found: (List (Spaced a), Bool)):
    spacedComments measure (trivia.foldLeft found (noteStep note)).fst
      = spacedComments measure found.fst ++ trivia.flatMap Trivia.comments :=
  match trivia with
    | [] => (List.appendNil (spacedComments measure found.fst)).flipped
    | [BlankLine, ..rest] => notesFold measure noted rest (noteStep note found BlankLine)
    | [OwnLine comment, ..rest] =>
      calc spacedComments measure (rest.foldLeft (noteStep note found (OwnLine comment)) (noteStep note)).fst
        _ = spacedComments measure (noteStep note found (OwnLine comment)).fst ++ rest.flatMap Trivia.comments :=
          notesFold measure noted rest (noteStep note found (OwnLine comment))
        _ = (spacedComments measure found.fst ++ [comment]) ++ rest.flatMap Trivia.comments :=
          Eq.cong
            ((front: List Comment) => front ++ rest.flatMap Trivia.comments)
            (snocNote measure noted found comment)
        _ = spacedComments measure found.fst ++ ([comment] ++ rest.flatMap Trivia.comments) :=
          List.appendAssoc (spacedComments measure found.fst) [comment] (rest.flatMap Trivia.comments)

--| A line under the notes made of the trivia above it: the trivia's
--| comments, then the line's.
theorem notedCore ∀ [note: Comment → a] (measure: a → List Comment)
    (noted: ∀ (comment: Comment) => measure (note comment) = [comment])
    (above: List Trivia) (line: a) (notes: List (Spaced a)) (blankBefore: Bool)
    (found: spacedNotes note above = (notes, blankBefore)):
    spacedComments measure (notes ++ [{ blankBefore, line }]) = above.flatMap Trivia.comments ++ measure line :=
  let folded: spacedComments measure (spacedNotes note above).fst = above.flatMap Trivia.comments :=
    notesFold measure noted above ([], False)
  let known: spacedComments measure notes = above.flatMap Trivia.comments := rewrite found at folded then folded
  calc spacedComments measure (notes ++ [{ blankBefore, line }])
    _ = spacedComments measure notes ++ spacedComments measure [{ blankBefore, line }] :=
      flatMapAppend (spaced => measure spaced.line) notes [{ blankBefore, line }]
    _ = spacedComments measure notes ++ measure line :=
      Eq.cong ((back: List Comment) => spacedComments measure notes ++ back) (List.appendNil (measure line))
    _ = above.flatMap Trivia.comments ++ measure line := Eq.cong ((front: List Comment) => front ++ measure line) known

theorem notedStatementComments ∀ (above: List Trivia) (line: Statement):
    spacedComments Statement.comments (notedStatement above line) = above.flatMap Trivia.comments ++ line.comments :=
  match found: spacedNotes StatementNote above with
    | (notes, blankBefore) => notedCore Statement.comments (comment => byComputing) above line notes blankBefore found

theorem notedDeclarationComments ∀ (above: List Trivia) (line: Declaration):
    spacedComments Declaration.comments (notedDeclaration above line)
      = above.flatMap Trivia.comments ++ line.comments :=
  match found: spacedNotes DeclarationNote above with
    | (notes, blankBefore) => notedCore Declaration.comments (comment => byComputing) above line notes blankBefore found

--| A statement's first token keeps only its trailing comment in the
--| tree; with the own-line comments above it, that is all it holds.
theorem keptAtStart ∀ (column: Nat) (first: Tok):
    first.value.above.flatMap Trivia.comments ++ (InStatement column first.offset).kept first = first.value.comments :=
  match trailing: first.value.trailing with
    | Some located => rewrite ownOffset first.offset then byComputing
    | None => rewrite ownOffset first.offset then byComputing

--| A statement or declaration read from the lexer's tokens, with the
--| comments above its first token: all the comments of what was read.
--|
--| Proof idea: the first token read is the one the statement starts at,
--| so the layout keeps only its trailing comment (`keptAtStart`); every
--| later token has a greater offset (`Rising`), so none is at the
--| layout's start and `Opened` gives the rest.
theorem firstCarried ∀ [measure: a → List Comment] (column: Nat) (first: Tok) (later read: List Tok)
    (value: a) (rest: List Tok)
    (rising: Rising [first, ..later])
    (split: [first, ..later] = read ++ rest)
    (opened: Opened (InStatement column first.offset) measure read value):
    first.value.above.flatMap Trivia.comments ++ measure value = allCarried read :=
  match read, opened, split with
    | [], never, _ => never.impossible
    | [head, ..tail], carried, split =>
      let isFirst: first = head := List.consInjectiveHead first head later (tail ++ rest) split
      let laterSame: later = tail ++ rest := Eq.cong (.drop 1) split
      let apart: List.All (other => first.offset < other.offset) (tail ++ rest) := rewrite <- laterSame then rising.left
      let tailPast: List.All (InStatement column first.offset).past tail :=
        List.allImplies
          (other => first.offset < other.offset)
          (InStatement column first.offset).past
          (other below => Nat.equalOfLess first.offset other.offset below)
          tail
          (List.allAppendLeft (other => first.offset < other.offset) tail rest apart)
      let sum := carried tailPast
      rewrite <- isFirst at sum then
        rewrite <- isFirst then
          calc first.value.above.flatMap Trivia.comments ++ measure value
            _ = first.value.above.flatMap Trivia.comments
                ++ ((InStatement column first.offset).kept first ++ allCarried tail) :=
              Eq.cong ((back: List Comment) => first.value.above.flatMap Trivia.comments ++ back) sum
            _ = (first.value.above.flatMap Trivia.comments ++ (InStatement column first.offset).kept first)
                ++ allCarried tail :=
              (List.appendAssoc
                (first.value.above.flatMap Trivia.comments)
                ((InStatement column first.offset).kept first)
                (allCarried tail)).flipped
            _ = first.value.comments ++ allCarried tail :=
              Eq.cong ((front: List Comment) => front ++ allCarried tail) (keptAtStart column first)

--| A repetition whose every value holds its tokens' comments holds them
--| all.
--|
--| Proof idea: induction on the values, splitting what was read as
--| `Parse.Each` does.
theorem eachInner ∀ [measure: a → List Comment] (layout: Layout) (read: List Tok) (values: List a)
    (each: Parse.Each (Inner layout measure) read values):
    Inner layout (found => found.flatMap measure) read values :=
  match values, each with
    | [], none => rewrite none then (past => byComputing)
    | [value, ..rest], found =>
      match found with
        | (first, later, split, holds, others) =>
          rewrite split then
            (past =>
              calc ([value, ..rest]).flatMap measure
                _ = allCarried first ++ rest.flatMap measure :=
                  Eq.cong
                    ((front: List Comment) => front ++ rest.flatMap measure)
                    (holds (List.allAppendLeft layout.past first later past))
                _ = allCarried first ++ allCarried later :=
                  Eq.cong
                    ((back: List Comment) => allCarried first ++ back)
                    (eachInner layout later rest others (List.allAppendRight layout.past first later past))
                _ = allCarried (first ++ later) := (allCarriedAppend first later).flipped)

-- Bodies and blocks.

theorem clearedAll ∀ (comments: Comments)
    (none: comments.above = []):
    Comments.all { comments | above = [] } = comments.all :=
  Eq.cong ((above: List Comment) => above ++ comments.after.toList) none.flipped

--| Clearing changes nothing where the first token holds no comments.
--|
--| Proof idea: induction on the expression, down its leftmost spine: the
--| comments cleared are those of the leftmost token, which are none.
theorem withoutFirstAboveSame ∀ (expr: Expr)
    (none: expr.firstAbove = []):
    expr.withoutFirstAbove.comments = expr.comments :=
  match expr with
    | Var name comments => clearedAll comments none
    | NumberLiteral digits comments => clearedAll comments none
    | StringLiteral written comments => clearedAll comments none
    | Bracketed open inner close =>
      Eq.cong ((front: List Comment) => front ++ (inner.comments ++ close.all)) (clearedAll open none)
    | ListLiteral open items close =>
      Eq.cong ((front: List Comment) => front ++ (itemsComments items ++ close.all)) (clearedAll open none)
    | Call callee open arguments close =>
      Eq.cong
        ((front: List Comment) => front ++ (open.all ++ (itemsComments arguments ++ close.all)))
        (withoutFirstAboveSame callee none)
    | Field target dot name nameComments =>
      Eq.cong ((front: List Comment) => front ++ (dot.all ++ nameComments.all)) (withoutFirstAboveSame target none)
    | Negate minus operand => Eq.cong ((front: List Comment) => front ++ operand.comments) (clearedAll minus none)
    | Binary operator sign left right =>
      Eq.cong ((front: List Comment) => front ++ (sign.all ++ right.comments)) (withoutFirstAboveSame left none)
    | If ifComments condition thenComments whenTrue elseComments whenFalse =>
      Eq.cong
        ((front: List Comment) =>
          front
            ++ (condition.comments
              ++ (thenComments.all ++ (whenTrue.comments ++ (elseComments.all ++ whenFalse.comments)))))
        (clearedAll ifComments none)

--| `Layout.headed` loses nothing of an expression whose first token is
--| `head`: inside brackets it changes nothing, and outside them the
--| layout keeps no comments above `head`.
def HeadClear (layout: Layout) (head: Tok): Prop := match layout with
  | InBrackets => True
  | InStatement column begin => ((InStatement column begin).comments head).above = []

--| `HeadClear` of the next token, if the layout allows it.
def ClearAt (layout: Layout) (rest: List Tok): Prop := match rest with
  | [] => True
  | [head, ..tail] => layout.allows head = True → HeadClear layout head

theorem clearBrackets ∀ (rest: List Tok): ClearAt InBrackets rest := match rest with
  | [] => byComputing
  | [head, ..tail] => allowed => byComputing

theorem headedSame ∀ (layout: Layout) (head: Tok) (value: Expr)
    (clear: HeadClear layout head)
    (above: value.firstAbove = (layout.comments head).above):
    (layout.headed value).comments = value.comments :=
  match layout, clear, above with
    | InBrackets, _, _ => byComputing
    | InStatement column begin, none, above => withoutFirstAboveSame value (Eq.trans above none)

theorem bareOpened ∀ (layout: Layout) (read: List Tok) (value: Expr) (others: List Tok)
    (clear: ClearAt layout (read ++ others))
    (spec: ExprSpec layout read value):
    Opened layout Statement.comments read (Bare (layout.headed value)) :=
  match read, spec, clear with
    | [], never, _ => never.impossible
    | [head, ..tail], known, clear => past =>
      calc (layout.headed value).comments
        _ = value.comments := headedSame layout head value (clear known.left) known.right.left
        _ = layout.kept head ++ allCarried tail := known.right.right past

--| An expression as a statement, where the next token is one `headed`
--| loses nothing of.
theorem openedBare ∀ (self: Layout → {Parse Tok} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Parse.ReadsIn Lexer (() => self inner) (ExprSpec inner))
    (start: Parse.Mark Tok) (rest: List Tok)
    (shape: start.rest = rest)
    (fine: Parse.Fits Tok Lexer rest)
    (clear: ClearAt layout rest):
    Parse.ReadsAt start (() => bareStatement self layout) (Opened layout Statement.comments) :=
  Parse.readsAtThen (nested layout start (rewrite shape then fine)) (read value after starts spec =>
    readsAtDone after
      (Bare (layout.headed value)) _
      (rewrite List.appendNil read then
        bareOpened layout read value after.rest (rewrite <- starts, shape then clear) spec))

theorem innerInline ∀ (self: Layout → {Parse Tok} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Parse.ReadsIn Lexer (() => self inner) (ExprSpec inner))
    (start: Parse.Mark Tok) (rest: List Tok)
    (shape: start.rest = rest)
    (fine: Parse.Fits Tok Lexer rest)
    (clear: ClearAt layout rest):
    Parse.ReadsAt start (() => inlineBody self layout) (Inner layout Body.comments) :=
  Parse.readsAtThen (openedBare self layout nested start rest shape fine clear) (read line after starts opened =>
    readsAtDone after
      ({ statements = [{ blankBefore = False, line }] }: Body) _
      (rewrite List.appendNil read then
        (past => Eq.trans (List.appendNil line.comments) (openedInner layout read line opened past))))

--| A statement's line read from its first token, `first`.
--|
--| Proof idea: by the token's kind. A `let` skips that very token
--| (`skipOpened`) and reads its name, `=` and body as a chain; anything
--| else is an expression, whose first token is the statement's, so the
--| layout keeps nothing above it (`startAbove`).
theorem openedStatementLine ∀ (self: Layout → {Parse Tok} Expr)
    (nested: ∀ (inner: Layout) => Parse.ReadsIn Lexer (() => self inner) (ExprSpec inner)) (fuel: Nat)
    (readsBody: ∀ (inner: Layout) => Parse.ReadsIn Lexer (() => bodyFuel fuel self inner) (Inner inner Body.comments))
    (column: Nat) (start: Parse.Mark Tok) (first: Tok) (later: List Tok)
    (fine: Parse.Fits Tok Lexer [first, ..later])
    (shape: start.rest = [first, ..later]):
    Parse.ReadsAt start
      (() => statementLine fuel self (InStatement column first.offset) first first.value.kind)
      (Opened (InStatement column first.offset) Statement.comments) :=
  let bare: Parse.ReadsAt start
    (() => bareStatement self (InStatement column first.offset))
    (Opened (InStatement column first.offset) Statement.comments) :=
    openedBare self (InStatement column first.offset) nested start [first, ..later] shape fine (allowed =>
      startAbove column first)
  match kind: first.value.kind with
    | Reserved LetKeyword => skipOpened (InStatement column first.offset) start first later fine shape (done =>
      andThen (innerName (InStatement column first.offset)) (pair =>
        match pair with
          | (bound, nameComments) => andThen (innerSign (InStatement column first.offset) "'='" Defines) (equals =>
            lastly (readsBody (InStatement column first.offset)) (inner => byComputing) (inner => byComputing))))
    | Reserved FnKeyword => bare
    | Reserved IfKeyword => bare
    | Reserved ThenKeyword => bare
    | Reserved ElseKeyword => bare
    | Name text => bare
    | Number digits => bare
    | Str written => bare
    | Sign punctuation => bare
    | Op operator => bare
    | Stray text => bare

theorem innerStatementAt ∀ (self: Layout → {Parse Tok} Expr)
    (nested: ∀ (inner: Layout) => Parse.ReadsIn Lexer (() => self inner) (ExprSpec inner)) (fuel: Nat)
    (readsBody: ∀ (inner: Layout) => Parse.ReadsIn Lexer (() => bodyFuel fuel self inner) (Inner inner Body.comments))
    (column: Nat) (start: Parse.Mark Tok) (first: Tok) (later: List Tok)
    (fine: Parse.Fits Tok Lexer [first, ..later])
    (shape: start.rest = [first, ..later]):
    Parse.ReadsAt start
      (() =>
        notedStatement first.value.above
          (statementLine fuel self (InStatement column first.offset) first first.value.kind))
      (Inner InBrackets (spacedComments Statement.comments)) :=
  Parse.readsAtThen
    (openedStatementLine self nested fuel readsBody column start first later fine shape)
    (read line after starts opened =>
      readsAtDone after
        (notedStatement first.value.above line) _
        (rewrite List.appendNil read then
          (past =>
            Eq.trans
              (notedStatementComments first.value.above line)
              (firstCarried column first later read line after.rest fine.holds.right
                (Eq.trans shape.flipped starts)
                opened))))

--| A statement's lines hold every comment of its tokens, those above its
--| first token included (they are the note lines).
--|
--| Proof idea: from the mark the statement looks from; where its first
--| token starts a line at the column, `innerStatementAt`, and otherwise it
--| stops.
theorem innerStatement ∀ (self: Layout → {Parse Tok} Expr)
    (nested: ∀ (inner: Layout) => Parse.ReadsIn Lexer (() => self inner) (ExprSpec inner)) (fuel: Nat)
    (readsBody: ∀ (inner: Layout) => Parse.ReadsIn Lexer (() => bodyFuel fuel self inner) (Inner inner Body.comments))
    (column: Nat):
    Parse.ReadsIn Lexer (() => statement fuel self column) (Inner InBrackets (spacedComments Statement.comments)) :=
  readsAtMark _ _ (start fine =>
    match e: start.rest with
      | [] =>
        Parse.readsStop
          [inv := Lexer]
          (Inner InBrackets (spacedComments Statement.comments))
          start
          (rewrite e then fine)
      | [first, ..later] =>
        match starts: first.value.startsLine && first.value.column == column with
          | False =>
            Parse.readsStop
              [inv := Lexer]
              (Inner InBrackets (spacedComments Statement.comments))
              start
              (rewrite e then fine)
          | True => innerStatementAt self nested fuel readsBody column start first later fine e)

theorem blockCarried ∀ (read: List Tok) (groups: List (List (Spaced Statement)))
    (each: Parse.Each (Inner InBrackets (spacedComments Statement.comments)) read groups):
    Inner InBrackets Body.comments read { statements = withoutFirstBlank groups.concat } :=
  past =>
    calc linesComments (withoutFirstBlank groups.concat)
      _ = spacedComments Statement.comments (withoutFirstBlank groups.concat) :=
        linesFlat (withoutFirstBlank groups.concat)
      _ = spacedComments Statement.comments groups.concat := unblankedSame Statement.comments groups.concat
      _ = groups.flatMap (spacedComments Statement.comments) :=
        flatMapConcat (spaced => Statement.comments spaced.line) groups
      _ = allCarried read := eachInner InBrackets read groups each past

theorem innerBlock ∀ (self: Layout → {Parse Tok} Expr)
    (nested: ∀ (inner: Layout) => Parse.ReadsIn Lexer (() => self inner) (ExprSpec inner)) (fuel: Nat)
    (readsBody: ∀ (inner: Layout) => Parse.ReadsIn Lexer (() => bodyFuel fuel self inner) (Inner inner Body.comments))
    (column: Nat):
    Parse.ReadsIn Lexer (() => block fuel self column) (Inner InBrackets Body.comments) :=
  Parse.readsThen
    (Parse.readsMany1
      (() => statement fuel self column)
      (Inner InBrackets (spacedComments Statement.comments))
      (innerStatement self nested fuel readsBody column))
    (read lines each =>
      Parse.readsDone
        ({ statements = withoutFirstBlank lines.toList.concat }: Body) _
        (rewrite List.appendNil read then blockCarried read lines.toList each))

--| An inline body's first token holds no comments above it in the tree:
--| it is the statement's first, or it doesn't start a line, and then the
--| lexer put none above it (`Tidy`).
theorem inlineClear ∀ (column at: Nat) (token: Tok)
    (tidy: Tidy token)
    (deeper: (token.value.startsLine && token.value.column > column) = False)
    (allowed: (InStatement column at).allows token = True):
    ((InStatement column at).comments token).above = [] :=
  match same: token.offset == at with
    | True => byComputing
    | False =>
      match starts: token.value.startsLine with
        | False => Eq.trans (ownLinesSame token.value.above) (tidy starts)
        | True => (Bool.falseNotTrue (rewrite deeper at allowed then allowed)).impossible

--| A body, a block or one expression.
--|
--| Proof idea: induction on the fuel, from the mark where the next token is
--| seen. A token starting a deeper line starts a block (`innerBlock`, with
--| this lemma for the bodies nested in it); otherwise the body is one
--| expression, and `inlineClear` says `headed` loses nothing of it.
theorem innerBodyFuel ∀ (self: Layout → {Parse Tok} Expr)
    (nested: ∀ (inner: Layout) => Parse.ReadsIn Lexer (() => self inner) (ExprSpec inner))
    (fuel: Nat) (layout: Layout):
    Parse.ReadsIn Lexer (() => bodyFuel fuel self layout) (Inner layout Body.comments) :=
  Parse.readsInPeek [t := Parse.Located Token] _ _ (start fine =>
    match fuel with
      | Zero => Parse.readsFatal [inv := Lexer] _ (Inner layout Body.comments) start fine
      | Succ more =>
        match layout with
          | InBrackets =>
            innerInline self InBrackets nested start start.rest byComputing fine (clearBrackets start.rest)
          | InStatement column at =>
            match e: start.rest with
              | [] => innerInline self (InStatement column at) nested start [] e fine byComputing
              | [token, ..later] =>
                match deeper: token.value.startsLine && token.value.column > column with
                  | False => innerInline self (InStatement column at) nested start [token, ..later] e fine (allowed =>
                    inlineClear column at token fine.holds.left.left deeper allowed)
                  | True =>
                    inBrackets
                      [p := () => block more self token.value.column]
                      (InStatement column at)
                      (innerBlock self nested more (inner => innerBodyFuel self nested more inner) token.value.column)
                      start
                      (rewrite e then fine))

theorem innerBody ∀ (self: Layout → {Parse Tok} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Parse.ReadsIn Lexer (() => self inner) (ExprSpec inner)):
    Parse.ReadsIn Lexer (() => body self layout) (Inner layout Body.comments) :=
  Parse.readsWithMark _ _ (at fine => innerBodyFuel self nested (at.left + 1) layout)

-- `if`, and the expression parser.

--| A token seen next and read for its comments.
theorem innerTaken ∀ (layout: Layout) (start: Parse.Mark Tok) (token: Tok) (later: List Tok)
    (fine: Parse.Fits Tok Lexer [token, ..later])
    (shape: start.rest = [token, ..later]):
    Parse.ReadsAt start
      (() =>
        skip()
        layout.comments token)
      (Inner layout Comments.all) :=
  skipInner layout start token later fine shape (done =>
    ontoDone byComputing (List.appendNil (layout.kept token)).flipped)

--| `elseKeyword` holds its token's comments.
--|
--| Proof idea: from the mark where it looks. An `else` seen there is the
--| token skipped (`innerTaken`), or the parse fails; otherwise `keyword`
--| reads it or fails.
theorem innerElse ∀ (layout: Layout): Parse.ReadsIn Lexer (() => elseKeyword layout) (Inner layout Comments.all) :=
  Parse.readsInPeek _ _ (start fine =>
    match e: start.rest with
      | [] => innerKeyword layout ElseKeyword start (rewrite e then fine)
      | [token, ..later] =>
        match isElse: (keywordIs ElseKeyword token.value.kind).isSome with
          | False => innerKeyword layout ElseKeyword start (rewrite e then fine)
          | True =>
            match allowed: layout.allowsElse token with
              | True => innerTaken layout start token later fine e
              | False =>
                Parse.readsFail
                  [inv := Lexer]
                  "'else' must not start a line to the left of its 'if' statement"
                  (Inner layout Comments.all)
                  start
                  (rewrite e then fine))

--| An `if` from its keyword, the token seen next.
theorem exprIf ∀ (self: Layout → {Parse Tok} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Parse.ReadsIn Lexer (() => self inner) (ExprSpec inner))
    (start: Parse.Mark Tok) (token: Tok) (later: List Tok)
    (fine: Parse.Fits Tok Lexer [token, ..later])
    (shape: start.rest = [token, ..later])
    (allowed: layout.allows token = True):
    Parse.ReadsAt start
      (() =>
        skip()
        let condition := self layout
        let thenComments := keyword layout ThenKeyword
        let whenTrue := body self layout
        let elseComments := elseKeyword layout
        let whenFalse := body self layout
        If (layout.comments token) condition thenComments whenTrue elseComments whenFalse)
      (ExprSpec layout) :=
  skipExpr layout start token later fine shape allowed (done =>
    andThen (innerExpr layout (nested layout)) (condition =>
      andThen (innerKeyword layout ThenKeyword) (thenComments =>
        andThen (innerBody self layout nested) (whenTrue =>
          andThen (innerElse layout) (elseComments =>
            lastly (innerBody self layout nested) (whenFalse => byComputing) (whenFalse => byComputing))))))

--| One level of the expression parser, given that `self` reads what it
--| should for the expressions nested in it.
theorem exprRule ∀ (self: Layout → {Parse Tok} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Parse.ReadsIn Lexer (() => self inner) (ExprSpec inner)):
    Parse.ReadsIn Lexer (() => expressionRule self layout) (ExprSpec layout) :=
  Parse.readsInPeek _ _ (start fine =>
    match e: start.rest with
      | [] => exprChain self layout nested start (rewrite e then fine)
      | [token, ..later] =>
        match found: isIf layout token with
          | False => exprChain self layout nested start (rewrite e then fine)
          | True => exprIf self layout nested start token later fine e (Bool.andLeft [a := layout.allows token] found))

--| Every expression the parser reads from the lexer's tokens holds
--| their comments.
theorem exprExpression ∀ (layout: Layout): Parse.ReadsIn Lexer (() => expression layout) (ExprSpec layout) :=
  Parse.readsRecursiveWith expressionRule ExprSpec (self nested argument => exprRule self argument nested) layout

-- Declarations and the file.

def stepComments (step: (Comments, (Text, Comments))): List Comment := step.fst.all ++ step.snd.snd.all

theorem innerParameterStep: Parse.ReadsIn Lexer parameterStep (Inner InBrackets stepComments) :=
  innerOf
    (andThen (innerSign InBrackets "','" Comma) (comma =>
      lastly (innerName InBrackets) (named => byComputing) (named => byComputing)))

def listComments (found: ((Text, Comments), List (Comments, (Text, Comments)))): List Comment :=
  found.fst.snd.all ++ found.snd.flatMap stepComments

theorem innerParameterList: Parse.ReadsIn Lexer parameterList (Inner InBrackets listComments) :=
  innerOf
    (andThen (innerName InBrackets) (first =>
      lastly
        (Parse.readsWeaken
          (Parse.readsMany parameterStep (Inner InBrackets stepComments) innerParameterStep)
          (eachInner [measure := stepComments] InBrackets))
        (others => byComputing)
        (others => byComputing)))

def parametersComments (parameters: List Parameter): List Comment := parameters.flatMap Parameter.allComments

theorem withCommasComments ∀ (first: (Text, Comments)) (others: List (Comments, (Text, Comments))):
    parametersComments (withCommas first others) = first.snd.all ++ others.flatMap stepComments :=
  match others with
    | [] => List.appendNil (first.snd.all ++ [])
    | [(comma, next), ..rest] =>
      calc parametersComments (withCommas first [(comma, next), ..rest])
        _ = (first.snd.all ++ comma.all) ++ (next.snd.all ++ rest.flatMap stepComments) :=
          Eq.cong ((back: List Comment) => (first.snd.all ++ comma.all) ++ back) (withCommasComments next rest)
        _ = first.snd.all ++ (comma.all ++ (next.snd.all ++ rest.flatMap stepComments)) :=
          List.appendAssoc first.snd.all comma.all (next.snd.all ++ rest.flatMap stepComments)
        _ = first.snd.all ++ ((comma.all ++ next.snd.all) ++ rest.flatMap stepComments) :=
          Eq.cong
            ((back: List Comment) => first.snd.all ++ back)
            (List.appendAssoc comma.all next.snd.all (rest.flatMap stepComments)).flipped

theorem innerParameters: Parse.ReadsIn Lexer
      (() => parametersOf (Parse.optional parameterList))
      (Inner InBrackets parametersComments) :=
  Parse.readsThen (Parse.readsOptional innerParameterList) (read found maybe =>
    match found, maybe with
      | None, none => Parse.readsDone [] _ (rewrite none then (past => byComputing))
      | Some (first, others), inner =>
        Parse.readsDone
          (withCommas first others) _
          (rewrite List.appendNil read then (past => Eq.trans (withCommasComments first others) (inner past))))

theorem openedFunctionLine ∀ (layout: Layout) (start: Parse.Mark Tok) (first: Tok) (later: List Tok)
    (fine: Parse.Fits Tok Lexer [first, ..later])
    (shape: start.rest = [first, ..later]):
    Parse.ReadsAt start (() => functionLine layout first) (Opened layout Declaration.comments) :=
  skipOpened layout start first later fine shape (done =>
    andThen (innerName layout) (pair =>
      match pair with
        | (declared, nameComments) => andThen (innerSign layout "'('" OpenParen) (open =>
          andThen (inBrackets layout innerParameters) (parameters =>
            andThen (inBrackets layout (innerSign InBrackets "')'" CloseParen)) (close =>
              andThen (innerSign layout "'='" Defines) (equals =>
                lastly (innerBody expression layout exprExpression) (inner => byComputing) (inner => byComputing)))))))

theorem openedValueLine ∀ (layout: Layout) (start: Parse.Mark Tok) (first: Tok) (later: List Tok)
    (fine: Parse.Fits Tok Lexer [first, ..later])
    (shape: start.rest = [first, ..later]):
    Parse.ReadsAt start (() => valueLine layout first) (Opened layout Declaration.comments) :=
  skipOpened layout start first later fine shape (done =>
    andThen (innerName layout) (pair =>
      match pair with
        | (declared, nameComments) => andThen (innerSign layout "'='" Defines) (equals =>
          lastly (innerBody expression layout exprExpression) (inner => byComputing) (inner => byComputing))))

--| Not a declaration: what `declarationLine` does at any other token.
theorem noDeclaration ∀ (layout: Layout):
    Parse.ReadsIn Lexer
      (() =>
        Parse.note (Parse.Problem.Literal "fn")
        Parse.note (Parse.Problem.Literal "let")
        Empty.absurd Parse.stop())
      (Opened layout Declaration.comments) :=
  Parse.readsThen (Parse.readsNote (Parse.Problem.Literal "fn")) (noted done none =>
    Parse.readsThen (Parse.readsNote (Parse.Problem.Literal "let")) (notedToo doneToo noneToo => Parse.readsStop _))

theorem openedDeclarationLine ∀ (layout: Layout) (start: Parse.Mark Tok) (first: Tok) (later: List Tok)
    (fine: Parse.Fits Tok Lexer [first, ..later])
    (shape: start.rest = [first, ..later]):
    Parse.ReadsAt start (() => declarationLine layout first) (Opened layout Declaration.comments) :=
  match kind: first.value.kind with
    | Reserved FnKeyword => openedFunctionLine layout start first later fine shape
    | Reserved LetKeyword => openedValueLine layout start first later fine shape
    | Reserved IfKeyword => noDeclaration layout start (rewrite shape then fine)
    | Reserved ThenKeyword => noDeclaration layout start (rewrite shape then fine)
    | Reserved ElseKeyword => noDeclaration layout start (rewrite shape then fine)
    | Name text => noDeclaration layout start (rewrite shape then fine)
    | Number digits => noDeclaration layout start (rewrite shape then fine)
    | Str written => noDeclaration layout start (rewrite shape then fine)
    | Sign punctuation => noDeclaration layout start (rewrite shape then fine)
    | Op operator => noDeclaration layout start (rewrite shape then fine)
    | Stray text => noDeclaration layout start (rewrite shape then fine)

theorem innerDeclarationAt ∀ (start: Parse.Mark Tok) (first: Tok) (later: List Tok)
    (fine: Parse.Fits Tok Lexer [first, ..later])
    (shape: start.rest = [first, ..later]):
    Parse.ReadsAt start
      (() => notedDeclaration first.value.above (declarationLine (InStatement 0 first.offset) first))
      (Inner InBrackets (spacedComments Declaration.comments)) :=
  Parse.readsAtThen
    (openedDeclarationLine (InStatement 0 first.offset) start first later fine shape)
    (read parsed after starts opened =>
      readsAtDone after
        (notedDeclaration first.value.above parsed) _
        (rewrite List.appendNil read then
          (past =>
            Eq.trans
              (notedDeclarationComments first.value.above parsed)
              (firstCarried 0 first later read parsed after.rest fine.holds.right
                (Eq.trans shape.flipped starts)
                opened))))

--| A declaration's lines hold every comment of its tokens, those above
--| its first token included.
--|
--| Proof idea: as `innerStatement`, with `innerDeclarationAt`.
theorem innerDeclaration: Parse.ReadsIn Lexer declaration (Inner InBrackets (spacedComments Declaration.comments)) :=
  readsAtMark _ _ (start fine =>
    match e: start.rest with
      | [] =>
        Parse.readsStop
          [inv := Lexer]
          (Inner InBrackets (spacedComments Declaration.comments))
          start
          (rewrite e then fine)
      | [first, ..later] =>
        match starts: first.value.startsLine && first.value.column == 0 with
          | False =>
            Parse.readsStop
              [inv := Lexer]
              (Inner InBrackets (spacedComments Declaration.comments))
              start
              (rewrite e then fine)
          | True => innerDeclarationAt start first later fine e)

theorem fileOfComments ∀ (declarations: List (Spaced Declaration)) (endTrivia: List Trivia):
    (fileOf declarations endTrivia).comments
      = spacedComments Declaration.comments declarations ++ endTrivia.flatMap Trivia.comments :=
  let folded: spacedComments Declaration.comments (spacedNotes DeclarationNote endTrivia).fst
    = endTrivia.flatMap Trivia.comments :=
    notesFold Declaration.comments (comment => byComputing) endTrivia ([], False)
  match found: spacedNotes DeclarationNote endTrivia with
    | (endNotes, blank) =>
      calc spacedComments Declaration.comments (withoutFirstBlank (declarations ++ endNotes))
        _ = spacedComments Declaration.comments (declarations ++ endNotes) :=
          unblankedSame Declaration.comments (declarations ++ endNotes)
        _ = spacedComments Declaration.comments declarations ++ spacedComments Declaration.comments endNotes :=
          flatMapAppend (spaced => Declaration.comments spaced.line) declarations endNotes
        _ = spacedComments Declaration.comments declarations ++ endTrivia.flatMap Trivia.comments :=
          Eq.cong ((back: List Comment) => spacedComments Declaration.comments declarations ++ back) folded

--| What the file holds, given its declarations: their comments, then the
--| end's.
def FileEnds (declarations: List (Spaced Declaration)) (endTrivia: List Trivia) (read: List Tok) (file: SourceFile):
    Prop :=
  read = [] ∧ file.comments = spacedComments Declaration.comments declarations ++ endTrivia.flatMap Trivia.comments

theorem carriesFileEnd ∀ (declarations: List (Spaced Declaration)) (endTrivia: List Trivia):
    Parse.ReadsIn Lexer (() => fileEnd declarations endTrivia) (FileEnds declarations endTrivia) :=
  let done: Parse.ReadsIn Lexer (() => fileOf declarations endTrivia) (FileEnds declarations endTrivia) :=
    Parse.readsDone (fileOf declarations endTrivia) _ ((byComputing, (fileOfComments declarations endTrivia)))
  Parse.readsPeek _ _ (start fine =>
    match e: start.rest with
      | [] => done
      | [token, ..later] =>
        match indented: token.value.startsLine && token.value.column > 0 with
          | False => done
          | True => Parse.readsFail _ _)

--| A file read from the lexer's tokens holds all their comments, then
--| those after the last token.
def FileCarries (endTrivia: List Trivia) (read: List Tok) (file: SourceFile): Prop :=
  file.comments = allCarried read ++ endTrivia.flatMap Trivia.comments

theorem carriesSourceFile ∀ (endTrivia: List Trivia):
    Parse.ReadsIn Lexer (() => sourceFile endTrivia) (FileCarries endTrivia) :=
  Parse.readsThen
    (Parse.readsMany declaration (Inner InBrackets (spacedComments Declaration.comments)) innerDeclaration)
    (read found each =>
      Parse.readsWeaken (carriesFileEnd found.concat endTrivia) (endRead file facts =>
        rewrite facts.left, List.appendNil read then
          calc file.comments
            _ = spacedComments Declaration.comments found.concat ++ endTrivia.flatMap Trivia.comments := facts.right
            _ = allCarried read ++ endTrivia.flatMap Trivia.comments :=
              Eq.cong
                ((front: List Comment) => front ++ endTrivia.flatMap Trivia.comments)
                (Eq.trans
                  (flatMapConcat (spaced => Declaration.comments spaced.line) found)
                  (eachInner InBrackets read found each (bracketsPast read)))))

--| The walk, finished: a file read from the lexer's tokens holds their
--| comments, then the end's.
theorem tokensCarry ∀ (tokens: List Tok) (endTrivia: List Trivia) (file: SourceFile)
    (fits: Parse.Fits Tok Lexer tokens)
    (whole: Parse.whole tokens (() => sourceFile endTrivia) = Ok file):
    file.comments = allCarried tokens ++ endTrivia.flatMap Trivia.comments :=
  Parse.wholeReadsIn tokens
    (() => sourceFile endTrivia)
    (FileCarries endTrivia)
    file
    (carriesSourceFile endTrivia)
    fits
    whole
