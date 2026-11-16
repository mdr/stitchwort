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
    (readsLast: Parse.ReadsIn inv p (Inner layout first))
    (holds: ∀ (v: a) => extra (f v))
    (same: ∀ (v: a) => measure (f v) = before (first v)):
    Parse.ReadsIn inv (() => f (p())) (Onto layout before measure extra) :=
  Parse.readsThen readsLast (read v carried =>
    Parse.readsDone (f v) _
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
      (Onto layout
        (more => layout.kept token ++ more)
        Expr.comments
        (found => found.firstAbove = (layout.comments token).above))):
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
          innerOne [measure := Comments.all] layout token value
            (Eq.cong Comments.all (selectedComments layout (signIs wanted) token value selected)))

theorem innerKeyword ∀ (layout: Layout) (wanted: Keyword):
    Parse.ReadsIn Lexer (() => keyword layout wanted) (Inner layout Comments.all) :=
  Parse.readsWeaken
    (Parse.readsOne "'${wanted.spelling}'" (selectComments layout (keywordIs wanted)))
    (taken value found =>
      match found with
        | (token, single, selected) =>
          rewrite single then
            innerOne [measure := Comments.all] layout token value
              (Eq.cong Comments.all (selectedComments layout (keywordIs wanted) token value selected)))

def namedComments (named: (Text, Comments)): List Comment := named.snd.all

theorem selectedNamed ∀ (layout: Layout) (token: Tok) (named: (Text, Comments))
    (selected: selectWithComments layout nameOf token = Some named):
    named.snd = layout.comments token :=
  match allowed: layout.allows token with
    | True =>
      match kind: token.value.kind with | Name text => rewrite <- Option.someInjective selected then byComputing

theorem innerName ∀ (layout: Layout): Parse.ReadsIn Lexer (() => name layout) (Inner layout namedComments) :=
  Parse.readsWeaken (Parse.readsOne "a name" (selectWithComments layout nameOf)) (taken value found =>
    match found with
      | (token, single, selected) =>
        rewrite single then
          innerOne [measure := namedComments] layout token value (Eq.cong Comments.all (selectedNamed layout token value selected)))

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

theorem innerSignInBrackets ∀ (what: Text) (wanted: Punctuation):
    Parse.ReadsIn Lexer (() => signInBrackets what wanted) (Inner InBrackets optionComments) :=
  Parse.readsInPeek _ _ (start fine =>
    match e: start.rest with
      | [] =>
        innerNoted [measure := optionComments] InBrackets (Parse.Problem.Expected what) None byComputing start
          (rewrite e then fine)
      | [token, ..later] =>
        match isSign: (signIs wanted token.value.kind).isSome with
          | False =>
            innerNoted [measure := optionComments] InBrackets (Parse.Problem.Expected what) None byComputing start
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
            lastly (innerSign InBrackets "'${closer.spelling}'" closer) (close => byComputing) (close => byComputing)))))

-- Atoms and their calls and fields.

theorem exprAtomOf ∀ (self: Layout → {Parse Tok} Expr) (layout: Layout)
    (nested: ∀ (inner: Layout) => Parse.ReadsIn Lexer (() => self inner) (ExprSpec inner))
    (start: Parse.Mark Tok) (token: Tok) (later: List Tok)
    (fine: Parse.Fits Tok Lexer [token, ..later])
    (shape: start.rest = [token, ..later])
    (allowed: layout.allows token = True):
    Parse.ReadsAt start (() => atomOf self (layout.comments token) token.value.kind) (ExprSpec layout) :=
  match kind: token.value.kind with
    | Name text =>
      skipExpr layout start token later fine shape allowed (done =>
        ontoDone byComputing (List.appendNil (layout.kept token)).flipped)
    | Number digits =>
      skipExpr layout start token later fine shape allowed (done =>
        ontoDone byComputing (List.appendNil (layout.kept token)).flipped)
    | Str written =>
      skipExpr layout start token later fine shape allowed (done =>
        ontoDone byComputing (List.appendNil (layout.kept token)).flipped)
    | Sign OpenParen =>
      skipExpr layout start token later fine shape allowed (done =>
        andThen (Parse.readsWeaken (nested InBrackets) (exprBrackets layout)) (inner =>
          lastly
            (inBrackets layout (innerSign InBrackets "')'" CloseParen))
            (close => byComputing)
            (close => byComputing)))
    | Sign OpenSquare =>
      skipExpr layout start token later fine shape allowed (done =>
        lastly
          (inBrackets layout (innerItems self CloseSquare nested))
          (pair => match pair with | (found, close) => byComputing)
          (pair => match pair with | (found, close) => byComputing))
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
    (grew: Grows layout target first longer) (read: List Tok) (value: Expr)
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
    lastly
      (innerName layout)
      (pair => match pair with | (named, nameComments) => byComputing)
      (pair => match pair with | (named, nameComments) => byComputing))

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

theorem suffixNextAt ∀ (layout: Layout) (start: Parse.Mark Tok):
    Parse.ReadsAt start
      (() =>
        match peek() with
          | Some token if layout.allows token => (token.value.kind, layout.comments token)
          | _ => (Stray "", Comments.none))
      (read seen => read = [] ∧ seen = suffixNext layout start.rest.head) :=
  readsAtPeek _ (read seen => read = [] ∧ seen = suffixNext layout start.rest.head) start
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

theorem exprGrows ∀ (layout: Layout) (first: Expr) (firstRead: List Tok)
    (spec: ExprSpec layout firstRead first) (read: List Tok) (value: Expr)
    (grew: Grows layout first read value):
    ExprSpec layout (firstRead ++ read) value :=
  match firstRead, spec with
    | [], never => never.impossible
    | [head, ..tail], known =>
      (
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
theorem exprNegated ∀ (layout: Layout) (inner: () → {Parse Tok} Expr) (start: Parse.Mark Tok) (token: Tok)
    (later: List Tok)
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
theorem exprBinary ∀ (layout: Layout) (operator: Operator) (item: Tok) (leftRead rightRead: List Tok)
    (left right: Expr)
    (leftSpec: ExprSpec layout leftRead left)
    (rightSpec: ExprSpec layout rightRead right):
    ExprSpec layout (leftRead ++ [item, ..rightRead]) (Binary operator (layout.comments item) left right) :=
  match leftRead, leftSpec with
    | [], never => never.impossible
    | [head, ..tail], known =>
      (
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
