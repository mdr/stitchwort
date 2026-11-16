--| Spelling, for everything around expressions (SW-3418, layer E): an
--| `if` outside brackets, bodies, blocks and their lines, with the
--| comment lines and blank lines above each statement.
--|
--| `SpellProofs.sw` spells an expression with no block in it. Here the
--| induction goes on through an `if`'s branches into blocks
--| (`exprOut`, `bodyOut`, `linesOut`, mutual). What is new against
--| expressions: comment lines and blank lines wait for the next
--| statement's first token (`notesOf`, `SeenTo`), and a statement has to
--| end before what follows it (`After`), which the tokens' rising offsets
--| and the next line's start give (`lineAfter`).

namespace Toy.Fmt.Proofs
import Toy.Doc (..)
import Toy.Doc.Proofs (..)
import Toy.Syntax (..)
import Toy.Syntax.Proofs (..)
import Toy.Fmt (..)
import Std (Bool, DecEq, Eq, List, Nat, Option, Parse, Text, Void)

-- The lines that wait above a statement.

--| `spacedNotes` of trivia listed the newest first: the comment lines
--| waiting, and whether a blank line waits after the last of them.
def notesOf (note: Comment → a) (trivia: List Trivia): (List (Spaced a), Bool) := match trivia with
  | [] => ([], False)
  | [piece, ..older] => noteStep note (notesOf note older) piece

theorem notesOfReverse ∀ (note: Comment → a) (trivia: List Trivia):
    spacedNotes note trivia.reverse = notesOf note trivia :=
  match trivia with
    | [] => rfl
    | [piece, ..older] =>
      Eq.trans
        (Eq.cong ((list: List Trivia) => spacedNotes note list) (List.reverseCons piece older))
        (Eq.trans
          (List.foldLeftAppend older.reverse (([], False): (List (Spaced a), Bool)) [piece] (noteStep note))
          (Eq.cong ((found: (List (Spaced a), Bool)) => noteStep note found piece) (notesOfReverse note older)))

--| The trivia waiting once a line's blank line, if it has one, is seen.
def blankOf (blankBefore: Bool) (pending: List Trivia): List Trivia := match blankBefore with
  | True => addBlank pending
  | False => pending

theorem blankSeen ∀ (blankBefore: Bool) (seen: Views):
    viewsFrom seen (blankEvents blankBefore) = { views = seen.views, pending = blankOf blankBefore seen.pending } :=
  match blankBefore with
    | True => rfl
    | False =>
      match seen with
        | { views, pending } => rfl

--| A blank line after comment lines is remembered for the next line.
theorem blankNotes ∀ (note: Comment → a) (blankBefore: Bool) (pending: List Trivia) (lines: List (Spaced a))
    (waits: notesOf note pending = (lines, False)):
    notesOf note (blankOf blankBefore pending) = (lines, blankBefore) :=
  match blankBefore with
    | False => waits
    | True =>
      match pending, waits with
        | [], waits => Eq.cong ((found: (List (Spaced a), Bool)) => (found.fst, True)) waits
        | [OwnLine comment, ..older], waits => Eq.cong ((found: (List (Spaced a), Bool)) => (found.fst, True)) waits
        | [BlankLine, ..older], waits =>
          Void.exfalso (Bool.falseNotTrue (Eq.sym (Eq.cong ((found: (List (Spaced a), Bool)) => found.snd) waits)))

--| A comment line joins the lines waiting, with its blank line.
theorem noteNotes ∀ (note: Comment → a) (blankBefore: Bool) (pending: List Trivia)
    (lines: List (Spaced a)) (comment: Comment)
    (waits: notesOf note pending = (lines, False)):
    notesOf note [OwnLine comment, ..blankOf blankBefore pending]
      = (lines ++ [{ blankBefore, line = note comment }], False) :=
  Eq.cong
    ((found: (List (Spaced a), Bool)) => noteStep note found (OwnLine comment))
    (blankNotes note blankBefore pending lines waits)

theorem notedOf ∀ (above: List Trivia) (lines: List (Spaced Statement)) (blankBefore: Bool) (line: Statement)
    (found: spacedNotes StatementNote above = (lines, blankBefore)):
    notedStatement above line = lines ++ [{ blankBefore, line }] :=
  Eq.cong ((pair: (List (Spaced Statement), Bool)) => pair.fst ++ [{ blankBefore = pair.snd, line }]) found

theorem unspacedFront ∀ (pending more: List (Spaced a)) (last: Spaced a)
    (unspaced: Unspaced (pending ++ [last, ..more])):
    Unspaced (pending ++ [last]) :=
  match pending, unspaced with
    | [], unspaced =>
      Eq.cong
        ((first: Spaced a) => [first])
        (List.consInjectiveHead { last | blankBefore = False } last more more unspaced)
    | [head, ..tail], unspaced =>
      Eq.cong
        ((first: Spaced a) => [first, ..tail ++ [last]])
        (List.consInjectiveHead
          { head | blankBefore = False }
          head
          (tail ++ [last, ..more])
          (tail ++ [last, ..more])
          unspaced)

theorem firstBlankSame ∀ (isFirst: Bool) (lines: List (Spaced Statement))
    (unspaced: isFirst = True → Unspaced lines):
    firstBlank isFirst lines = lines :=
  match isFirst, unspaced with
    | False, _ => rfl
    | True, unspaced => unspaced rfl

--| The lines the parser gives a statement whose first token holds what
--| waited above it: the comment lines waiting, then the statement.
theorem notedLine ∀ (isFirst: Bool) (pending: List Trivia) (lines more: List (Spaced Statement)) (blankBefore: Bool)
    (line: Statement) (above: List Trivia)
    (same: above = (blankOf blankBefore pending).reverse)
    (waits: notesOf StatementNote pending = (lines, False))
    (unspaced: isFirst = True → Unspaced (lines ++ [{ blankBefore, line }, ..more])):
    firstBlank isFirst (notedStatement above line) = lines ++ [{ blankBefore, line }] :=
  let noted: notedStatement above line = lines ++ [{ blankBefore, line }] :=
    notedOf above lines blankBefore line
      (rewrite same in
        Eq.trans
          (notesOfReverse StatementNote (blankOf blankBefore pending))
          (blankNotes StatementNote blankBefore pending lines waits))
  rewrite noted in
    firstBlankSame isFirst (lines ++ [{ blankBefore, line }]) (first =>
      unspacedFront lines more { blankBefore, line } (unspaced first))

-- Views that leave lines waiting.

--| `events`, seen with `pending` waiting, are the views `found` (in
--| source order) and leave `left` waiting: `Seen` where comment lines may
--| come last.
def SeenTo (pending: List Trivia) (events: List Event) (found: List TokenView) (left: List Trivia): Prop :=
  ∀ (earlier: List TokenView) => viewsFrom { views = earlier, pending } events
    = { views = found.reverse ++ earlier, pending = left }

theorem seenToThen ∀ (pending middle left: List Trivia) (front back: List Event) (first second: List TokenView)
    (one: SeenTo pending front first middle)
    (other: SeenTo middle back second left):
    SeenTo pending (front ++ back) (first ++ second) left :=
  earlier =>
    Eq.trans
      (viewsAppend { views = earlier, pending } front back)
      (Eq.trans
        (Eq.cong ((seen: Views) => viewsFrom seen back) (one earlier))
        (Eq.trans
          (other (first.reverse ++ earlier))
          (Eq.cong
            ((views: List TokenView) => ({ views, pending = left }: Views))
            (Eq.trans
              (Eq.sym (List.appendAssoc second.reverse first.reverse earlier))
              (Eq.cong ((front: List TokenView) => front ++ earlier) (Eq.sym (List.reverseAppend first second)))))))

theorem seenBlank ∀ (blankBefore: Bool) (pending left: List Trivia) (events: List Event) (found: List TokenView)
    (seen: SeenTo (blankOf blankBefore pending) events found left):
    SeenTo pending (blankEvents blankBefore ++ events) found left :=
  earlier =>
    Eq.trans
      (viewsAppend { views = earlier, pending } (blankEvents blankBefore) events)
      (Eq.trans
        (Eq.cong ((before: Views) => viewsFrom before events) (blankSeen blankBefore { views = earlier, pending }))
        (seen earlier))

theorem seenNote ∀ (comment: Comment) (column: Nat) (pending left: List Trivia)
    (events: List Event) (found: List TokenView)
    (fine: IsComment comment.text)
    (seen: SeenTo [OwnLine comment, ..pending] events found left):
    SeenTo pending ([{ word = comment.text, start = Some column }] ++ events) found left :=
  match comment, fine, seen with
    | { text }, fine, seen => earlier =>
      Eq.trans
        (Eq.cong
          ((before: Views) => viewsFrom before events)
          (ownLineEvent { views = earlier, pending } text column fine))
        (seen earlier)

-- Offsets in source order.

--| Every token's offset is below `bound`.
def Below (bound: Nat): List (Parse.Located Token) → Prop
  | [] => True
  | [token, ..rest] => token.offset < bound ∧ Below bound rest

theorem risingFront ∀ (front back: List (Parse.Located Token))
    (rising: Rising ((front ++ back).map (found => found.offset))):
    Rising (front.map (found => found.offset)) :=
  match front, rising with
    | [], _ => rfl
    | [only], _ => rfl
    | [lower, higher, ..rest], Both above more => Both above (risingFront [higher, ..rest] back more)

theorem risingBack ∀ (front back: List (Parse.Located Token))
    (rising: Rising ((front ++ back).map (found => found.offset))):
    Rising (back.map (found => found.offset)) :=
  match front, rising with
    | [], rising => rising
    | [only], rising =>
      match back, rising with
        | [], _ => rfl
        | [next, ..more], Both _ later => later
    | [lower, higher, ..rest], Both _ more => risingBack [higher, ..rest] back more

theorem risingBelow ∀ (tokens: List (Parse.Located Token))
    (next: Parse.Located Token) (more: List (Parse.Located Token))
    (rising: Rising ((tokens ++ [next, ..more]).map (found => found.offset))):
    Below next.offset tokens :=
  match tokens, rising with
    | [], _ => rfl
    | [only], Both above _ => Both above rfl
    | [lower, higher, ..rest], Both above later =>
      match risingBelow [higher, ..rest] next more later with
        | Both under others => Both (omega [above, under]) (Both under others)

theorem belowNotAt ∀ (bound: Nat) (tokens: List (Parse.Located Token))
    (below: Below bound tokens):
    NotAt bound tokens :=
  match tokens, below with
    | [], _ => rfl
    | [token, ..rest], Both under others => Both (omega [under]) (belowNotAt bound rest others)

--| The tokens after a statement's first aren't its first.
theorem laterApart ∀ (column: Nat) (first: Parse.Located Token) (others: List (Parse.Located Token))
    (rising: Rising ([first, ..others].map (found => found.offset))):
    AllApart (InStatement column first.offset) others :=
  risingApart column first.offset first.offset others omega rising

-- Where a token starts, from its view.

theorem startColumn ∀ (token: Parse.Located Token) (column: Nat)
    (starts: (viewOf token).start = Some column):
    token.value.startsLine = True ∧ token.value.column = column :=
  match token, starts with
    | { value = { kind, startsLine = True, column = indent, above, trailing }, offset, length }, starts =>
      Both rfl (Option.someInjective starts)

theorem startsLow ∀ (token: Parse.Located Token) (column: Nat)
    (starts: (viewOf token).start = Some column):
    (token.value.startsLine && token.value.column <= column) = True :=
  match token, starts with
    | { value = { kind, startsLine = True, column = indent, above, trailing }, offset, length }, starts =>
      omega [Option.someInjective starts]

theorem startsAtLine ∀ (token: Parse.Located Token) (column: Nat)
    (starts: (viewOf token).start = Some column):
    (token.value.startsLine && token.value.column == column) = True :=
  match token, starts with
    | { value = { kind, startsLine = True, column = indent, above, trailing }, offset, length }, starts =>
      omega [Option.someInjective starts]

theorem startsDeeper ∀ (token: Parse.Located Token) (column deeper: Nat)
    (below: column < deeper)
    (starts: (viewOf token).start = Some deeper):
    (token.value.startsLine && token.value.column > column) = True :=
  match token, starts with
    | { value = { kind, startsLine = True, column = indent, above, trailing }, offset, length }, starts =>
      omega [Option.someInjective starts, below]

--| The views of a block's lines start a line at its column, if there
--| are any.
def StartsAt (column: Nat) (views: List TokenView): Prop := match views with
  | [] => True
  | [first, .._] => first.start = Some column

-- What follows a statement.

theorem lowUnallowed ∀ (startsLine: Bool) (indent column: Nat) (same: Bool)
    (low: (startsLine && indent <= column) = True)
    (apart: same = False):
    (not startsLine || indent > column || same) = False :=
  match startsLine, low with
    | True, low =>
      let shallow: (indent > column) = False := omega [low]
      rewrite shallow, apart in rfl

--| What settles a statement's tokens ends its expression too: a line
--| start no deeper than the statement, at another offset than its first
--| token's, is not allowed in it.
theorem settledAfter ∀ (column from: Nat) (front: List (Parse.Located Token))
    (first: Parse.Located Token) (others rest: List (Parse.Located Token))
    (settled: Settled (InStatement column from) (front ++ [first, ..others]) rest):
    After (InStatement column first.offset) [first, ..others] rest :=
  match rest, settled with
    | [], settled => Both (Both rfl rfl) rfl
    | [next, ..more], Inl closes =>
      match closerReserved next.value.kind closes with
        | Witness keyword reserved =>
          Both (endsAtReserved (InStatement column first.offset) next keyword more reserved) (Inl closes)
    | [next, ..more], Inr (Both low clear) =>
      match notAtBack next.offset front [first, ..others] clear with
        | Both apart othersClear =>
          Both
            (endsUnallowed
              (InStatement column first.offset)
              next
              more
              (lowUnallowed next.value.startsLine next.value.column column (next.offset == first.offset) low apart))
            (Inr (Both low (Both apart othersClear)))

theorem afterBack ∀ (layout: Layout) (front back rest: List (Parse.Located Token))
    (after: After layout (front ++ back) rest):
    After layout back rest :=
  match after with | Both ends settled => Both ends (settledBack layout front back rest settled)

--| A statement of a block ends before the next line of the block, and
--| the last one before what the block's tokens are settled by.
theorem lineAfter ∀ (column: Nat) (first: Parse.Located Token) (others later rest: List (Parse.Located Token))
    (starts: StartsAt column (later.map viewOf))
    (rising: Rising (([first, ..others] ++ later).map (found => found.offset)))
    (settled: Settled (InStatement column 0) ([first, ..others] ++ later) rest):
    After (InStatement column first.offset) [first, ..others] (later ++ rest) :=
  match later, starts, rising, settled with
    | [], _, _, settled =>
      settledAfter column 0 [] first others rest (rewrite List.appendNil others at settled in settled)
    | [next, ..more], starts, rising, _ =>
      settledAfter column 0 [] first others
        ([next, ..more] ++ rest)
        (Inr
          (Both
            (startsLow next column starts)
            (belowNotAt next.offset [first, ..others] (risingBelow [first, ..others] next more rising))))

--| What settles a statement settles a block inside it, and ends the
--| block.
theorem settledDeeper ∀ (column from deeper: Nat) (tokens rest: List (Parse.Located Token))
    (below: column < deeper)
    (settled: Settled (InStatement column from) tokens rest):
    Settled (InStatement deeper 0) tokens rest ∧ BlockEnds deeper rest :=
  match rest, settled with
    | [], _ => Both rfl (Inl rfl)
    | [next, ..more], Inl closes => Both (Inl closes) (Inr closes)
    | [next, ..more], Inr (Both low clear) =>
      match lowLine next.value.startsLine next.value.column column deeper False low below rfl with
        | Both _ (Both lower elsewhere) => Both (Inr (Both lower clear)) (Inl elsewhere)

theorem startNotLet ∀ (kind: Kind) (starts: startsExpression kind = True): kind ≠ Reserved LetKeyword := same =>
  Bool.falseNotTrue (rewrite same at starts in starts)

-- Expressions outside brackets, `if` included.

theorem postfixChain ∀ (expr: Expr) (postfix: expr.isPostfix = True): expr.isChain = True := match expr, postfix with
  | Var _ _, _ => rfl
  | NumberLiteral _ _, _ => rfl
  | StringLiteral _ _, _ => rfl
  | Bracketed _ _ _, _ => rfl
  | ListLiteral _ _ _, _ => rfl
  | Call _ _ _ _, _ => rfl
  | Field _ _ _ _, _ => rfl

theorem operandChain ∀ (expr: Expr) (operand: expr.isOperand = True): expr.isChain = True := match expr, operand with
  | Var _ _, _ => rfl
  | NumberLiteral _ _, _ => rfl
  | StringLiteral _ _, _ => rfl
  | Bracketed _ _ _, _ => rfl
  | ListLiteral _ _ _, _ => rfl
  | Call _ _ _ _, _ => rfl
  | Field _ _ _ _, _ => rfl
  | Negate _ _, _ => rfl

--| An `if` stands only as a whole expression: an operator chain or an
--| operand of the parser's shape holds none outside brackets.
theorem chainNoIf ∀ (expr: Expr) (shaped: Shaped expr) (chain: expr.isChain = True): NoIf expr :=
  match expr, shaped, chain with
    | Var _ _, _, _ => rfl
    | NumberLiteral _ _, _, _ => rfl
    | StringLiteral _ _, _, _ => rfl
    | Bracketed _ _ _, _, _ => rfl
    | ListLiteral _ _ _, _, _ => rfl
    | Call callee _ _ _, Both postfix (Both shapedCallee _), _ =>
      chainNoIf callee shapedCallee (postfixChain callee postfix)
    | Field target _ _ _, Both postfix shapedTarget, _ => chainNoIf target shapedTarget (postfixChain target postfix)
    | Negate _ operand, Both isOperand shapedOperand, _ =>
      chainNoIf operand shapedOperand (operandChain operand isOperand)
    | Binary _ _ left right, Both _ (Both _ (Both leftChain (Both rightChain (Both shapedLeft shapedRight)))), _ =>
      Both (chainNoIf left shapedLeft leftChain) (chainNoIf right shapedRight rightChain)

--| `Spells` outside brackets, in a statement at `column`: the tokens'
--| offsets rise too, which a block inside the expression needs to tell
--| its lines apart.
def SpellsOut (column: Nat) (pending: List Trivia) (head: Option Nat → Prop) (expr: Expr) (events: List Event): Prop :=
  ∃ (first: TokenView) => ∃ (others: List TokenView) => Seen pending events [first, ..others]
    ∧ (∀ (from: Nat) (tokens: List (Parse.Located Token)) => tokens.map viewOf = [first, ..others]
      → Rising (tokens.map (found => found.offset))
      → Leads (InStatement column from) pending head expr.firstAbove tokens
      → Spelled (InStatement column from) expr tokens)
    ∧ head first.start
    ∧ first.above = (waiting pending expr.firstAbove).reverse

theorem plainOut ∀ (column: Nat) (head: Option Nat → Prop) (expr: Expr) (events: List Event) (pending: List Trivia)
    (shaped: Shaped expr)
    (lexical: Lexical expr)
    (headed: HeadedExpr False expr)
    (plain: NoIf expr)
    (laid: Events (Deeper column) head expr events):
    SpellsOut column pending head expr events :=
  match exprSpells
    (Deeper column)
    (InStatement column 0)
    head
    expr
    events
    pending
    rfl
    shaped
    lexical
    headed
    plain
    laid with
    | Witness first (Witness others (Both seen (Both spells starts))) =>
      Witness first
        (Witness others (Both seen (Both (from tokens same rising leads => spells from tokens same leads) starts)))

--| The comments of a token that isn't its statement's first, from its
--| view.
theorem apartComments ∀ (column from: Nat) (token: Parse.Located Token) (kind: Kind)
    (start: Option Nat) (comments: Comments)
    (apart: (token.offset == from) = False)
    (same: viewOf token = tokenView [] kind start comments):
    comments = (InStatement column from).comments token :=
  match isFirst: token.offset == from, apart with | False, _ => viewComments token kind start comments same

--| The comments of a statement's keyword, which holds none above it in
--| the tree.
theorem keywordComments ∀ (column: Nat) (first: Parse.Located Token) (pending: List Trivia) (kind: Kind)
    (start: Option Nat) (comments: Comments)
    (none: comments.above = [])
    (same: viewOf first = tokenView pending kind start comments):
    comments = (InStatement column first.offset).comments first :=
  match comments, none, same with
    | { above = [], after }, _, same =>
      firstComments column first.offset first pending kind start after (sameOffset first.offset) same

--| What tokens with an expression's views have to do outside brackets:
--| with rising offsets, leading, they spell it.
def IfGoal (column from: Nat) (pending: List Trivia) (head: Option Nat → Prop) (above: List Comment)
    (expr: Expr) (tokens: List (Parse.Located Token)):
    Prop :=
  Rising (tokens.map (found => found.offset))
    → Leads (InStatement column from) pending head above tokens
    → Spelled (InStatement column from) expr tokens

-- Bodies and blocks.

--| Tokens with the views of a body's events, rising and none of them
--| the statement's first, spell the body before whatever may follow it.
def BodySpells (column: Nat) (body: Body) (events: List Event): Prop :=
  ∃ (first: TokenView) => ∃ (others: List TokenView) => Seen [] events [first, ..others]
    ∧ (∀ (from: Nat) (tokens rest: List (Parse.Located Token)) => tokens.map viewOf = [first, ..others]
      → Rising (tokens.map (found => found.offset))
      → AllApart (InStatement column from) tokens
      → After (InStatement column from) tokens rest
      → SpelledBody (InStatement column from) body tokens rest)

--| What is known of the lines left in a block: the last is a statement,
--| and when none is left nothing waits.
def LinesClose (noted: List (Spaced Statement)) (pending: List Trivia) (lines: List (Spaced Statement)): Prop :=
  match lines with
    | [] => noted = [] ∧ pending = []
    | [_, .._] => ClosedLines lines

--| The views of lines that end in a statement: one at least, the first
--| starting a line at the block's column.
def LinesOpen (column: Nat) (lines: List (Spaced Statement)) (views: List TokenView): Prop := match lines with
  | [] => views = []
  | [_, .._] =>
    ∃ (first: TokenView) => ∃ (others: List TokenView) => views = [first, ..others] ∧ first.start = Some column

--| What tokens with a block's views have to do: with rising offsets,
--| settled by what follows the block, they spell its lines.
def LinesGoal (column: Nat) (isFirst: Bool)
    (noted lines: List (Spaced Statement)) (rest tokens: List (Parse.Located Token)):
    Prop :=
  Rising (tokens.map (found => found.offset))
    → Settled (InStatement column 0) tokens rest
    → SpelledLines column isFirst noted lines tokens rest

def LinesSpell (column: Nat) (isFirst: Bool) (noted lines: List (Spaced Statement))
    (pending: List Trivia) (events: List Event):
    Prop :=
  ∃ (views: List TokenView) => SeenTo pending events views []
    ∧ LinesOpen column lines views
    ∧ (∀ (tokens rest: List (Parse.Located Token)) => tokens.map viewOf = views
      → BlockEnds column rest
      → LinesGoal column isFirst noted lines rest tokens)

theorem opensStarts ∀ (column: Nat) (lines: List (Spaced Statement)) (views: List TokenView)
    (opens: LinesOpen column lines views):
    StartsAt column views :=
  match lines, opens with
    | [], opens => rewrite opens in rfl
    | [_, .._], Witness first (Witness others (Both same starts)) => rewrite same in starts

theorem opensSome ∀ (column: Nat) (lines: List (Spaced Statement)) (views: List TokenView)
    (closed: ClosedLines lines)
    (opens: LinesOpen column lines views):
    ∃ (first: TokenView) => ∃ (others: List TokenView) => views = [first, ..others] ∧ first.start = Some column :=
  match lines, closed, opens with
    | [], never, _ => Void.exfalso (Bool.falseNotTrue never)
    | [_, .._], _, opens => opens

theorem opensNote ∀ (column: Nat) (note: Spaced Statement) (more: List (Spaced Statement)) (views: List TokenView)
    (some: LinesClose [] [] more → ClosedLines more)
    (opens: LinesOpen column more views):
    LinesOpen column [note, ..more] views :=
  match more, some, opens with
    | [], some, _ => Void.exfalso (Bool.falseNotTrue (some (Both rfl rfl)))
    | [_, .._], _, opens => opens

theorem closingNote ∀ (noted: List (Spaced Statement)) (pending: List Trivia) (blankBefore: Bool)
    (comment: Comment) (more: List (Spaced Statement))
    (closed: ClosedLines [{ blankBefore, line = StatementNote comment }, ..more]):
    LinesClose noted pending more ∧ ClosedLines more :=
  match more, closed with
    | [], never => Void.exfalso (Bool.falseNotTrue never)
    | [_, .._], closed => Both closed closed

theorem closingCoded ∀ (line: Spaced Statement) (more: List (Spaced Statement))
    (closed: ClosedLines [line, ..more]):
    LinesClose [] [] more :=
  match more, closed with
    | [], _ => Both rfl rfl
    | [_, .._], closed => closed

theorem closedSome ∀ (line: Spaced Statement) (more: List (Spaced Statement))
    (closed: LinesClose [] [] [line, ..more]):
    ClosedLines [line, ..more] :=
  closed

theorem laterOfLines ∀ (column: Nat) (statements: List (Spaced Statement)) (events: List Event)
    (unspaced: Unspaced statements)
    (laid: LineEvents column statements events):
    LaterLines column statements events :=
  match statements, unspaced, laid with
    | [], _, laid => laid
    | [{ blankBefore, line }, ..rest], unspaced, laid =>
      let none: False = blankBefore := Eq.cong firstBlankBefore unspaced
      rewrite <- none in Witness events (Both rfl laid)

theorem closingBody ∀ (statements: List (Spaced Statement))
    (closed: ClosedLines statements):
    LinesClose [] [] statements :=
  match statements, closed with
    | [], never => Void.exfalso (Bool.falseNotTrue never)
    | [_, .._], closed => closed

theorem falseFirst ∀ (goal: Prop) (never: False = True): goal := Void.exfalso (Bool.falseNotTrue never)

--| Tokens with the views of an expression's events spell it outside
--| brackets, where an `if`'s branch may be a block.
theorem exprOut ∀ (column: Nat) (head: Option Nat → Prop) (expr: Expr) (events: List Event) (pending: List Trivia)
    (shaped: Shaped expr)
    (lexical: Lexical expr)
    (headed: HeadedExpr False expr)
    (laid: Events (Deeper column) head expr events):
    SpellsOut column pending head expr events :=
  match expr, shaped, lexical, headed, laid with
    | Var name comments, shaped, lexical, headed, laid =>
      plainOut column head (Var name comments) events pending shaped lexical headed rfl laid
    | NumberLiteral digits comments, shaped, lexical, headed, laid =>
      plainOut column head (NumberLiteral digits comments) events pending shaped lexical headed rfl laid
    | StringLiteral written comments, shaped, lexical, headed, laid =>
      plainOut column head (StringLiteral written comments) events pending shaped lexical headed rfl laid
    | Bracketed open inner close, shaped, lexical, headed, laid =>
      plainOut column head (Bracketed open inner close) events pending shaped lexical headed rfl laid
    | ListLiteral open items close, shaped, lexical, headed, laid =>
      plainOut column head (ListLiteral open items close) events pending shaped lexical headed rfl laid
    | Call callee open arguments close, shaped, lexical, headed, laid =>
      plainOut column head
        (Call callee open arguments close)
        events
        pending
        shaped
        lexical
        headed
        (chainNoIf (Call callee open arguments close) shaped rfl)
        laid
    | Field target dot name nameComments, shaped, lexical, headed, laid =>
      plainOut column head
        (Field target dot name nameComments)
        events
        pending
        shaped
        lexical
        headed
        (chainNoIf (Field target dot name nameComments) shaped rfl)
        laid
    | Negate minus operand, shaped, lexical, headed, laid =>
      plainOut column head
        (Negate minus operand)
        events
        pending
        shaped
        lexical
        headed
        (chainNoIf (Negate minus operand) shaped rfl)
        laid
    | Binary operator sign left right, shaped, lexical, headed, laid =>
      plainOut column head
        (Binary operator sign left right)
        events
        pending
        shaped
        lexical
        headed
        (chainNoIf (Binary operator sign left right) shaped rfl)
        laid
    | If ({ above, after }) condition thenComments whenTrue elseComments whenFalse, Both shapedCondition
        (Both shapedTrue shapedFalse), Both fineIf
        (Both conditionLexical (Both fineThen (Both trueLexical (Both fineElse falseLexical)))), Both headedCondition
        (Both headedTrue headedFalse), Witness ifEvents
        (Witness afterIf
          (Both ifSplit
            (Both ifLaid
              (Witness conditionEvents
                (Witness afterCondition
                  (Both conditionSplit
                    (Both conditionLaid
                      (Witness thenEvents
                        (Witness afterThen
                          (Both thenSplit
                            (Both thenLaid
                              (Witness trueEvents
                                (Witness afterTrue
                                  (Both trueSplit
                                    (Both trueLaid
                                      (Witness elseEvents
                                        (Witness falseEvents
                                          (Both elseSplit (Both elseLaid falseLaid))))))))))))))))))) =>
      match tokenSeen head
        { above, after }
        "if"
        (Reserved IfKeyword)
        ifEvents
        pending
        fineIf
        (seen start => keywordEvent seen IfKeyword start)
        ifLaid, exprOut column
        (Deeper column).allows
        condition
        conditionEvents
        []
        shapedCondition
        conditionLexical
        headedCondition
        conditionLaid, tokenSeen
        (Deeper column).allows
        thenComments
        "then"
        (Reserved ThenKeyword)
        thenEvents
        []
        fineThen
        (seen start => keywordEvent seen ThenKeyword start)
        thenLaid, bodyOut column whenTrue trueEvents shapedTrue trueLexical headedTrue trueLaid, tokenSeen
        (Deeper column).reaches
        elseComments
        "else"
        (Reserved ElseKeyword)
        elseEvents
        []
        fineElse
        (seen start => keywordEvent seen ElseKeyword start)
        elseLaid, bodyOut column whenFalse falseEvents shapedFalse falseLexical headedFalse falseLaid with
        | Witness ifStart (Both ifAllowed ifSeen), Witness conditionFirst
            (Witness conditionOthers (Both conditionSeen (Both conditionSpells _))), Witness thenStart
            (Both thenAllowed thenSeen), Witness trueFirst
            (Witness trueOthers (Both trueSeen trueSpells)), Witness elseStart
            (Both elseReaches elseSeen), Witness falseFirst (Witness falseOthers (Both falseSeen falseSpells)) =>
          Witness
            (tokenView pending (Reserved IfKeyword) ifStart { above, after })
            (Witness
              ([conditionFirst, ..conditionOthers]
                ++ ([(tokenView [] (Reserved ThenKeyword) thenStart thenComments)]
                  ++ ([trueFirst, ..trueOthers]
                    ++ ([(tokenView [] (Reserved ElseKeyword) elseStart elseComments)]
                      ++ [falseFirst, ..falseOthers]))))
              (Both
                (rewrite ifSplit, conditionSplit, thenSplit, trueSplit, elseSplit in
                  seenThen pending ifEvents
                    (conditionEvents ++ (thenEvents ++ (trueEvents ++ (elseEvents ++ falseEvents))))
                    [(tokenView pending (Reserved IfKeyword) ifStart { above, after })]
                    ([conditionFirst, ..conditionOthers]
                      ++ ([(tokenView [] (Reserved ThenKeyword) thenStart thenComments)]
                        ++ ([trueFirst, ..trueOthers]
                          ++ ([(tokenView [] (Reserved ElseKeyword) elseStart elseComments)]
                            ++ [falseFirst, ..falseOthers]))))
                    ifSeen
                    (seenThen [] conditionEvents
                      (thenEvents ++ (trueEvents ++ (elseEvents ++ falseEvents)))
                      [conditionFirst, ..conditionOthers]
                      ([(tokenView [] (Reserved ThenKeyword) thenStart thenComments)]
                        ++ ([trueFirst, ..trueOthers]
                          ++ ([(tokenView [] (Reserved ElseKeyword) elseStart elseComments)]
                            ++ [falseFirst, ..falseOthers])))
                      conditionSeen
                      (seenThen [] thenEvents
                        (trueEvents ++ (elseEvents ++ falseEvents))
                        [(tokenView [] (Reserved ThenKeyword) thenStart thenComments)]
                        ([trueFirst, ..trueOthers]
                          ++ ([(tokenView [] (Reserved ElseKeyword) elseStart elseComments)]
                            ++ [falseFirst, ..falseOthers]))
                        thenSeen
                        (seenThen [] trueEvents
                          (elseEvents ++ falseEvents)
                          [trueFirst, ..trueOthers]
                          ([(tokenView [] (Reserved ElseKeyword) elseStart elseComments)]
                            ++ [falseFirst, ..falseOthers])
                          trueSeen
                          (seenThen [] elseEvents falseEvents
                            [(tokenView [] (Reserved ElseKeyword) elseStart elseComments)]
                            [falseFirst, ..falseOthers]
                            elseSeen
                            falseSeen)))))
                (Both
                  (from tokens same =>
                    viewsCons
                      (later =>
                        IfGoal column from pending head above
                          (If ({ above, after }) condition thenComments whenTrue elseComments whenFalse)
                          later)
                      tokens
                      (tokenView pending (Reserved IfKeyword) ifStart { above, after })
                      ([conditionFirst, ..conditionOthers]
                        ++ ([(tokenView [] (Reserved ThenKeyword) thenStart thenComments)]
                          ++ ([trueFirst, ..trueOthers]
                            ++ ([(tokenView [] (Reserved ElseKeyword) elseStart elseComments)]
                              ++ [falseFirst, ..falseOthers]))))
                      same
                      (ifToken afterIfTokens ifSame afterIfSame =>
                        viewsSplit
                          (later =>
                            IfGoal column from pending head above
                              (If ({ above, after }) condition thenComments whenTrue elseComments whenFalse)
                              [ifToken, ..later])
                          afterIfTokens
                          [conditionFirst, ..conditionOthers]
                          ([(tokenView [] (Reserved ThenKeyword) thenStart thenComments)]
                            ++ ([trueFirst, ..trueOthers]
                              ++ ([(tokenView [] (Reserved ElseKeyword) elseStart elseComments)]
                                ++ [falseFirst, ..falseOthers])))
                          afterIfSame
                          (conditionTokens afterConditionTokens conditionSame afterConditionSame =>
                            viewsCons
                              (later =>
                                IfGoal column from pending head above
                                  (If ({ above, after }) condition thenComments whenTrue elseComments whenFalse)
                                  [ifToken, ..conditionTokens ++ later])
                              afterConditionTokens
                              (tokenView [] (Reserved ThenKeyword) thenStart thenComments)
                              ([trueFirst, ..trueOthers]
                                ++ ([(tokenView [] (Reserved ElseKeyword) elseStart elseComments)]
                                  ++ [falseFirst, ..falseOthers]))
                              afterConditionSame
                              (thenToken afterThenTokens thenSame afterThenSame =>
                                viewsSplit
                                  (later =>
                                    IfGoal column from pending head above
                                      (If ({ above, after }) condition thenComments whenTrue elseComments whenFalse)
                                      [ifToken, ..conditionTokens ++ [thenToken, ..later]])
                                  afterThenTokens
                                  [trueFirst, ..trueOthers]
                                  ([(tokenView [] (Reserved ElseKeyword) elseStart elseComments)]
                                    ++ [falseFirst, ..falseOthers])
                                  afterThenSame
                                  (trueTokens afterTrueTokens trueSame afterTrueSame =>
                                    viewsCons
                                      (later =>
                                        IfGoal column from pending head above
                                          (If ({ above, after }) condition thenComments whenTrue elseComments whenFalse)
                                          [ifToken, ..conditionTokens ++ [thenToken, ..trueTokens ++ later]])
                                      afterTrueTokens
                                      (tokenView [] (Reserved ElseKeyword) elseStart elseComments)
                                      [falseFirst, ..falseOthers]
                                      afterTrueSame
                                      (elseToken falseTokens elseSame falseSame rising leads =>
                                        let risingRest :=
                                          risingBack
                                            [ifToken]
                                            (conditionTokens ++ [thenToken, ..trueTokens ++ [elseToken, ..falseTokens]])
                                            rising
                                        let risingAfterCondition :=
                                          risingBack conditionTokens
                                            [thenToken, ..trueTokens ++ [elseToken, ..falseTokens]]
                                            risingRest
                                        let risingAfterThen :=
                                          risingBack
                                            [thenToken]
                                            (trueTokens ++ [elseToken, ..falseTokens])
                                            risingAfterCondition
                                        let apartAfterCondition :=
                                          apartBack
                                            (InStatement column from)
                                            conditionTokens
                                            [thenToken, ..trueTokens ++ [elseToken, ..falseTokens]]
                                            leads.left
                                        let apartAfterTrue :=
                                          apartBack
                                            (InStatement column from)
                                            trueTokens
                                            [elseToken, ..falseTokens]
                                            apartAfterCondition.right
                                        match headFits
                                          (InStatement column from)
                                          pending
                                          head
                                          above
                                          ifToken
                                          (conditionTokens ++ [thenToken, ..trueTokens ++ [elseToken, ..falseTokens]])
                                          (Reserved IfKeyword)
                                          ifStart
                                          after
                                          leads
                                          ifAllowed
                                          ifSame, innerFits
                                          (Deeper column)
                                          (InStatement column from)
                                          thenToken
                                          (Reserved ThenKeyword)
                                          thenStart
                                          thenComments
                                          rfl
                                          apartAfterCondition.left
                                          thenAllowed
                                          thenSame with
                                          | Both ifKind (Both ifAllows ifNotes), Both thenKind
                                              (Both thenAllows thenNotes) =>
                                            Witness ifToken
                                              (Witness conditionTokens
                                                (Witness thenToken
                                                  (Witness trueTokens
                                                    (Witness elseToken
                                                      (Witness falseTokens
                                                        (Both rfl
                                                          (Both ifKind
                                                            (Both ifAllows
                                                              (Both thenKind
                                                                (Both thenAllows
                                                                  (Both
                                                                    (Eq.cong ((view: TokenView) => view.kind) elseSame)
                                                                    (Both
                                                                      (reachesElse column column from elseToken
                                                                          elseStart rfl elseReaches
                                                                          (Eq.cong
                                                                            ((view: TokenView) => view.start)
                                                                            elseSame))
                                                                      (Both
                                                                        (conditionSpells from conditionTokens
                                                                            conditionSame
                                                                            (risingFront conditionTokens
                                                                              [
                                                                                thenToken,
                                                                                ..trueTokens
                                                                                  ++ [elseToken, ..falseTokens]
                                                                              ]
                                                                              risingRest)
                                                                            (innerLeads
                                                                              (Deeper column)
                                                                              (InStatement column from)
                                                                              condition.firstAbove
                                                                              conditionTokens
                                                                              rfl
                                                                              (apartFront
                                                                                (InStatement column from)
                                                                                conditionTokens
                                                                                [
                                                                                  thenToken,
                                                                                  ..trueTokens
                                                                                    ++ [elseToken, ..falseTokens]
                                                                                ]
                                                                                leads.left)))
                                                                        (Both
                                                                          (rest follows =>
                                                                            trueSpells from trueTokens rest trueSame
                                                                              (risingFront trueTokens
                                                                                [elseToken, ..falseTokens]
                                                                                risingAfterThen)
                                                                              (apartFront
                                                                                (InStatement column from)
                                                                                trueTokens
                                                                                [elseToken, ..falseTokens]
                                                                                apartAfterCondition.right)
                                                                              follows)
                                                                          (Both
                                                                            (rest follows =>
                                                                              falseSpells from falseTokens rest
                                                                                  falseSame
                                                                                  (risingBack
                                                                                    [elseToken]
                                                                                    falseTokens
                                                                                    (risingBack trueTokens
                                                                                      [elseToken, ..falseTokens]
                                                                                      risingAfterThen))
                                                                                  apartAfterTrue.right
                                                                                  follows)
                                                                            (Both ifNotes
                                                                              (Both thenNotes
                                                                                (apartComments column from elseToken
                                                                                  (Reserved ElseKeyword)
                                                                                  elseStart
                                                                                  elseComments
                                                                                  apartAfterTrue.left
                                                                                  elseSame))))))))))))))))))))))))
                  (Both ifAllowed rfl))))

--| Tokens with the views of a body's events spell the body: its one
--| expression on its keyword's line, or a block of lines deeper than
--| the statement.
theorem bodyOut ∀ (column: Nat) (body: Body) (events: List Event)
    (shaped: ShapedBody body)
    (lexical: LexicalBody body)
    (headed: HeadedBody False body)
    (laid: BodyEvents (Deeper column) body events):
    BodySpells column body events :=
  match body, shaped, lexical, headed, laid with
    | { statements = [{ blankBefore, line = Bare value }] }, Both (Both shapedValue _) _, Both
        (Both valueLexical _) _, Both (Both (Both noAbove headedValue) _) (Both unspaced _), Inl inline =>
      match exprOut column
        (inlineHead (Deeper column) value)
        value
        events
        []
        shapedValue
        valueLexical
        headedValue
        inline with
        | Witness first (Witness others (Both seen (Both spells (Both starts _)))) =>
          Witness first
            (Witness others
              (Both seen (from tokens rest same =>
                viewsCons
                  (later =>
                    Rising (later.map (found => found.offset))
                      → AllApart (InStatement column from) later
                      → After (InStatement column from) later rest
                      → SpelledBody
                        (InStatement column from)
                        { statements = [{ blankBefore, line = Bare value }] }
                        later
                        rest)
                  tokens
                  first
                  others
                  same
                  (firstToken otherTokens firstSame othersSame rising apart after =>
                    Inl
                      (Both
                        (Eq.sym (Eq.cong firstBlankBefore unspaced))
                        (Witness firstToken
                          (Witness otherTokens
                            (Both rfl
                              (Both
                                (inlineAhead
                                  (InStatement column from)
                                  [firstToken, ..otherTokens]
                                  first
                                  others
                                  (consViews firstToken otherTokens first others firstSame othersSame)
                                  (outside => starts.right (noAbove outside)))
                                (Both shapedValue
                                  (Both
                                    (spells from
                                      [firstToken, ..otherTokens]
                                      (consViews firstToken otherTokens first others firstSame othersSame)
                                      rising
                                      (leadsWider
                                        (InStatement column from)
                                        []
                                        (Deeper column).allows
                                        (inlineHead (Deeper column) value)
                                        value.firstAbove
                                        [firstToken, ..otherTokens]
                                        (start held => held.left)
                                        (innerLeads
                                          (Deeper column)
                                          (InStatement column from)
                                          value.firstAbove
                                          [firstToken, ..otherTokens]
                                          rfl
                                          apart)))
                                    (Both after
                                      (headedOfNoAbove (InStatement column from) value (outside =>
                                        noAbove outside))))))))))))))
    | { statements = [] }, _, _, _, Inl never => Void.exfalso (Bool.falseNotTrue never)
    | { statements = [{ blankBefore, line = Let _ _ _ _ _ }] }, _, _, _, Inl never =>
      Void.exfalso (Bool.falseNotTrue never)
    | { statements = [{ blankBefore, line = StatementNote _ }] }, _, _, _, Inl never =>
      Void.exfalso (Bool.falseNotTrue never)
    | { statements = [_, _, .._] }, _, _, _, Inl never => Void.exfalso (Bool.falseNotTrue never)
    | { statements }, Both shapedLines closed, Both lexicalLines _, Both headedLines (Both unspaced _), Inr
        (Witness deeper (Both under lines)) =>
      match linesOut deeper True [] statements events [] shapedLines lexicalLines headedLines
        (closingBody statements closed)
        (isFirst => unspaced)
        rfl
        (laterOfLines deeper statements events unspaced lines) with
        | Witness views (Both seen (Both opens spells)) =>
          match opensSome deeper statements views closed opens with
            | Witness first (Witness others (Both viewsSame starts)) =>
              Witness first
                (Witness others
                  (Both (rewrite <- viewsSame in seen) (from tokens rest same =>
                    viewsCons
                      (later =>
                        Rising (later.map (found => found.offset))
                          → AllApart (InStatement column from) later
                          → After (InStatement column from) later rest
                          → SpelledBody (InStatement column from) { statements } later rest)
                      tokens
                      first
                      others
                      same
                      (firstToken otherTokens firstSame othersSame rising apart after =>
                        match startColumn firstToken deeper
                          (Eq.trans (Eq.cong ((view: TokenView) => view.start) firstSame) starts), settledDeeper column
                            from deeper
                            [firstToken, ..otherTokens]
                            rest
                            under
                            after.right with
                          | Both _ atDeeper, Both settled ends =>
                            Inr
                              (Both
                                (startsDeeper firstToken column deeper under
                                  (Eq.trans (Eq.cong ((view: TokenView) => view.start) firstSame) starts))
                                (rewrite atDeeper in
                                  spells
                                    [firstToken, ..otherTokens]
                                    rest
                                    (rewrite viewsSame in
                                      consViews firstToken otherTokens first others firstSame othersSame)
                                    ends
                                    rising
                                    settled))))))

--| Tokens with the views of a block's lines spell the lines: each
--| statement's first token starts a line at the block's column and
--| holds the comment lines and the blank line above the statement.
theorem linesOut ∀ (column: Nat) (isFirst: Bool) (noted lines: List (Spaced Statement))
    (events: List Event) (pending: List Trivia)
    (shaped: ShapedLines lines)
    (lexical: LexicalLines lines)
    (headed: HeadedLines False lines)
    (closed: LinesClose noted pending lines)
    (unspaced: isFirst = True → Unspaced (noted ++ lines))
    (waits: notesOf StatementNote pending = (noted, False))
    (laid: LaterLines column lines events):
    LinesSpell column isFirst noted lines pending events :=
  match lines, shaped, lexical, headed, closed, unspaced, laid with
    | [], _, _, _, Both notedNone pendingNone, _, laid =>
      Witness []
        (Both
          (rewrite laid, pendingNone in (earlier => rfl))
          (Both rfl (tokens rest same ends =>
            viewsNil (later => LinesGoal column isFirst noted [] rest later) tokens same (rising settled =>
              Both rfl (Both notedNone ends)))))
    | [{ blankBefore, line = StatementNote comment }, ..more], Both _ shapedMore, Both fine lexicalMore, Both _
          headedMore, closed, unspaced, Witness later
        (Both split (Witness front (Witness back (Both thenSplit (Both noteLaid moreLaid))))) =>
      match linesOut column isFirst
        (noted ++ [{ blankBefore, line = StatementNote comment }])
        more
        back
        [OwnLine comment, ..blankOf blankBefore pending]
        shapedMore
        lexicalMore
        headedMore
        (closingNote
          (noted ++ [{ blankBefore, line = StatementNote comment }])
          [OwnLine comment, ..blankOf blankBefore pending]
          blankBefore
          comment
          more
          closed).left
        (first => rewrite List.appendAssoc noted [{ blankBefore, line = StatementNote comment }] more in unspaced first)
        (noteNotes StatementNote blankBefore pending noted comment waits)
        moreLaid with
        | Witness views (Both seen (Both opens spells)) =>
          Witness views
            (Both
              (rewrite split, thenSplit, noteLaid in
                seenBlank blankBefore pending []
                  ([{ word = comment.text, start = Some column }] ++ back)
                  views
                  (seenNote comment column (blankOf blankBefore pending) [] back views fine seen))
              (Both
                (opensNote column
                  { blankBefore, line = StatementNote comment }
                  more
                  views
                  (_ => (closingNote noted pending blankBefore comment more closed).right)
                  opens)
                spells))
    | [{ blankBefore, line = Bare value }, ..more], Both shapedValue shapedMore, Both valueLexical lexicalMore, Both
        (Both noAbove headedValue)
        headedMore, closed, unspaced, Witness later
        (Both split (Witness front (Witness back (Both thenSplit (Both valueLaid moreLaid))))) =>
      match exprOut column
        (atColumn column)
        value
        front
        (blankOf blankBefore pending)
        shapedValue
        valueLexical
        headedValue
        valueLaid, linesOut column False [] more back [] shapedMore lexicalMore headedMore
        (closingCoded { blankBefore, line = Bare value } more closed)
        (never => falseFirst (Unspaced ([] ++ more)) never)
        rfl
        moreLaid with
        | Witness first (Witness others (Both valueSeen (Both valueSpells (Both starts aboveSame)))), Witness moreViews
            (Both moreSeen (Both moreOpens moreSpells)) =>
          Witness
            ([first, ..others] ++ moreViews)
            (Both
              (rewrite split, thenSplit in
                seenBlank blankBefore pending []
                  (front ++ back)
                  ([first, ..others] ++ moreViews)
                  (seenToThen
                    (blankOf blankBefore pending)
                    []
                    []
                    front
                    back
                    [first, ..others]
                    moreViews
                    valueSeen
                    moreSeen))
              (Both (Witness first (Witness (others ++ moreViews) (Both rfl starts))) (tokens rest same ends =>
                viewsSplit
                  (later => LinesGoal column isFirst noted [{ blankBefore, line = Bare value }, ..more] rest later)
                  tokens
                  [first, ..others]
                  moreViews
                  same
                  (statementTokens laterTokens statementSame laterSame =>
                    viewsCons
                      (found =>
                        LinesGoal column isFirst noted
                          [{ blankBefore, line = Bare value }, ..more]
                          rest
                          (found ++ laterTokens))
                      statementTokens
                      first
                      others
                      statementSame
                      (firstToken otherTokens firstSame othersSame rising settled =>
                        let risingStatement := risingFront [firstToken, ..otherTokens] laterTokens rising
                        let spelled :=
                          valueSpells firstToken.offset
                            [firstToken, ..otherTokens]
                            (consViews firstToken otherTokens first others firstSame othersSame)
                            risingStatement
                            (leadsCast
                              (InStatement column firstToken.offset)
                              (blankOf blankBefore pending)
                              (atColumn column)
                              value.firstAbove
                              [firstToken, ..otherTokens]
                              (noAbove rfl)
                              (firstLeads column
                                (blankOf blankBefore pending)
                                (atColumn column)
                                firstToken
                                otherTokens
                                (laterApart column firstToken otherTokens risingStatement)))
                        match spelledStart
                          (InStatement column firstToken.offset)
                          value
                          [firstToken, ..otherTokens]
                          shapedValue
                          spelled with
                          | Witness found (Witness foundOthers (Both foundSplit startKind)) =>
                            Witness firstToken
                              (Witness otherTokens
                                (Witness laterTokens
                                  (Both rfl
                                    (Both
                                      (startsAtLine firstToken column
                                        (Eq.trans (Eq.cong ((view: TokenView) => view.start) firstSame) starts))
                                      (Both
                                        (startNotLet firstToken.value.kind
                                          (rewrite List.consInjectiveHead firstToken found otherTokens foundOthers
                                                  foundSplit in
                                            startKind))
                                        (Both
                                          (notedLine isFirst pending noted more blankBefore
                                            (Bare value)
                                            firstToken.value.above
                                            (Eq.trans
                                              (Eq.cong ((view: TokenView) => view.above) firstSame)
                                              (Eq.trans aboveSame
                                                (Eq.cong
                                                  ((comments: List Comment) =>
                                                    (waiting (blankOf blankBefore pending) comments).reverse)
                                                  (noAbove rfl))))
                                            waits
                                            unspaced)
                                          (Both spelled
                                            (Both
                                              (lineAfter column firstToken otherTokens laterTokens rest
                                                (rewrite laterSame in opensStarts column more moreViews moreOpens)
                                                rising
                                                settled)
                                              (moreSpells laterTokens rest laterSame ends
                                                (risingBack [firstToken, ..otherTokens] laterTokens rising)
                                                (settledBack
                                                  (InStatement column 0)
                                                  [firstToken, ..otherTokens]
                                                  laterTokens
                                                  rest
                                                  settled)))))))))))))))
    | [{ blankBefore, line = Let letComments name nameComments equals body }, ..more], Both shapedBody shapedMore, Both
        (Both fineLet (Both isName (Both fineName (Both fineEquals bodyLexical))))
        lexicalMore, Both (Both letAbove headedBody) headedMore, closed, unspaced, Witness later
        (Both split
          (Witness front
            (Witness back
              (Both thenSplit
                (Both
                  (Witness letEvents
                    (Witness afterLet
                      (Both letSplit
                        (Both letAt
                          (Witness nameEvents
                            (Witness afterName
                              (Both nameSplit
                                (Both nameAt
                                  (Witness equalsEvents
                                    (Witness bodyEvents (Both equalsSplit (Both equalsAt bodyLaid))))))))))))
                  moreLaid))))) =>
      match tokenSeen
        (atColumn column)
        letComments
        "let"
        (Reserved LetKeyword)
        letEvents
        (blankOf blankBefore pending)
        fineLet
        (seen start => keywordEvent seen LetKeyword start)
        letAt, tokenSeen
        (Deeper column).allows
        nameComments
        name
        (Name name)
        nameEvents
        []
        fineName
        (seen start => nameEvent seen name start isName)
        nameAt, tokenSeen
        (Deeper column).allows
        equals
        "="
        (Sign Defines)
        equalsEvents
        []
        fineEquals
        (seen start => signEvent seen Defines start)
        equalsAt, bodyOut column body bodyEvents shapedBody bodyLexical headedBody bodyLaid, linesOut column False []
          more back [] shapedMore lexicalMore headedMore
          (closingCoded { blankBefore, line = Let letComments name nameComments equals body } more closed)
          (never => falseFirst (Unspaced ([] ++ more)) never)
          rfl
          moreLaid with
        | Witness letStart (Both letAllowed letSeen), Witness nameStart (Both nameAllowed nameSeen), Witness equalsStart
            (Both equalsAllowed equalsSeen), Witness bodyFirst
            (Witness bodyOthers (Both bodySeen bodySpells)), Witness moreViews
            (Both moreSeen (Both moreOpens moreSpells)) =>
          Witness
            ([
              tokenView (blankOf blankBefore pending) (Reserved LetKeyword) letStart letComments,
              tokenView [] (Name name) nameStart nameComments,
              tokenView [] (Sign Defines) equalsStart equals,
              bodyFirst,
              ..bodyOthers
            ]
              ++ moreViews)
            (Both
              (rewrite split, thenSplit, letSplit, nameSplit, equalsSplit in
                seenBlank blankBefore pending []
                  ((letEvents ++ (nameEvents ++ (equalsEvents ++ bodyEvents))) ++ back)
                  ([
                    tokenView (blankOf blankBefore pending) (Reserved LetKeyword) letStart letComments,
                    tokenView [] (Name name) nameStart nameComments,
                    tokenView [] (Sign Defines) equalsStart equals,
                    bodyFirst,
                    ..bodyOthers
                  ]
                    ++ moreViews)
                  (seenToThen
                    (blankOf blankBefore pending)
                    []
                    []
                    (letEvents ++ (nameEvents ++ (equalsEvents ++ bodyEvents)))
                    back
                    [
                      tokenView (blankOf blankBefore pending) (Reserved LetKeyword) letStart letComments,
                      tokenView [] (Name name) nameStart nameComments,
                      tokenView [] (Sign Defines) equalsStart equals,
                      bodyFirst,
                      ..bodyOthers
                    ]
                    moreViews
                    (seenThen
                      (blankOf blankBefore pending)
                      letEvents
                      (nameEvents ++ (equalsEvents ++ bodyEvents))
                      [tokenView (blankOf blankBefore pending) (Reserved LetKeyword) letStart letComments]
                      [
                        tokenView [] (Name name) nameStart nameComments,
                        tokenView [] (Sign Defines) equalsStart equals,
                        bodyFirst,
                        ..bodyOthers
                      ]
                      letSeen
                      (seenThen [] nameEvents
                        (equalsEvents ++ bodyEvents)
                        [tokenView [] (Name name) nameStart nameComments]
                        [tokenView [] (Sign Defines) equalsStart equals, bodyFirst, ..bodyOthers]
                        nameSeen
                        (seenThen [] equalsEvents bodyEvents
                          [tokenView [] (Sign Defines) equalsStart equals]
                          [bodyFirst, ..bodyOthers]
                          equalsSeen
                          bodySeen)))
                    moreSeen))
              (Both
                (Witness
                  (tokenView (blankOf blankBefore pending) (Reserved LetKeyword) letStart letComments)
                  (Witness
                    ([
                      tokenView [] (Name name) nameStart nameComments,
                      tokenView [] (Sign Defines) equalsStart equals,
                      bodyFirst,
                      ..bodyOthers
                    ]
                      ++ moreViews)
                    (Both rfl letAllowed)))
                (tokens rest same ends =>
                  viewsCons
                    (found =>
                      LinesGoal column isFirst noted
                        [{ blankBefore, line = Let letComments name nameComments equals body }, ..more]
                        rest
                        found)
                    tokens
                    (tokenView (blankOf blankBefore pending) (Reserved LetKeyword) letStart letComments)
                    ([
                      tokenView [] (Name name) nameStart nameComments,
                      tokenView [] (Sign Defines) equalsStart equals,
                      bodyFirst,
                      ..bodyOthers
                    ]
                      ++ moreViews)
                    same
                    (firstToken afterFirst firstSame afterFirstSame =>
                      viewsCons
                        (found =>
                          LinesGoal column isFirst noted
                            [{ blankBefore, line = Let letComments name nameComments equals body }, ..more]
                            rest
                            [firstToken, ..found])
                        afterFirst
                        (tokenView [] (Name name) nameStart nameComments)
                        ([tokenView [] (Sign Defines) equalsStart equals, bodyFirst, ..bodyOthers] ++ moreViews)
                        afterFirstSame
                        (named afterNamed namedSame afterNamedSame =>
                          viewsCons
                            (found =>
                              LinesGoal column isFirst noted
                                [{ blankBefore, line = Let letComments name nameComments equals body }, ..more]
                                rest
                                [firstToken, named, ..found])
                            afterNamed
                            (tokenView [] (Sign Defines) equalsStart equals)
                            ([bodyFirst, ..bodyOthers] ++ moreViews)
                            afterNamedSame
                            (equalsToken afterEquals equalsSame afterEqualsSame =>
                              viewsSplit
                                (found =>
                                  LinesGoal column isFirst noted
                                    [{ blankBefore, line = Let letComments name nameComments equals body }, ..more]
                                    rest
                                    [firstToken, named, equalsToken, ..found])
                                afterEquals
                                [bodyFirst, ..bodyOthers]
                                moreViews
                                afterEqualsSame
                                (bodyTokens laterTokens bodySame laterSame rising settled =>
                                  let risingStatement :=
                                    risingFront [firstToken, named, equalsToken, ..bodyTokens] laterTokens rising
                                  let apart :=
                                    laterApart column firstToken [named, equalsToken, ..bodyTokens] risingStatement
                                  let after :=
                                    lineAfter column firstToken
                                      [named, equalsToken, ..bodyTokens]
                                      laterTokens
                                      rest
                                      (rewrite laterSame in opensStarts column more moreViews moreOpens)
                                      rising
                                      settled
                                  match innerFits
                                    (Deeper column)
                                    (InStatement column firstToken.offset)
                                    named
                                    (Name name)
                                    nameStart
                                    nameComments
                                    rfl
                                    apart.left
                                    nameAllowed
                                    namedSame, innerFits
                                    (Deeper column)
                                    (InStatement column firstToken.offset)
                                    equalsToken
                                    (Sign Defines)
                                    equalsStart
                                    equals
                                    rfl
                                    apart.right.left
                                    equalsAllowed
                                    equalsSame with
                                    | Both nameKind (Both nameAllows nameNotes), Both equalsKind
                                        (Both equalsAllows equalsNotes) =>
                                      Witness firstToken
                                        (Witness named
                                          (Witness equalsToken
                                            (Witness bodyTokens
                                              (Witness laterTokens
                                                (Both rfl
                                                  (Both
                                                    (startsAtLine firstToken column
                                                      (Eq.trans
                                                        (Eq.cong ((view: TokenView) => view.start) firstSame)
                                                        letAllowed))
                                                    (Both
                                                      (Eq.cong ((view: TokenView) => view.kind) firstSame)
                                                      (Both nameKind
                                                        (Both nameAllows
                                                          (Both equalsKind
                                                            (Both equalsAllows
                                                              (Both
                                                                (keywordComments column firstToken
                                                                  (blankOf blankBefore pending)
                                                                  (Reserved LetKeyword)
                                                                  letStart
                                                                  letComments
                                                                  letAbove
                                                                  firstSame)
                                                                (Both nameNotes
                                                                  (Both equalsNotes
                                                                    (Both
                                                                      (notedLine isFirst pending noted more blankBefore
                                                                        (Let letComments name nameComments equals body)
                                                                        firstToken.value.above
                                                                        (Eq.trans
                                                                          (Eq.cong
                                                                            ((view: TokenView) => view.above)
                                                                            firstSame)
                                                                          (Eq.cong
                                                                            ((comments: List Comment) =>
                                                                              (waiting
                                                                                (blankOf blankBefore pending)
                                                                                comments).reverse)
                                                                            letAbove))
                                                                        waits
                                                                        unspaced)
                                                                      (Both
                                                                        (bodySpells firstToken.offset bodyTokens
                                                                          (laterTokens ++ rest)
                                                                          bodySame
                                                                          (risingBack
                                                                            [firstToken, named, equalsToken]
                                                                            bodyTokens
                                                                            risingStatement)
                                                                          apart.right.right
                                                                          (afterBack
                                                                            (InStatement column firstToken.offset)
                                                                            [firstToken, named, equalsToken]
                                                                            bodyTokens
                                                                            (laterTokens ++ rest)
                                                                            after))
                                                                        (moreSpells laterTokens rest laterSame ends
                                                                          (risingBack
                                                                            [
                                                                              firstToken,
                                                                              named,
                                                                              equalsToken,
                                                                              ..bodyTokens
                                                                            ]
                                                                            laterTokens
                                                                            rising)
                                                                          (settledBack
                                                                            (InStatement column 0)
                                                                            [
                                                                              firstToken,
                                                                              named,
                                                                              equalsToken,
                                                                              ..bodyTokens
                                                                            ]
                                                                            laterTokens
                                                                            rest
                                                                            settled)))))))))))))))))))))))))
