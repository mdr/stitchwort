--| `wordsEdge1`, and when the marks of the tree's comments give it (SW-4107).
--|
--| `wordsEdgeOfMarks`: in an expression of the slice, if no comment falls between two tokens that are no closers,
--| none before the first unless `lead`, and none after the last unless `end`, then its comments on tokens that are no
--| closers lie at the edges `wordEdge1` allows. The marks are `Fmt.NoteMarks`', of the expression's spelling with the
--| closers and commas left out.

namespace Fmt.WordsEdge
import Std (Bool, DecEq, Eq, List, Option, Text)
import Syntax (Comments, Decl, DefBody, Expr, InfixKind, Note, Tok, Word)
import Fmt (..)
import Fmt.SpellProofs (..)
import Fmt.TreeJoinProofs (
  OperatorSpells,
  PrefixSpells,
  Quiet,
  lexKind,
  lexKindOfSpells,
  operatorSpellsOf,
  spellsNotComment,
  infixListed,
  spellsOfText1,
  wordQuiet
)
import Fmt.NoteMarks (..)
import Fmt.CalmProofs (calmAllEmpty, calmItemsEmpty, keptNoted, keptTrails)

-- The part.

--| A token's comments as `edge1` allows them: own-line comments only if it leads, a trailing one only if it ends.
def Word.wordEdge1 (word: Word) (lead end: Bool): Bool := (lead || !word.noted) && (end || !word.trails)

--| `edgeQuiet1`'s tests of comments on the tokens that are no closers: closers and blank-line flags are not looked
--| at.
def Expr.wordsEdge1 (expr: Expr) (lead end: Bool): Bool := match expr with
  | Atom _ word => word.wordEdge1 lead end
  | Paren open inner _ => open.wordEdge1 lead False && inner.wordsEdge1 False end
  | Tuple open items _ _ => open.wordEdge1 lead False && lastWordsEdge1 end items
  | ListOf open items _ _ => open.wordEdge1 lead (end && items.isEmpty) && lastWordsEdge1 end items
  | App head arguments => !arguments.isEmpty && head.wordsEdge1 lead False && lastWordsEdge1 end arguments
  | Infix _ left operator right =>
    left.wordsEdge1 lead False && operator.wordEdge1 False False && right.wordsEdge1 False end
  | Prefix operator operand => operator.wordEdge1 lead False && operand.wordsEdge1 False end
  | _ => False

--| Items or arguments, the last of which may end with a comment (`end`).
def lastWordsEdge1 (end: Bool) (items: List Expr): Bool := match items with
  | [] => True
  | [last] => last.wordsEdge1 False end
  | [expr, ..rest] => expr.wordsEdge1 False False && lastWordsEdge1 end rest

--| The calmed type's and value's comments on tokens that are no closers lie at their edges, as in `edgeQuiet1`.
def Decl.wordsEdge1: Decl → Bool
  | Definition [] header (Assigned _ value) =>
    (header.result.calm False).wordsEdge1 False True && (value.calm False).wordsEdge1 True True
  | _ => False

-- The marks at an expression's edges.

--| The texts' tokens and comments as an expression of the part needs them: no comment before the first token unless
--| `lead`, none between two tokens, and none after the last unless `end`.
def EdgeMarks (pending: Bool) (texts: List Text) (lead end: Bool): Prop :=
  (lead = False → firstQuiet (marks pending texts) = True)
    ∧ tailQuiet (marks pending texts) = True
    ∧ (end = False → pendingAfter pending texts = False)

--| Two runs of tokens, one after the other: the first ends with no comment, and the second starts with none.
theorem edgeSplit ∀ (pending: Bool) (front back: List Text) (lead end: Bool)
    (frontHas: hasToken front = True)
    (backHas: hasToken back = True)
    (edges: EdgeMarks pending (front ++ back) lead end):
    EdgeMarks pending front lead False ∧ EdgeMarks (pendingAfter pending front) back False end :=
  let (first, inner, last) := edges
  let whole: marks pending (front ++ back) = marks pending front ++ marks (pendingAfter pending front) back :=
    marksAppend pending front back
  let (frontInner, backAll) :=
    tailAppend pending front (marks (pendingAfter pending front) back) frontHas (rewrite whole at inner then inner)
  let (backFirst, backInner) := quietAll (marks (pendingAfter pending front) back) backAll
  (
    (
      noLead =>
        rewrite <- firstAppend pending front (marks (pendingAfter pending front) back) frontHas, <- whole then
          first noLead,
      frontInner,
      _ => firstClears (pendingAfter pending front) back backHas backFirst
    ),
    (_ => backFirst, backInner, noEnd => rewrite <- pendingAppend pending front back then last noEnd)
  )

--| Comments after the tokens (a closer's) don't make a comment before them.
theorem edgeNotes ∀ (pending: Bool) (texts notes: List Text) (lead end: Bool)
    (allNoted: allNotes notes = True)
    (edges: EdgeMarks pending (texts ++ notes) lead end):
    EdgeMarks pending texts lead end :=
  let (first, inner, last) := edges
  let whole: marks pending (texts ++ notes) = marks pending texts :=
    rewrite marksAppend pending texts notes, marksNotes (pendingAfter pending texts) notes allNoted, List.appendNil
  (
    noLead => rewrite <- whole then first noLead,
    rewrite <- whole then inner,
    noEnd =>
      let after: (pendingAfter pending texts || !notes.isEmpty) = False :=
        rewrite <- pendingNotes (pendingAfter pending texts) notes allNoted, <- pendingAppend pending texts notes then
          last noEnd
      Bool.orFalseLeft _ _ after
  )

-- A token's spelling.

theorem notesAllNotes ∀ (notes: List Note)
    (sound: notesSound notes = True):
    allNotes (notes.map (note => note.text)) = True :=
  match notes with
    | [] => byComputing
    | [note, ..rest] =>
      let (comment, others) := sound
      let starts: note.text.startsWith "--" = True := Bool.andLeft comment
      rewrite starts then notesAllNotes rest others

theorem afterAllNotes ∀ (after: Option Text) (sound: afterSound after = True): allNotes after.toList = True :=
  match after with
    | None => byComputing
    | Some comment =>
      let starts: comment.startsWith "--" = True := Bool.andLeft sound
      rewrite starts

theorem wordNotes ∀ (word: Word) (sound: word.sound = True): allNotes word.notes = True :=
  notesAllNotes word.comments.above (Bool.andLeft (Bool.andRight sound))

theorem wordAfter ∀ (word: Word) (sound: word.sound = True): allNotes word.comments.after.toList = True :=
  afterAllNotes word.comments.after (Bool.andRight (Bool.andRight sound))

--| A token that is no closer keeps its comments and its text once the closers are left out.
theorem spelledFilter ∀ (word: Word)
    (plain: notCloser word.text = True)
    (sound: word.sound = True):
    (word.spelledAt False).filter notCloser = word.notes ++ ([word.text] ++ word.comments.after.toList) :=
  rewrite List.filterAppend word.notes ([word.text] ++ word.comments.after.toList) notCloser,
      List.filterAppend [word.text] word.comments.after.toList notCloser,
      filterNotes word.notes (wordNotes word sound),
      filterNotes word.comments.after.toList (wordAfter word sound),
      plain

--| A closer leaves only its comments.
theorem closerFilter ∀ (word: Word)
    (closer: notCloser word.text = False)
    (sound: word.sound = True):
    (word.spelledAt False).filter notCloser = word.notes ++ word.comments.after.toList :=
  rewrite List.filterAppend word.notes ([word.text] ++ word.comments.after.toList) notCloser,
      List.filterAppend [word.text] word.comments.after.toList notCloser,
      filterNotes word.notes (wordNotes word sound),
      filterNotes word.comments.after.toList (wordAfter word sound),
      closer

theorem closerNotes ∀ (word: Word)
    (closer: notCloser word.text = False)
    (sound: word.sound = True):
    allNotes ((word.spelledAt False).filter notCloser) = True :=
  rewrite closerFilter word closer sound then
    notesAppend word.notes word.comments.after.toList (wordNotes word sound) (wordAfter word sound)

theorem wordHas ∀ (word: Word)
    (plain: notCloser word.text = True)
    (token: notComment word.text = True)
    (sound: word.sound = True):
    hasToken ((word.spelledAt False).filter notCloser) = True :=
  rewrite spelledFilter word plain sound then
    hasAppendRight word.notes ([word.text] ++ word.comments.after.toList) (rewrite token)

theorem notesEmpty ∀ (notes: List Note): (notes.map (note => note.text)).isEmpty = notes.isEmpty := match notes with
  | [] => byComputing
  | [note, ..rest] => byComputing

--| A token's comments where the marks allow them are where `wordEdge1` allows them.
--|
--| Proof idea: once the closers are left out the token is its own-line comments, its text and its trailing comment,
--| so its one mark says whether it has own-line comments (or a comment was waiting), and the comment after it is
--| the trailing one.
theorem wordEdgeOfMarks ∀ (word: Word) (lead end pending: Bool)
    (plain: notCloser word.text = True)
    (token: notComment word.text = True)
    (sound: word.sound = True)
    (edges: EdgeMarks pending ((word.spelledAt False).filter notCloser) lead end):
    word.wordEdge1 lead end = True :=
  let (first, _, last) := edges
  let notes := wordNotes word sound
  let after := wordAfter word sound
  let filtered := spelledFilter word plain sound
  let marked: marks pending ((word.spelledAt False).filter notCloser) = [pendingAfter pending word.notes] :=
    rewrite filtered,
        marksAppend pending word.notes ([word.text] ++ word.comments.after.toList),
        marksNotes pending word.notes notes,
        token,
        marksNotes False word.comments.after.toList after
  let ended: pendingAfter pending ((word.spelledAt False).filter notCloser) = !word.comments.after.toList.isEmpty :=
    rewrite filtered, pendingAppend pending word.notes ([word.text] ++ word.comments.after.toList), token then
      pendingNotes False word.comments.after.toList after
  let waiting: pendingAfter pending word.notes = (pending || !word.notes.isEmpty) :=
    pendingNotes pending word.notes notes
  let noted: (!word.notes.isEmpty) = word.noted := rewrite notesEmpty word.comments.above
  let trails: (!word.comments.after.toList.isEmpty) = word.trails := match word.comments.after with
    | None => byComputing
    | Some comment => byComputing
  match lead, end with
    | True, True => byComputing
    | True, False =>
      let bare: word.trails = False := rewrite <- trails, <- ended then last byComputing
      rewrite bare
    | False, True =>
      let quiet: (pending || word.noted) = False :=
        let firstMark := first byComputing
        Bool.notTrue _ (rewrite marked, waiting, noted at firstMark then firstMark)
      rewrite Bool.orFalseRight _ _ quiet
    | False, False =>
      let quiet: (pending || word.noted) = False :=
        let firstMark := first byComputing
        Bool.notTrue _ (rewrite marked, waiting, noted at firstMark then firstMark)
      let bare: word.trails = False := rewrite <- trails, <- ended then last byComputing
      rewrite Bool.orFalseRight _ _ quiet, bare

-- Tokens that are no closers.

--| A text a token of a kind that is no comma or closer is spelled with is a token that is no closer.
theorem kindPlain ∀ (kind: Tok) (text: Text)
    (spells: Syntax.Proofs.Spells kind text)
    (quiet: Quiet kind):
    notCloser text = True ∧ notComment text = True :=
  let kinded: lexKind text = kind := lexKindOfSpells kind text spells
  let (notComma, notParen, notBracket, notBrace) := quiet
  let token: notComment text = True := rewrite spellsNotComment kind text spells
  match a: text == ")" with
    | True => (notParen (rewrite DecEq.sound a at kinded then kinded)).impossible
    | False =>
      match b: text == "]" with
        | True => (notBracket (rewrite DecEq.sound b at kinded then kinded)).impossible
        | False =>
          match c: text == "}" with
            | True => (notBrace (rewrite DecEq.sound c at kinded then kinded)).impossible
            | False =>
              match d: text == "," with
                | True => (notComma (rewrite DecEq.sound d at kinded then kinded)).impossible
                | False => (byComputing, token)

theorem atomPlain ∀ (kind: Tok) (word: Word)
    (within: (Atom kind word).within1 = True):
    notCloser word.text = True ∧ notComment word.text = True :=
  kindPlain kind word.text (spellsOfText1 kind word.text (Bool.andRight within)) (wordQuiet kind (Bool.andLeft within))

theorem operatorPlain ∀ (text: Text)
    (listed: operatorText1 text = True):
    notCloser text = True ∧ notComment text = True :=
  let (kind, spells, quiet) := operatorSpellsOf text listed
  kindPlain kind text spells quiet

theorem prefixPlain ∀ (text: Text) (listed: prefixText1 text = True): notCloser text = True ∧ notComment text = True :=
  match a: text == "-" with
    | True => rewrite DecEq.sound a then (byComputing, byComputing)
    | False =>
      match b: text == "!" with
        | True => rewrite DecEq.sound b then (byComputing, byComputing)
        | False =>
          match c: text == "¬" with
            | True => rewrite DecEq.sound c then (byComputing, byComputing)

theorem textPlain ∀ (word: Word) (fixed: Text)
    (same: (word.text == fixed) = True)
    (plain: notCloser fixed = True ∧ notComment fixed = True):
    notCloser word.text = True ∧ notComment word.text = True :=
  rewrite DecEq.sound same then plain

theorem textCloser ∀ (word: Word) (fixed: Text)
    (same: (word.text == fixed) = True)
    (closer: notCloser fixed = False):
    notCloser word.text = False :=
  rewrite DecEq.sound same then closer

-- Every expression has a token.

theorem exprHas ∀ (expr: Expr)
    (within: expr.within1 = True)
    (lexical: expr.lexical1 = True)
    (sound: expr.sound = True):
    hasToken ((expr.spelt False).filter notCloser) = True :=
  match expr with
    | Atom kind word =>
      let (plain, token) := atomPlain kind word within
      wordHas word plain token sound
    | Paren open inner close =>
      let (plain, token) := textPlain open "(" (Bool.andLeft lexical) (byComputing, byComputing)
      rewrite List.filterAppend (open.spelledAt False) (inner.spelt False ++ close.spelledAt False) notCloser then
        hasAppendLeft _ _ (wordHas open plain token (Bool.andLeft sound))
    | Tuple open items comma close =>
      let (plain, token) := textPlain open "(" (Bool.andLeft lexical) (byComputing, byComputing)
      rewrite List.filterAppend (open.spelledAt False) (commaSpelt items ++ close.spelledAt False) notCloser then
        hasAppendLeft _ _ (wordHas open plain token (Bool.andLeft sound))
    | ListOf open items comma close =>
      let (plain, token) := textPlain open "[" (Bool.andLeft lexical) (byComputing, byComputing)
      rewrite List.filterAppend (open.spelledAt False) (commaSpelt items ++ close.spelledAt False) notCloser then
        hasAppendLeft _ _ (wordHas open plain token (Bool.andLeft sound))
    | App head arguments =>
      rewrite List.filterAppend (head.spelt False) (argumentsSpelt arguments) notCloser then
        hasAppendLeft _ _ (exprHas head (Bool.andLeft within) (Bool.andLeft lexical) (Bool.andLeft sound))
    | Infix kind left operator right =>
      rewrite List.filterAppend (left.spelt False) (operator.spelledAt False ++ right.spelt False) notCloser then
        hasAppendLeft _ _
          (exprHas left (infixLeftWithin kind left operator right within) (Bool.andLeft lexical) (Bool.andLeft sound))
    | Prefix operator operand =>
      let (plain, token) := prefixPlain operator.text (Bool.andRight within)
      rewrite List.filterAppend (operator.spelledAt False) (operand.spelt False) notCloser then
        hasAppendLeft _ _ (wordHas operator plain token (Bool.andLeft sound))

theorem infixLeftWithin ∀ (kind: InfixKind) (left: Expr) (operator: Word) (right: Expr)
    (within: (Infix kind left operator right).within1 = True):
    left.within1 = True :=
  match kind with
    | InfixBinary => Bool.andLeft within
    | InfixArrow => Bool.andLeft within

theorem commaHas ∀ (items: List Expr)
    (filled: items.isEmpty = False)
    (within: allWithin1 items = True)
    (lexical: allLexical1 items = True)
    (sound: allSound items = True):
    hasToken ((commaSpelt items).filter notCloser) = True :=
  match items with
    | [item] => exprHas item (Bool.andLeft within) (Bool.andLeft lexical) (Bool.andLeft sound)
    | [item, next, ..more] =>
      rewrite List.filterAppend (item.spelt False) ([","] ++ commaSpelt [next, ..more]) notCloser then
        hasAppendLeft _ _ (exprHas item (Bool.andLeft within) (Bool.andLeft lexical) (Bool.andLeft sound))

theorem argumentsHas ∀ (arguments: List Expr)
    (filled: arguments.isEmpty = False)
    (within: allWithin1 arguments = True)
    (lexical: allLexical1 arguments = True)
    (sound: allSound arguments = True):
    hasToken ((argumentsSpelt arguments).filter notCloser) = True :=
  match arguments with
    | [argument, ..rest] =>
      rewrite List.filterAppend (argument.spelt False) (argumentsSpelt rest) notCloser then
        hasAppendLeft _ _ (exprHas argument (Bool.andLeft within) (Bool.andLeft lexical) (Bool.andLeft sound))

-- The part from the marks.

--| An expression of the slice whose tokens that are no closers have comments only where the marks allow them has
--| comments only where `wordsEdge1` allows them.
--|
--| Proof idea: induction on the expression. Each node's spelling, closers left out, is its parts' in order, and
--| `edgeSplit` hands each part the marks at its own edges: a part followed by another has no comment after it, and one
--| after another none before it; a closer's comments come after its part (`edgeNotes`).
theorem wordsEdgeOfMarks ∀ (expr: Expr) (lead end pending: Bool)
    (within: expr.within1 = True)
    (shaped: expr.shaped1 = True)
    (lexical: expr.lexical1 = True)
    (sound: expr.sound = True)
    (edges: EdgeMarks pending ((expr.spelt False).filter notCloser) lead end):
    expr.wordsEdge1 lead end = True :=
  match expr with
    | Atom kind word =>
      let (plain, token) := atomPlain kind word within
      wordEdgeOfMarks word lead end pending plain token sound edges
    | Paren open inner close =>
      let (openText, closeText, innerLexical) := lexical
      let (openSound, innerSound, closeSound) := sound
      let (plain, token) := textPlain open "(" openText (byComputing, byComputing)
      bracketEdge open
        (inner.spelt False)
        close
        lead
        end
        pending _
        plain
        token
        openSound
        (textCloser close ")" closeText byComputing)
        closeSound
        (exprHas inner within innerLexical innerSound)
        edges
        (innerEdges =>
          wordsEdgeOfMarks inner False end
            (pendingAfter pending ((open.spelledAt False).filter notCloser))
            within
            shaped
            innerLexical
            innerSound
            innerEdges)
    | Tuple open items comma close =>
      let (openText, closeText, itemsLexical) := lexical
      let (openSound, itemsSound, closeSound) := sound
      let (plain, token) := textPlain open "(" openText (byComputing, byComputing)
      let filled: items.isEmpty = False := match items, shaped with
        | [_, .._], _ => byComputing
      bracketEdge open
        (commaSpelt items)
        close
        lead
        end
        pending _
        plain
        token
        openSound
        (textCloser close ")" closeText byComputing)
        closeSound
        (commaHas items filled within itemsLexical itemsSound)
        edges
        (itemsEdges =>
          itemsEdgeOfMarks items end
            (pendingAfter pending ((open.spelledAt False).filter notCloser))
            within
            (Bool.andRight shaped)
            itemsLexical
            itemsSound
            itemsEdges)
    | ListOf open items comma close =>
      let (openText, closeText, itemsLexical) := lexical
      let (openSound, itemsSound, closeSound) := sound
      let (plain, token) := textPlain open "[" openText (byComputing, byComputing)
      let closer := textCloser close "]" closeText byComputing
      match items with
        | [] =>
          let spelt: ((open.spelledAt False ++ commaSpelt [] ++ close.spelledAt False).filter notCloser)
            = (open.spelledAt False).filter notCloser ++ (close.spelledAt False).filter notCloser :=
            rewrite List.filterAppend (open.spelledAt False) (commaSpelt [] ++ close.spelledAt False) notCloser
          let openEdges :=
            edgeNotes pending
              ((open.spelledAt False).filter notCloser)
              ((close.spelledAt False).filter notCloser)
              lead
              end
              (closerNotes close closer closeSound)
              (rewrite spelt at edges then edges)
          match end with
            | True => Bool.andIntro (wordEdgeOfMarks open lead True pending plain token openSound openEdges) byComputing
            | False =>
              Bool.andIntro (wordEdgeOfMarks open lead False pending plain token openSound openEdges) byComputing
        | [item, ..rest] =>
          let opened :=
            bracketEdge open
              (commaSpelt [item, ..rest])
              close
              lead
              end
              pending _
              plain
              token
              openSound
              closer
              closeSound
              (commaHas [item, ..rest] byComputing within itemsLexical itemsSound)
              edges
              (itemsEdges =>
                itemsEdgeOfMarks
                  [item, ..rest]
                  end
                  (pendingAfter pending ((open.spelledAt False).filter notCloser))
                  within
                  shaped
                  itemsLexical
                  itemsSound
                  itemsEdges)
          match end with
            | True => opened
            | False => opened
    | App head arguments =>
      let (headWithin, argumentsWithin) := within
      let (_, headShaped, filled, _, argumentsShaped) := shaped
      let (headLexical, argumentsLexical) := lexical
      let (headSound, argumentsSound) := sound
      let filledFalse: arguments.isEmpty = False := Bool.notTrue _ filled
      let split: ((head.spelt False ++ argumentsSpelt arguments).filter notCloser)
        = (head.spelt False).filter notCloser ++ (argumentsSpelt arguments).filter notCloser :=
        List.filterAppend (head.spelt False) (argumentsSpelt arguments) notCloser
      let (headEdges, argumentsEdges) :=
        edgeSplit pending
          ((head.spelt False).filter notCloser)
          ((argumentsSpelt arguments).filter notCloser)
          lead
          end
          (exprHas head headWithin headLexical headSound)
          (argumentsHas arguments filledFalse argumentsWithin argumentsLexical argumentsSound)
          (rewrite split at edges then edges)
      Bool.andIntro filled
        (Bool.andIntro
          (wordsEdgeOfMarks head lead False pending headWithin headShaped headLexical headSound headEdges)
          (argumentsEdgeOfMarks arguments end
            (pendingAfter pending ((head.spelt False).filter notCloser))
            filledFalse
            argumentsWithin
            argumentsShaped
            argumentsLexical
            argumentsSound
            argumentsEdges))
    | Infix kind left operator right =>
      match kind with
        | InfixBinary =>
          let (leftWithin, rightWithin, _) := within
          infixEdge left operator right lead end pending _ _ _ leftWithin rightWithin
            (infixListed InfixBinary left operator right within)
            shaped
            lexical
            sound
            edges
            (leftEdges =>
              wordsEdgeOfMarks left lead False pending leftWithin
                (Bool.andLeft shaped)
                (Bool.andLeft lexical)
                (Bool.andLeft sound)
                leftEdges)
            (middle rightEdges =>
              wordsEdgeOfMarks right False end middle rightWithin
                (Bool.andLeft (Bool.andRight shaped))
                (Bool.andRight (Bool.andRight lexical))
                (Bool.andRight (Bool.andRight sound))
                rightEdges)
        | InfixArrow =>
          let (leftWithin, rightWithin, _) := within
          infixEdge left operator right lead end pending _ _ _ leftWithin rightWithin
            (infixListed InfixArrow left operator right within)
            shaped
            lexical
            sound
            edges
            (leftEdges =>
              wordsEdgeOfMarks left lead False pending leftWithin
                (Bool.andLeft shaped)
                (Bool.andLeft lexical)
                (Bool.andLeft sound)
                leftEdges)
            (middle rightEdges =>
              wordsEdgeOfMarks right False end middle rightWithin
                (Bool.andLeft (Bool.andRight shaped))
                (Bool.andRight (Bool.andRight lexical))
                (Bool.andRight (Bool.andRight sound))
                rightEdges)
        | _ => cases
    | Prefix operator operand =>
      let (operandWithin, listed) := within
      let (plain, token) := prefixPlain operator.text listed
      let (operatorSound, operandSound) := sound
      let split: ((operator.spelledAt False ++ operand.spelt False).filter notCloser)
        = (operator.spelledAt False).filter notCloser ++ (operand.spelt False).filter notCloser :=
        List.filterAppend (operator.spelledAt False) (operand.spelt False) notCloser
      let (operatorEdges, operandEdges) :=
        edgeSplit pending
          ((operator.spelledAt False).filter notCloser)
          ((operand.spelt False).filter notCloser)
          lead
          end
          (wordHas operator plain token operatorSound)
          (exprHas operand operandWithin (Bool.andRight lexical) operandSound)
          (rewrite split at edges then edges)
      Bool.andIntro
        (wordEdgeOfMarks operator lead False pending plain token operatorSound operatorEdges)
        (wordsEdgeOfMarks operand False end
          (pendingAfter pending ((operator.spelledAt False).filter notCloser))
          operandWithin
          (Bool.andLeft shaped)
          (Bool.andRight lexical)
          operandSound
          operandEdges)

--| A bracket with something inside: its opener's comments and its inside's, from the marks.
theorem bracketEdge ∀ (open: Word) (inside: List Text) (close: Word) (lead end pending goal: Bool)
    (plain: notCloser open.text = True)
    (token: notComment open.text = True)
    (openSound: open.sound = True)
    (closer: notCloser close.text = False)
    (closeSound: close.sound = True)
    (insideHas: hasToken (inside.filter notCloser) = True)
    (edges: EdgeMarks pending ((open.spelledAt False ++ inside ++ close.spelledAt False).filter notCloser) lead end)
    (insideOf: EdgeMarks
      (pendingAfter pending ((open.spelledAt False).filter notCloser))
      (inside.filter notCloser)
      False
      end
      → goal = True):
    (open.wordEdge1 lead False && goal) = True :=
  let split: ((open.spelledAt False ++ inside ++ close.spelledAt False).filter notCloser)
    = (open.spelledAt False).filter notCloser
      ++ (inside.filter notCloser ++ (close.spelledAt False).filter notCloser) :=
    rewrite List.filterAppend (open.spelledAt False) (inside ++ close.spelledAt False) notCloser,
        List.filterAppend inside (close.spelledAt False) notCloser
  let (openEdges, restEdges) :=
    edgeSplit pending
      ((open.spelledAt False).filter notCloser)
      (inside.filter notCloser ++ (close.spelledAt False).filter notCloser)
      lead
      end
      (wordHas open plain token openSound)
      (hasAppendLeft _ _ insideHas)
      (rewrite split at edges then edges)
  Bool.andIntro
    (wordEdgeOfMarks open lead False pending plain token openSound openEdges)
    (insideOf
      (edgeNotes
        (pendingAfter pending ((open.spelledAt False).filter notCloser))
        (inside.filter notCloser)
        ((close.spelledAt False).filter notCloser)
        False
        end
        (closerNotes close closer closeSound)
        restEdges))

--| An infix operator's operands and the operator between them, from the marks.
theorem infixEdge ∀ (left: Expr) (operator: Word) (right: Expr) (lead end pending extra leftGoal rightGoal: Bool)
    (leftWithin: left.within1 = True)
    (rightWithin: right.within1 = True)
    (listed: operatorText1 operator.text = True)
    (shaped: (left.shaped1 && right.shaped1 && extra) = True)
    (lexical: (left.lexical1 && (operatorTok operator.text).isSome && right.lexical1) = True)
    (sound: (left.sound && operator.sound && right.sound) = True)
    (edges: EdgeMarks pending
      ((left.spelt False ++ operator.spelledAt False ++ right.spelt False).filter notCloser)
      lead
      end)
    (leftOf: EdgeMarks pending ((left.spelt False).filter notCloser) lead False → leftGoal = True)
    (rightOf: ∀ (middle: Bool) => EdgeMarks middle ((right.spelt False).filter notCloser) False end → rightGoal = True):
    (leftGoal && operator.wordEdge1 False False && rightGoal) = True :=
  let (plain, token) := operatorPlain operator.text listed
  let (leftSound, operatorSound, rightSound) := sound
  let split: ((left.spelt False ++ operator.spelledAt False ++ right.spelt False).filter notCloser)
    = (left.spelt False).filter notCloser
      ++ ((operator.spelledAt False).filter notCloser ++ (right.spelt False).filter notCloser) :=
    rewrite List.filterAppend (left.spelt False) (operator.spelledAt False ++ right.spelt False) notCloser,
        List.filterAppend (operator.spelledAt False) (right.spelt False) notCloser
  let rightHas := exprHas right rightWithin (Bool.andRight (Bool.andRight lexical)) rightSound
  let (leftEdges, restEdges) :=
    edgeSplit pending
      ((left.spelt False).filter notCloser)
      ((operator.spelledAt False).filter notCloser ++ (right.spelt False).filter notCloser)
      lead
      end
      (exprHas left leftWithin (Bool.andLeft lexical) leftSound)
      (hasAppendLeft _ _ (wordHas operator plain token operatorSound))
      (rewrite split at edges then edges)
  let middle := pendingAfter pending ((left.spelt False).filter notCloser)
  let (operatorEdges, rightEdges) :=
    edgeSplit middle
      ((operator.spelledAt False).filter notCloser)
      ((right.spelt False).filter notCloser)
      False
      end
      (wordHas operator plain token operatorSound)
      rightHas
      restEdges
  Bool.andIntro
    (leftOf leftEdges)
    (Bool.andIntro
      (wordEdgeOfMarks operator False False middle plain token operatorSound operatorEdges)
      (rightOf (pendingAfter middle ((operator.spelledAt False).filter notCloser)) rightEdges))

--| A bracket's items, from the marks.
theorem itemsEdgeOfMarks ∀ (items: List Expr) (end pending: Bool)
    (within: allWithin1 items = True)
    (shaped: allShaped1 items = True)
    (lexical: allLexical1 items = True)
    (sound: allSound items = True)
    (edges: EdgeMarks pending ((commaSpelt items).filter notCloser) False end):
    lastWordsEdge1 end items = True :=
  match items with
    | [] => byComputing
    | [last] =>
      wordsEdgeOfMarks last False end pending
        (Bool.andLeft within)
        (Bool.andLeft shaped)
        (Bool.andLeft lexical)
        (Bool.andLeft sound)
        edges
    | [item, next, ..more] =>
      let split: ((item.spelt False ++ [","] ++ commaSpelt [next, ..more]).filter notCloser)
        = (item.spelt False).filter notCloser ++ (commaSpelt [next, ..more]).filter notCloser :=
        rewrite List.filterAppend (item.spelt False) ([","] ++ commaSpelt [next, ..more]) notCloser
      let (itemEdges, restEdges) :=
        edgeSplit pending
          ((item.spelt False).filter notCloser)
          ((commaSpelt [next, ..more]).filter notCloser)
          False
          end
          (exprHas item (Bool.andLeft within) (Bool.andLeft lexical) (Bool.andLeft sound))
          (commaHas [next, ..more] byComputing (Bool.andRight within) (Bool.andRight lexical) (Bool.andRight sound))
          (rewrite split at edges then edges)
      Bool.andIntro
        (wordsEdgeOfMarks item False False pending
          (Bool.andLeft within)
          (Bool.andLeft shaped)
          (Bool.andLeft lexical)
          (Bool.andLeft sound)
          itemEdges)
        (itemsEdgeOfMarks
          [next, ..more]
          end
          (pendingAfter pending ((item.spelt False).filter notCloser))
          (Bool.andRight within)
          (Bool.andRight shaped)
          (Bool.andRight lexical)
          (Bool.andRight sound)
          restEdges)

--| A call's arguments, from the marks.
theorem argumentsEdgeOfMarks ∀ (arguments: List Expr) (end pending: Bool)
    (filled: arguments.isEmpty = False)
    (within: allWithin1 arguments = True)
    (shaped: allShaped1 arguments = True)
    (lexical: allLexical1 arguments = True)
    (sound: allSound arguments = True)
    (edges: EdgeMarks pending ((argumentsSpelt arguments).filter notCloser) False end):
    lastWordsEdge1 end arguments = True :=
  match arguments with
    | [last] =>
      wordsEdgeOfMarks last False end pending
        (Bool.andLeft within)
        (Bool.andLeft shaped)
        (Bool.andLeft lexical)
        (Bool.andLeft sound)
        (rewrite List.appendNil (last.spelt False) at edges then edges)
    | [argument, next, ..more] =>
      let split: ((argument.spelt False ++ argumentsSpelt [next, ..more]).filter notCloser)
        = (argument.spelt False).filter notCloser ++ (argumentsSpelt [next, ..more]).filter notCloser :=
        List.filterAppend (argument.spelt False) (argumentsSpelt [next, ..more]) notCloser
      let (argumentEdges, restEdges) :=
        edgeSplit pending
          ((argument.spelt False).filter notCloser)
          ((argumentsSpelt [next, ..more]).filter notCloser)
          False
          end
          (exprHas argument (Bool.andLeft within) (Bool.andLeft lexical) (Bool.andLeft sound))
          (argumentsHas [next, ..more] byComputing (Bool.andRight within) (Bool.andRight lexical) (Bool.andRight sound))
          (rewrite split at edges then edges)
      Bool.andIntro
        (wordsEdgeOfMarks argument False False pending
          (Bool.andLeft within)
          (Bool.andLeft shaped)
          (Bool.andLeft lexical)
          (Bool.andLeft sound)
          argumentEdges)
        (argumentsEdgeOfMarks
          [next, ..more]
          end
          (pendingAfter pending ((argument.spelt False).filter notCloser))
          byComputing
          (Bool.andRight within)
          (Bool.andRight shaped)
          (Bool.andRight lexical)
          (Bool.andRight sound)
          restEdges)

-- `calm` changes no comment.

theorem wordEdgeKept ∀ (word: Word) (item closer lead end: Bool):
    (word.kept item closer).wordEdge1 lead end = word.wordEdge1 lead end :=
  rewrite keptNoted word item closer, keptTrails word item closer

theorem wordsEdgeCalm ∀ (expr: Expr) (item lead end: Bool)
    (within: expr.within1 = True):
    (expr.calm item).wordsEdge1 lead end = expr.wordsEdge1 lead end :=
  match expr with
    | Atom kind word => wordEdgeKept word item False lead end
    | Paren open inner close =>
      rewrite wordEdgeKept open item False lead False, wordsEdgeCalm inner False False end within
    | Tuple open items comma close =>
      rewrite wordEdgeKept open item False lead False, lastEdgeCalmAll end True items within
    | ListOf open items comma close =>
      rewrite calmItemsEmpty items,
          wordEdgeKept open item False lead (end && items.isEmpty),
          lastEdgePick end (items.all Expr.plainItem) items within
    | App head arguments =>
      rewrite calmAllEmpty arguments False,
          wordsEdgeCalm head item lead False (Bool.andLeft within),
          lastEdgeCalmAll end False arguments (Bool.andRight within)
    | Infix kind left operator right =>
      match kind with
        | InfixBinary =>
          let (leftWithin, rightWithin, _) := within
          rewrite wordsEdgeCalm left item lead False leftWithin,
              wordEdgeKept operator False False False False,
              wordsEdgeCalm right False False end rightWithin
        | InfixArrow =>
          let (leftWithin, rightWithin, _) := within
          rewrite wordsEdgeCalm left item lead False leftWithin,
              wordEdgeKept operator False False False False,
              wordsEdgeCalm right False False end rightWithin
        | _ => cases
    | Prefix operator operand =>
      rewrite wordEdgeKept operator item False lead False, wordsEdgeCalm operand False False end (Bool.andLeft within)

theorem lastEdgeCalmAll ∀ (end item: Bool) (items: List Expr)
    (within: allWithin1 items = True):
    lastWordsEdge1 end (calmAll item items) = lastWordsEdge1 end items :=
  match items with
    | [] => byComputing
    | [last] => wordsEdgeCalm last item False end (Bool.andLeft within)
    | [first, next, ..more] =>
      rewrite wordsEdgeCalm first item False False (Bool.andLeft within),
          lastEdgeCalmAll end item [next, ..more] (Bool.andRight within)

theorem lastEdgePick ∀ (end plain: Bool) (items: List Expr)
    (within: allWithin1 items = True):
    lastWordsEdge1 end (pickItems plain items) = lastWordsEdge1 end items :=
  match plain with
    | False => lastEdgeCalmAll end True items within
    | True =>
      match items with
        | [] => byComputing
        | [last] => wordsEdgeCalm last False False end (Bool.andLeft within)
        | [first, next, ..more] =>
          rewrite wordsEdgeCalm first False False False (Bool.andLeft within),
              lastEdgeCalmAll end True [next, ..more] (Bool.andRight within)

-- Closed examples of the token lemmas.

theorem operatorPlainExample: notCloser "+" = True ∧ notComment "+" = True := operatorPlain "+" byComputing

theorem prefixPlainExample: notCloser "!" = True ∧ notComment "!" = True := prefixPlain "!" byComputing

theorem textCloserExample: notCloser (fixedWord ")" Comments.none).text = False :=
  textCloser (fixedWord ")" Comments.none) ")" byComputing byComputing
