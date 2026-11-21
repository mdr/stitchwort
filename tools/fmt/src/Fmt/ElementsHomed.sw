--| `homedOfSettled` (SW-4144, piece E1 of the comments-anywhere plan, SW-4130): a settled slice 1 declaration is
--| homed node by node (`Expr.homed`).
--|
--| `settled` reads the declaration's words once, from the back (`homedBack`) and forwards (`arrowsBare`). A node's
--| words are one run of them, so the induction carries the words that come before it (`rest`, newest first) and
--| reads each node's own facts off: `homedBack` of a run followed by `rest` gives `homedBack` of what lies before,
--| and a closer's check `trailsBack earlier` stops at its own opener (`trailsBackCoded`: the opener is no closer),
--| so it is `trailsBeforeClose`, whatever `rest` holds.

namespace Fmt.ElementsHomed
import Std (Bool, DecEq, Eq, List, Nat, Option, Text)
import Syntax (Decl, DefBody, Expr, Header, InfixKind, Tok, Word)
import Fmt (..)
import Fmt.TrailsProofs (Coded, codedSnoc, trailsBackCoded)
import Fmt.SpellProofs (firstWordLead, wordsLead)
import Syntax.SharedFacts (arrowsBarePrefix, arrowsBareSuffix, headerResultWithin, homedBackSuffix)

-- What `settled` gives the layout.

--| A closer with a comment after it has comments above it, or follows code that ends its line with one (`before`).
def Word.homedAfter (word: Word) (before: Bool): Bool := !word.trails || word.noted || before

--| `Decl.settled`'s `homedBack` and `arrowsBare`, node by node: each closer is homed after the code before it in
--| its brackets, and `->` has no comment after it and its right operand none above its first token.
def Expr.homed: Expr → Bool
  | Atom _ _ => True
  | Paren open inner close => inner.homed && close.homedAfter (Paren open inner close).trailsBeforeClose
  | Tuple open items trailing close =>
    allHomed items && close.homedAfter (Tuple open items trailing close).trailsBeforeClose
  | ListOf open items trailing close =>
    allHomed items && close.homedAfter (ListOf open items trailing close).trailsBeforeClose
  | App head arguments => head.homed && allHomed arguments
  | Infix InfixBinary left _ right => left.homed && right.homed
  | Infix InfixArrow left operator right => left.homed && right.homed && !operator.trails && !right.noted
  | Prefix _ operand => operand.homed
  | _ => False

def allHomed: List Expr → Bool
  | [] => True
  | [expr, ..rest] => expr.homed && allHomed rest

--| A slice 1 declaration's type and value are homed.
def Decl.homed: Decl → Bool
  | Definition [] header (Assigned _ value) => header.result.homed && value.homed
  | _ => False

-- Words read back.

--| Two runs, then what lies before them: each is homed after what comes before it.
theorem homedBehind ∀ (xs ys rest: List Word)
    (homed: homedBack ((xs ++ ys) ++ rest) = True):
    homedBack (ys ++ rest) = True ∧ homedBack (xs ++ (ys ++ rest)) = True :=
  let regrouped: homedBack (xs ++ (ys ++ rest)) = True := rewrite (List.appendAssoc xs ys rest).flipped then homed
  (homedBackSuffix xs (ys ++ rest) regrouped, regrouped)

theorem homedAfterOf ∀ (trails noted before: Bool)
    (homed: (!(True && trails) || False || noted || before) = True):
    (!trails || noted || before) = True :=
  match trails, noted, before with
    | True, True, True | False => homed
    | True, False, True => homed
    | False, True | False, True | False => homed

theorem appendNonEmpty ∀ (xs: List Word) (last: Word) (ys: List Word): (xs ++ [last, ..ys]).isEmpty = False :=
  match xs with | [] | [_, .._] => byComputing

--| A closer is homed after the code before it: with a comment after it, it has comments above it or the code
--| before it, closers aside, ends its line with one.
theorem closerHomedOf ∀ (close: Word) (earlier: List Word)
    (closer: isCloserText close.text = True)
    (some: earlier.isEmpty = False)
    (homed: homedBack [close, ..earlier] = True):
    close.homedAfter (trailsBack earlier) = True :=
  let check := Bool.andLeft homed
  homedAfterOf close.trails close.noted (trailsBack earlier) (rewrite closer, some at check then check)

--| A bracket's closer and what it holds, read back from the closer: what the bracket holds is homed with the
--| opener and what is before it behind, and the closer is homed after what its bracket holds, closers aside, whatever
--| lies before the opener.
theorem bracketBack ∀ (open close: Word) (inside rest: List Word)
    (closer: isCloserText close.text = True)
    (opens: isCloserText open.text = False)
    (homed: homedBack ([close, ..(inside ++ [open])] ++ rest) = True):
    homedBack (inside ++ ([open] ++ rest)) = True ∧ close.homedAfter (trailsBack (inside ++ [open])) = True :=
  let within: homedBack (inside ++ ([open] ++ rest)) = True :=
    rewrite (List.appendAssoc inside [open] rest).flipped then Bool.andRight homed
  let some: ((inside ++ [open]) ++ rest).isEmpty = False :=
    rewrite List.appendAssoc inside [open] rest then appendNonEmpty inside open rest
  let after := closerHomedOf close ((inside ++ [open]) ++ rest) closer some homed
  (within, rewrite (trailsBackCoded (inside ++ [open]) rest (codedSnoc inside open opens)).flipped then after)

-- Words read forwards.

--| `->` is read with its next word: drop the first word.
theorem arrowsTail ∀ [x: Word] (zs: List Word) (arrows: arrowsBare [x, ..zs] = True): arrowsBare zs = True :=
  match zs with
    | [] => byComputing
    | [z, ..more] => Bool.andRight arrows

-- The runs of an expression's words.

--| Two runs joined: the later one's words come first when read back.
theorem joinBack ∀ (front back rest: List Word)
    (homed: homedBack ((front ++ back).reverse ++ rest) = True):
    homedBack (front.reverse ++ rest) = True ∧ homedBack (back.reverse ++ (front.reverse ++ rest)) = True :=
  homedBehind back.reverse front.reverse rest (rewrite (List.reverseAppend front back).flipped then homed)

--| A word then a run.
theorem consBack ∀ [head: Word] (tail: List Word) [rest: List Word]
    (homed: homedBack ([head, ..tail].reverse ++ rest) = True):
    homedBack (tail.reverse ++ ([head] ++ rest)) = True :=
  rewrite (List.appendAssoc tail.reverse [head] rest).flipped, (List.reverseCons head tail).flipped then homed

--| The bracket's words, read back: its closer, what it holds, its opener.
theorem bracketReverse ∀ (open close: Word) (inside: List Word):
    ([open, ..inside] ++ [close]).reverse = [close, ..(inside.reverse ++ [open])] :=
  rewrite List.reverseSnoc [open, ..inside] close, List.reverseCons open inside

theorem arrowOf ∀ (operator next: Word) (more: List Word)
    (arrow: operatorTok operator.text = Some Arrow)
    (arrows: arrowsBare [operator, next, ..more] = True):
    (!operator.trails && !next.noted) = True :=
  let check := Bool.andLeft arrows
  rewrite arrow at check then check

theorem arrowTokOf ∀ (text: Text) (arrow: arrowText1 text = True): operatorTok text = Some Arrow :=
  Bool.orElim arrow (isArrow => rewrite DecEq.sound isArrow) (isArrow => rewrite DecEq.sound isArrow)

--| A bracket's node: its closer is a closer and its opener is none.
theorem bracketHomed ∀ [open close: Word] (inside: List Word) [rest: List Word]
    (closer: isCloserText close.text = True)
    (opens: isCloserText open.text = False)
    (homed: homedBack (([open, ..inside] ++ [close]).reverse ++ rest) = True):
    homedBack (inside.reverse ++ ([open] ++ rest)) = True
      ∧ close.homedAfter (trailsBack (([open, ..inside] ++ [close]).reverse.drop 1)) = True :=
  let (within, after) :=
    bracketBack open close inside.reverse rest closer opens
      (Eq.subst (words => homedBack (words ++ rest) = True) (bracketReverse open close inside) homed)
  (within, rewrite bracketReverse open close inside then after)

theorem arrowsInside ∀ [open close: Word] (inside: List Word)
    (arrows: arrowsBare ([open, ..inside] ++ [close]) = True):
    arrowsBare inside = True :=
  arrowsTail inside (arrowsBarePrefix [open, ..inside] [close] arrows)

-- The induction.

theorem homedAt ∀ (expr: Expr)
    (within: expr.within1 = True)
    (lexical: expr.lexical = True) (rest: List Word)
    (homed: homedBack (expr.words.reverse ++ rest) = True)
    (arrows: arrowsBare expr.words = True):
    expr.homed = True :=
  match expr, within with
    | Atom kind word, within => byComputing
    | Prefix operator operand, within =>
      homedAt operand
        (Bool.andLeft within)
        (Bool.andRight lexical)
        ([operator] ++ rest)
        (consBack operand.words homed)
        (arrowsTail operand.words arrows)
    | Paren open inner close, within =>
      let isClose: close.text = ")" := DecEq.sound (Bool.andLeft (Bool.andRight lexical))
      let isOpen: open.text = "(" := DecEq.sound (Bool.andLeft lexical)
      let (holds, closes) := bracketHomed inner.words (rewrite isClose) (rewrite isOpen) homed
      Bool.andIntro
        (homedAt inner within
          (Bool.andRight (Bool.andRight lexical))
          ([open] ++ rest)
          holds
          (arrowsInside inner.words arrows))
        closes
    | Tuple open items trailing close, within =>
      let isClose: close.text = ")" := DecEq.sound (Bool.andLeft (Bool.andRight lexical))
      let isOpen: open.text = "(" := DecEq.sound (Bool.andLeft lexical)
      let (holds, closes) := bracketHomed (itemsWords items) (rewrite isClose) (rewrite isOpen) homed
      Bool.andIntro
        (allHomedAt items within
          (Bool.andRight (Bool.andRight lexical))
          ([open] ++ rest)
          holds
          (arrowsInside (itemsWords items) arrows))
        closes
    | ListOf open items trailing close, within =>
      let isClose: close.text = "]" := DecEq.sound (Bool.andLeft (Bool.andRight lexical))
      let isOpen: open.text = "[" := DecEq.sound (Bool.andLeft lexical)
      let (holds, closes) := bracketHomed (itemsWords items) (rewrite isClose) (rewrite isOpen) homed
      Bool.andIntro
        (allHomedAt items within
          (Bool.andRight (Bool.andRight lexical))
          ([open] ++ rest)
          holds
          (arrowsInside (itemsWords items) arrows))
        closes
    | App head arguments, within =>
      let (headBack, argumentsBack) := joinBack head.words (itemsWords arguments) rest homed
      Bool.andIntro
        (homedAt head
          (Bool.andLeft within)
          (Bool.andLeft lexical)
          rest
          headBack
          (arrowsBarePrefix head.words (itemsWords arguments) arrows))
        (allHomedAt arguments
          (Bool.andRight within)
          (Bool.andRight lexical)
          (head.words.reverse ++ rest)
          argumentsBack
          (arrowsBareSuffix head.words (itemsWords arguments) arrows))
    | Infix InfixBinary left operator right, within =>
      let (leftBack, rightBack) := joinBack left.words [operator, ..right.words] rest homed
      let leftHomed :=
        homedAt left
          (Bool.andLeft within)
          (Bool.andLeft lexical)
          rest
          leftBack
          (arrowsBarePrefix left.words [operator, ..right.words] arrows)
      let rightArrows := arrowsTail right.words (arrowsBareSuffix left.words [operator, ..right.words] arrows)
      Bool.andIntro leftHomed
        (homedAt right
          (Bool.andLeft (Bool.andRight within))
          (Bool.andRight (Bool.andRight lexical))
          ([operator] ++ (left.words.reverse ++ rest))
          (consBack right.words rightBack)
          rightArrows)
    | Infix InfixArrow left operator right, within =>
      let rightWithin: right.within1 = True := Bool.andLeft (Bool.andRight within)
      let (leftBack, rightBack) := joinBack left.words [operator, ..right.words] rest homed
      let leftHomed :=
        homedAt left
          (Bool.andLeft within)
          (Bool.andLeft lexical)
          rest
          leftBack
          (arrowsBarePrefix left.words [operator, ..right.words] arrows)
      let tailArrows := arrowsBareSuffix left.words [operator, ..right.words] arrows
      let rightHomed :=
        homedAt right rightWithin
          (Bool.andRight (Bool.andRight lexical))
          ([operator] ++ (left.words.reverse ++ rest))
          (consBack right.words rightBack)
          (arrowsTail right.words tailArrows)
      let (more, words) := wordsLead right rightWithin
      let bare :=
        arrowOf operator right.lead more
          (arrowTokOf operator.text (Bool.andRight (Bool.andRight within)))
          (Eq.subst (ws => arrowsBare [operator, ..ws] = True) words tailArrows)
      Bool.andIntro leftHomed (Bool.andIntro rightHomed (rewrite (notedLead right rightWithin) then bare))

--| Items or arguments, the same.
theorem allHomedAt ∀ (items: List Expr)
    (within: allWithin1 items = True)
    (lexical: allLexical items = True) (rest: List Word)
    (homed: homedBack ((itemsWords items).reverse ++ rest) = True)
    (arrows: arrowsBare (itemsWords items) = True):
    allHomed items = True :=
  match items with
    | [] => byComputing
    | [item, ..more] =>
      let (itemBack, moreBack) := joinBack item.words (itemsWords more) rest homed
      Bool.andIntro
        (homedAt item
          (Bool.andLeft within)
          (Bool.andLeft lexical)
          rest
          itemBack
          (arrowsBarePrefix item.words (itemsWords more) arrows))
        (allHomedAt more
          (Bool.andRight within)
          (Bool.andRight lexical)
          (item.words.reverse ++ rest)
          moreBack
          (arrowsBareSuffix item.words (itemsWords more) arrows))

theorem notedLead ∀ (expr: Expr) (within: expr.within1 = True): expr.noted = expr.lead.noted :=
  let unfolded: expr.noted = expr.firstWord.noted := byComputing
  rewrite unfolded, firstWordLead expr within

--| A settled slice 1 declaration's type and value are homed: `homedBack` and `arrowsBare` of the declaration's
--| words, read node by node. A closer's code before it, read back through closers, stops at a token of its own
--| brackets (the opener, at the latest), so the test is the node's own (`trailsBackCoded`).
--|
--| Proof idea: the declaration's words are `def name :` then the type, `:=`, the value. Read back from the end,
--| the value's words come first, then `:=`, the type's, and the head, so each is a run with what lies before it
--| (`joinBack`) and `homedAt` reads its nodes off (an `Atom` is homed with no check; a bracket's closer, from
--| `bracketBack`; `->`, from `arrowsBare` at the operator and its right operand's first word).
theorem homedOfSettled ∀ (decl: Decl)
    (within: decl.within1 = True)
    (lexical: decl.lexical = True)
    (settled: decl.settled = True):
    decl.homed = True :=
  match decl, within with
    | Definition [] header (Assigned colonEq value), within =>
      let resultWithin: header.result.within1 = True := headerResultWithin header (Bool.andLeft within)
      let valueWithin: value.within1 = True := Bool.andRight within
      let resultLexical: header.result.lexical = True := Bool.andLeft (Bool.andRight lexical)
      let valueLexical: value.lexical = True := Bool.andRight (Bool.andRight lexical)
      let head := [fixedWord "def" header.keyword, header.name, fixedWord ":" header.colon]
      let colonEqWord := fixedWord ":=" colonEq
      let homed: homedBack (head ++ (header.result.words ++ [colonEqWord, ..value.words])).reverse = True :=
        Bool.andLeft settled
      let arrows: arrowsBare (head ++ (header.result.words ++ [colonEqWord, ..value.words])) = True :=
        Bool.andLeft (Bool.andRight settled)
      let homedOnto: homedBack ((head ++ (header.result.words ++ [colonEqWord, ..value.words])).reverse ++ []) = True :=
        rewrite List.appendNil (head ++ (header.result.words ++ [colonEqWord, ..value.words])).reverse then homed
      let (_, tailBack) := joinBack head (header.result.words ++ [colonEqWord, ..value.words]) [] homedOnto
      let (resultBack, valueBack) :=
        joinBack header.result.words [colonEqWord, ..value.words] (head.reverse ++ []) tailBack
      let tailArrows := arrowsBareSuffix head (header.result.words ++ [colonEqWord, ..value.words]) arrows
      Bool.andIntro
        (homedAt header.result resultWithin resultLexical
          (head.reverse ++ [])
          resultBack
          (arrowsBarePrefix header.result.words [colonEqWord, ..value.words] tailArrows))
        (homedAt value valueWithin valueLexical
          ([colonEqWord] ++ (header.result.words.reverse ++ (head.reverse ++ [])))
          (consBack value.words valueBack)
          (arrowsTail value.words (arrowsBareSuffix header.result.words [colonEqWord, ..value.words] tailArrows)))
