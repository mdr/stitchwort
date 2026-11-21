--| Two runs of the parser on items that differ only in their comments give alike trees (docs/reviews/
--| SW-4132-two-run-parse.md), continued from `Syntax.FollowsFormsArms`: patterns. It has the patterns'
--| trees and parser, record patterns, constructor patterns, bracketed, tuple and list patterns, the components of
--| tuples, lists and alternatives, and the rule's knot; and the ladder's tiers, built from the facts proved above and
--| the statement-level facts they need.

namespace Syntax.FollowsFormsPatterns
import Std (Bool, DecEq, Eq, List, Nat, Option, Pair, Parse, Result, Text, Unit, Void)
import Syntax (..)
import Fmt (..)
import Fmt.Walk (..)
import Fmt.BlankProofs (blankPure)
import Syntax.DeafProofs (..)
import Syntax.FollowsBase (..)
import Syntax.FollowsLadder (..)
import Syntax.FollowsForms (..)
import Syntax.FollowsFormsBinders (..)
import Syntax.FollowsFormsArms (..)

-- Patterns: the trees.

def FieldPatternAlike (field twin: FieldPattern): Prop :=
  blankFieldPatterns (walkFieldPatterns blankPure [field]) = blankFieldPatterns (walkFieldPatterns blankPure [twin])

def FieldsPatternAlike (fields twin: FieldsPattern): Prop :=
  (walkFields blankPure fields).blank = (walkFields blankPure twin).blank

theorem fieldPatternsBlankCons ∀ (field: FieldPattern) (rest: List FieldPattern):
    blankFieldPatterns (walkFieldPatterns blankPure [field, ..rest])
      = blankFieldPatterns (walkFieldPatterns blankPure [field])
        ++ blankFieldPatterns (walkFieldPatterns blankPure rest) :=
  match field with | { name, value = (Some (_, _) | None) } => byComputing

theorem fieldPatternsBlank ∀ (fields twins: List FieldPattern)
    (alike: List.All2 FieldPatternAlike fields twins):
    blankFieldPatterns (walkFieldPatterns blankPure fields) = blankFieldPatterns (walkFieldPatterns blankPure twins) :=
  List.all2Join
    [f := list => blankFieldPatterns (walkFieldPatterns blankPure list)]
    [key := field => blankFieldPatterns (walkFieldPatterns blankPure [field])]
    (k rest => k ++ rest)
    fieldPatternsBlankCons
    (x y same => same)
    fields
    twins
    alike

theorem alikeFieldPattern ∀ (name nameTwin: Word)
    (names: WordsAlike name nameTwin) (value twin: Option (Word, Pattern))
    (values: Option.Alike (PairAlike WordsAlike PatternsAlike) value twin):
    FieldPatternAlike { name, value } { name = nameTwin, value = twin } :=
  match value, twin with
    | None, None =>
      calc blankFieldPatterns (walkFieldPatterns blankPure [{ name, value = None }])
        _ = [{ name = name.blank, value = None }] := byComputing
        _ = [{ name = nameTwin.blank, value = None }] := rewrite names
        _ = blankFieldPatterns (walkFieldPatterns blankPure [{ name = nameTwin, value = None }]) := byComputing
    | Some (equals, pattern), Some (equalsTwin, patternTwin) =>
      calc blankFieldPatterns (walkFieldPatterns blankPure [{ name, value = Some (equals, pattern) }])
        _ = [{ name = name.blank, value = Some (equals.blank, pattern.walk blankPure) }] := byComputing
        _ = [{ name = nameTwin.blank, value = Some (equalsTwin.blank, patternTwin.walk blankPure) }] :=
          rewrite names, values.left, values.right
        _ = blankFieldPatterns
            (walkFieldPatterns blankPure [{ name = nameTwin, value = Some (equalsTwin, patternTwin) }]) := byComputing

theorem alikeFieldsPattern ∀ (open openTwin: Word)
    (opens: WordsAlike open openTwin) (fields twins: List FieldPattern)
    (alike: List.All2 FieldPatternAlike fields twins)
    (trailing: Bool) (rest restTwin: Option Word)
    (rests: Option.Alike WordsAlike rest restTwin) (close closeTwin: Word)
    (closes: WordsAlike close closeTwin):
    FieldsPatternAlike { open, fields, trailingComma = trailing, rest, close } {
      open = openTwin,
      fields = twins,
      trailingComma = trailing,
      rest = restTwin,
      close = closeTwin
    } :=
  rewrite repeatedly [opens, fieldPatternsBlank fields twins alike, keywordBlank rest restTwin rests, closes]

theorem alikePatternWord ∀ (kind: Tok) (word twin: Word)
    (words: WordsAlike word twin):
    PatternsAlike (PatternWord kind word) (PatternWord kind twin) :=
  rewrite repeatedly [words]

theorem alikePatternCtor ∀ (name nameTwin: Word)
    (names: WordsAlike name nameTwin) (arguments twins: List Pattern)
    (alike: List.All2 PatternsAlike arguments twins):
    PatternsAlike (PatternCtor name arguments) (PatternCtor nameTwin twins) :=
  rewrite repeatedly [names, walkPatternsAlike arguments twins alike]

theorem alikePatternCtorFields ∀ (name nameTwin: Word)
    (names: WordsAlike name nameTwin) (fields twins: FieldsPattern)
    (alike: FieldsPatternAlike fields twins):
    PatternsAlike (PatternCtorFields name fields) (PatternCtorFields nameTwin twins) :=
  rewrite repeatedly [names, alike]

theorem alikePatternRecord ∀ (fields twins: FieldsPattern)
    (alike: FieldsPatternAlike fields twins):
    PatternsAlike (PatternRecord fields) (PatternRecord twins) :=
  rewrite repeatedly [alike]

theorem alikePatternTuple ∀ (open openTwin: Word)
    (opens: WordsAlike open openTwin) (items twins: List Pattern)
    (alike: List.All2 PatternsAlike items twins)
    (trailing: Bool) (close closeTwin: Word)
    (closes: WordsAlike close closeTwin):
    PatternsAlike (PatternTuple open items trailing close) (PatternTuple openTwin twins trailing closeTwin) :=
  rewrite repeatedly [opens, walkPatternsAlike items twins alike, closes]

theorem tailsBlank ∀ (tail twin: Option (Word, Pattern))
    (alike: Option.Alike (PairAlike WordsAlike PatternsAlike) tail twin):
    blankAfterWord (walkTail blankPure tail) = blankAfterWord (walkTail blankPure twin) :=
  match tail, twin with
    | None, None => byComputing
    | Some (dots, rest), Some (dotsTwin, restTwin) =>
      calc blankAfterWord (walkTail blankPure (Some (dots, rest)))
        _ = Some (dots.blank, rest.walk blankPure) := byComputing
        _ = Some (dotsTwin.blank, restTwin.walk blankPure) := rewrite alike.left, alike.right
        _ = blankAfterWord (walkTail blankPure (Some (dotsTwin, restTwin))) := byComputing

theorem alikePatternList ∀ (open openTwin: Word)
    (opens: WordsAlike open openTwin) (items twins: List Pattern)
    (alike: List.All2 PatternsAlike items twins)
    (trailing: Bool) (tail tailTwin: Option (Word, Pattern))
    (tails: Option.Alike (PairAlike WordsAlike PatternsAlike) tail tailTwin) (close closeTwin: Word)
    (closes: WordsAlike close closeTwin):
    PatternsAlike
      (PatternList open items trailing tail close)
      (PatternList openTwin twins trailing tailTwin closeTwin) :=
  rewrite repeatedly [opens, walkPatternsAlike items twins alike, tailsBlank tail tailTwin tails, closes]

theorem alikePatternNamed ∀ (open openTwin name nameTwin colonEq colonEqTwin: Word)
    (opens: WordsAlike open openTwin)
    (names: WordsAlike name nameTwin)
    (colonEqs: WordsAlike colonEq colonEqTwin) (value twin: Pattern)
    (values: PatternsAlike value twin) (close closeTwin: Word)
    (closes: WordsAlike close closeTwin):
    PatternsAlike
      (PatternNamed open name colonEq value close)
      (PatternNamed openTwin nameTwin colonEqTwin twin closeTwin) :=
  rewrite repeatedly [opens, names, colonEqs, values, closes]

theorem alikePatternParen ∀ (open openTwin: Word)
    (opens: WordsAlike open openTwin) (inner twin: Pattern)
    (inners: PatternsAlike inner twin) (close closeTwin: Word)
    (closes: WordsAlike close closeTwin):
    PatternsAlike (PatternParen open inner close) (PatternParen openTwin twin closeTwin) :=
  rewrite repeatedly [opens, inners, closes]

theorem alikePatternNegative ∀ (minus minusTwin number numberTwin: Word)
    (minuses: WordsAlike minus minusTwin)
    (numbers: WordsAlike number numberTwin):
    PatternsAlike (PatternNegative minus number) (PatternNegative minusTwin numberTwin) :=
  rewrite repeatedly [minuses, numbers]

theorem alikePatternAbsurd ∀ (open openTwin close closeTwin: Word)
    (opens: WordsAlike open openTwin)
    (closes: WordsAlike close closeTwin):
    PatternsAlike (PatternAbsurd open close) (PatternAbsurd openTwin closeTwin) :=
  rewrite repeatedly [opens, closes]

theorem alikePatternAppend ∀ (start twin: Pattern)
    (starts: PatternsAlike start twin) (operator operatorTwin: Word)
    (operators: WordsAlike operator operatorTwin) (rest restTwin: Pattern)
    (rests: PatternsAlike rest restTwin):
    PatternsAlike (PatternAppend start operator rest) (PatternAppend twin operatorTwin restTwin) :=
  rewrite repeatedly [starts, operators, rests]

theorem patternLinksBlank ∀ (links twins: List (Word, Pattern))
    (alike: List.All2 (PairAlike WordsAlike PatternsAlike) links twins):
    blankLinks (walkPatternLinks blankPure links) = blankLinks (walkPatternLinks blankPure twins) :=
  List.all2Join
    [f := list => blankLinks (walkPatternLinks blankPure list)]
    [key := link => (link.fst.blank, link.snd.walk blankPure)]
    (k rest => [k, ..rest])
    (link rest => match link with | (bar, alternative) => byComputing)
    (x y same => rewrite same.left, same.right)
    links
    twins
    alike

-- Patterns: the parser.

theorem followsNegativeDigits ∀ (modes: Modes) (minus minusTwin: Word)
    (minuses: WordsAlike minus minusTwin) (number: Bool):
    Parse.Follows SameCode PatternsAlike (() => negativeDigits modes minus number) (() =>
      negativeDigits modes minusTwin number) :=
  match number with
    | True =>
      Parse.followsMap
        (found => PatternNegative minus found)
        (found => PatternNegative minusTwin found)
        followsBump
        (found foundTwin founds => alikePatternNegative minus minusTwin found foundTwin minuses founds)
    | False => followsFail modes "a number" (() => modes.fail "a number")

theorem followsNegativePattern ∀ (modes: Modes):
    Parse.Follows SameCode PatternsAlike (() => negativePattern modes) (() => negativePattern modes) :=
  byWalking [followsNegativeDigits]

theorem followsPatternAppendOf ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (modes: Modes) (start startTwin: Pattern)
    (starts: PatternsAlike start startTwin)
    (next: PatternLevel) (plus: Bool):
    Parse.Follows SameCode PatternsAlike (() => patternAppendOf pself modes start next plus) (() =>
      patternAppendOf pselfTwin modes startTwin next plus) :=
  match !plus with
    | True => Parse.followsDone starts
    | False =>
      let texts: isTextPattern start = isTextPattern startTwin := calc isTextPattern start
        _ = isTextPattern (start.walk blankPure) := isTextPatternDeaf start
        _ = isTextPattern (startTwin.walk blankPure) := rewrite starts
        _ = isTextPattern startTwin := Eq.flipped (isTextPatternDeaf startTwin)
      rewrite texts then
        match isTextPattern startTwin with
          | True => Parse.followsThen followsBump (operator operatorTwin operators =>
            Parse.followsMap
              (rest => PatternAppend start operator rest)
              (rest => PatternAppend startTwin operatorTwin rest)
              (pknot { modes, level = next })
              (rest restTwin rests =>
                alikePatternAppend start startTwin starts operator operatorTwin operators rest restTwin rests))
          | False => followsFatalAny "a text pattern can only take a fixed start" (() =>
            Syntax.fatal "a text pattern can only take a fixed start")

theorem followsPatternAppend ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (modes: Modes) (start startTwin: Pattern)
    (starts: PatternsAlike start startTwin) (next: PatternLevel):
    Parse.Follows SameCode PatternsAlike (() => patternAppend pself modes start next) (() =>
      patternAppend pselfTwin modes startTwin next) :=
  byWalking [followsPatternAppendOf]

theorem followsAlternativeLinksOn ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (more: Nat) (modes: Modes) (next: PatternLevel) (found foundTwin: List (Word, Pattern))
    (founds: List.All2 (PairAlike WordsAlike PatternsAlike) found foundTwin)
    (rest: ∀ (found foundTwin: List (Word, Pattern)) => List.All2 (PairAlike WordsAlike PatternsAlike) found foundTwin
      → Parse.Follows SameCode
        (List.All2 (PairAlike WordsAlike PatternsAlike))
        (() => alternativeLinks more pself modes next found)
        (() => alternativeLinks more pselfTwin modes next foundTwin)) (items others: List Item)
    (same: List.All2 SameCode items others):
    Parse.Follows SameCode
      (List.All2 (PairAlike WordsAlike PatternsAlike))
      (() => alternativeLinksOn (Succ more) pself modes next found items)
      (() => alternativeLinksOn (Succ more) pselfTwin modes next foundTwin others) :=
  match items, others with
    | [], [] => Parse.followsDone (List.all2Reverse found foundTwin founds)
    | [bar, ..tail], [barTwin, ..tailTwin] =>
      let links: linkHere modes bar = linkHere modes barTwin :=
        deafItem (linkHere modes) (linkHereDeaf modes) bar barTwin same.left
      rewrite links then
        match linkHere modes barTwin with
          | True => Parse.followsThen followsBump (barLeaf barLeafTwin bars =>
            Parse.followsThen (pknot { modes, level = next }) (alternative alternativeTwin alternatives =>
              rest
                [(barLeaf, alternative), ..found]
                [(barLeafTwin, alternativeTwin), ..foundTwin]
                (Both (bars, alternatives) founds)))
          | False => Parse.followsDone (List.all2Reverse found foundTwin founds)

theorem followsAlternativeLinks ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (fuel: Nat) (modes: Modes) (next: PatternLevel) (found foundTwin: List (Word, Pattern))
    (founds: List.All2 (PairAlike WordsAlike PatternsAlike) found foundTwin):
    Parse.Follows SameCode
      (List.All2 (PairAlike WordsAlike PatternsAlike))
      (() => alternativeLinks fuel pself modes next found)
      (() => alternativeLinks fuel pselfTwin modes next foundTwin) :=
  match fuel with
    | Zero =>
      followsOn
        (seen => alternativeLinksOn Zero pself modes next found seen)
        (seen => alternativeLinksOn Zero pselfTwin modes next foundTwin seen)
        (seen others same =>
          match seen, others with
            | [], [] => Parse.followsDone (List.all2Reverse found foundTwin founds)
            | [item, ..tail], [other, ..tailTwin] => Parse.followsDone (List.all2Reverse found foundTwin founds))
    | Succ more =>
      followsOn
        (seen => alternativeLinksOn (Succ more) pself modes next found seen)
        (seen => alternativeLinksOn (Succ more) pselfTwin modes next foundTwin seen)
        (seen others same =>
          followsAlternativeLinksOn pknot more modes next found foundTwin founds
            (found1 found2 founds2 => followsAlternativeLinks pknot more modes next found1 found2 founds2)
            seen
            others
            same)

theorem followsAlternatives ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (modes: Modes) (first firstTwin: Pattern)
    (firsts: PatternsAlike first firstTwin) (next: PatternLevel):
    Parse.Follows SameCode PatternsAlike (() => alternatives pself modes first next) (() =>
      alternatives pselfTwin modes firstTwin next) :=
  Parse.followsThen Parse.followsMark (here hereTwin marks =>
    rewrite <- marks.right.right then
      Parse.followsMap
        (links => alternativesEnd first links)
        (links => alternativesEnd firstTwin links)
        (followsAlternativeLinks pknot (here.left + 1) modes next [] [] Trivial)
        (links linksTwin alike =>
          alternativesEndDeaf first firstTwin links linksTwin firsts (patternLinksBlank links linksTwin alike)))

-- Record patterns, `{ x, y = p, .. }`.

def FieldsRead (read twin: (List FieldPattern, Bool, Option Word)): Prop :=
  PairAlike (List.All2 FieldPatternAlike) (PairAlike Same (Option.Alike WordsAlike)) read twin

theorem followsFieldPatternValue ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (modes: Modes) (equals equalsTwin: Option Word)
    (equalses: Option.Alike WordsAlike equals equalsTwin):
    Parse.Follows SameCode
      (Option.Alike (PairAlike WordsAlike PatternsAlike))
      (() => fieldPatternValue pself modes equals)
      (() => fieldPatternValue pselfTwin modes equalsTwin) :=
  match equals, equalsTwin with
    | None, None => Parse.followsDone Trivial
    | Some word, Some twin =>
      Parse.followsMap
        (value => Some (word, value))
        (value => Some (twin, value))
        (pknot { modes, level = PatternFieldValue })
        (value valueTwin values => (equalses, values))

theorem followsFieldPatternNext ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern] (more: Nat)
    (modes: Modes) (found foundTwin: List FieldPattern)
    (founds: List.All2 FieldPatternAlike found foundTwin) (field fieldTwin: FieldPattern)
    (fields: FieldPatternAlike field fieldTwin) (comma commaTwin: Option Word)
    (commas: Option.Alike WordsAlike comma commaTwin)
    (rest: ∀ (found foundTwin: List FieldPattern) => List.All2 FieldPatternAlike found foundTwin
      → Parse.Follows SameCode FieldsRead (() => fieldPatterns more pself modes found) (() =>
        fieldPatterns more pselfTwin modes foundTwin)):
    Parse.Follows SameCode FieldsRead (() => fieldPatternNext more pself modes found field comma) (() =>
      fieldPatternNext more pselfTwin modes foundTwin fieldTwin commaTwin) :=
  match comma, commaTwin with
    | Some word, Some twin => rest [field, ..found] [fieldTwin, ..foundTwin] (Both fields founds)
    | None, None => Parse.followsDone (
      List.all2Reverse [field, ..found] [fieldTwin, ..foundTwin] (Both fields founds),
      byComputing,
      Trivial
    )

theorem followsFieldPatternClose ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (more: Nat) (modes: Modes) (found foundTwin: List FieldPattern)
    (founds: List.All2 FieldPatternAlike found foundTwin) (closed: Bool)
    (rest: ∀ (found foundTwin: List FieldPattern) => List.All2 FieldPatternAlike found foundTwin
      → Parse.Follows SameCode FieldsRead (() => fieldPatterns more pself modes found) (() =>
        fieldPatterns more pselfTwin modes foundTwin)):
    Parse.Follows SameCode FieldsRead (() => fieldPatternClose more pself modes found closed) (() =>
      fieldPatternClose more pselfTwin modes foundTwin closed) :=
  match closed with
    | True =>
      match found, foundTwin with
        | [], [] => Parse.followsDone (founds, byComputing, Trivial)
        | [item, ..tail], [twin, ..tailTwin] =>
          Parse.followsDone (List.all2Reverse found foundTwin founds, byComputing, Trivial)
    | False => Parse.followsThen (followsLower modes "a field name, or `..`") (name nameTwin names =>
      Parse.followsThen
        (Parse.followsThen (followsEat modes Equals) (equals equalsTwin equalses =>
          followsFieldPatternValue pknot modes equals equalsTwin equalses))
        (value valueTwin values =>
          Parse.followsThen (followsEat modes Comma) (comma commaTwin commas =>
            followsFieldPatternNext more modes found foundTwin founds
              { name, value }
              { name = nameTwin, value = valueTwin }
              (alikeFieldPattern name nameTwin names value valueTwin values)
              comma
              commaTwin
              commas
              rest)))

theorem followsFieldPatternStep ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (more: Nat) (modes: Modes) (found foundTwin: List FieldPattern)
    (founds: List.All2 FieldPatternAlike found foundTwin) (dots: Bool)
    (rest: ∀ (found foundTwin: List FieldPattern) => List.All2 FieldPatternAlike found foundTwin
      → Parse.Follows SameCode FieldsRead (() => fieldPatterns more pself modes found) (() =>
        fieldPatterns more pselfTwin modes foundTwin)):
    Parse.Follows SameCode FieldsRead (() => fieldPatternStep more pself modes found dots) (() =>
      fieldPatternStep more pselfTwin modes foundTwin dots) :=
  match dots with
    | True =>
      Parse.followsMap
        (found2 => (found.reverse, False, Some found2))
        (found2 => (foundTwin.reverse, False, Some found2))
        followsBump
        (found2 foundTwin2 founds2 => (List.all2Reverse found foundTwin founds, byComputing, founds2))
    | False => followsThenEq (followsAt modes RBrace) (closed =>
      followsFieldPatternClose pknot more modes found foundTwin founds closed rest)

theorem followsFieldPatterns ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (fuel: Nat) (modes: Modes) (found foundTwin: List FieldPattern)
    (founds: List.All2 FieldPatternAlike found foundTwin):
    Parse.Follows SameCode FieldsRead (() => fieldPatterns fuel pself modes found) (() =>
      fieldPatterns fuel pselfTwin modes foundTwin) :=
  match fuel with
    | Zero => Parse.followsDone (List.all2Reverse found foundTwin founds, byComputing, Trivial)
    | Succ more => followsThenEq (followsAt modes DotDot) (dots =>
      followsFieldPatternStep pknot more modes found foundTwin founds dots (found1 found2 founds2 =>
        followsFieldPatterns pknot more modes found1 found2 founds2))

theorem followsFieldsPatternEnd ∀ (inner: Modes) (open openTwin: Word)
    (opens: WordsAlike open openTwin) (read readTwin: (List FieldPattern, Bool, Option Word))
    (reads: FieldsRead read readTwin):
    Parse.Follows SameCode FieldsPatternAlike (() => fieldsPatternEnd inner open read) (() =>
      fieldsPatternEnd inner openTwin readTwin) :=
  match read, readTwin with
    | (fields, trailing, rest), (fieldsTwin, trailingTwin, restTwin) =>
      Parse.followsMap
        (close => { open, fields, trailingComma = trailing, rest, close })
        (close => { open = openTwin, fields = fieldsTwin, trailingComma = trailingTwin, rest = restTwin, close })
        (followsExpect inner RBrace "`,` or `}`")
        (close closeTwin closes =>
          rewrite <- reads.right.left then
            alikeFieldsPattern open openTwin opens fields fieldsTwin reads.left trailing rest restTwin reads.right.right
                close closeTwin closes)

theorem followsFieldsPattern ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin) (modes: Modes):
    Parse.Follows SameCode FieldsPatternAlike (() => fieldsPattern pself modes) (() => fieldsPattern pselfTwin modes) :=
  Parse.followsThen (followsExpect modes LBrace "`{`") (open openTwin opens =>
    Parse.followsThen Parse.followsMark (here hereTwin marks =>
      rewrite <- marks.right.right then
        Parse.followsThen
          (followsFieldPatterns pknot (here.left + 1) modes.inBrackets [] [] Trivial)
          (read readTwin reads => followsFieldsPatternEnd modes.inBrackets open openTwin opens read readTwin reads)))

-- Constructor patterns.

theorem wordTextSame ∀ (word twin: Word) (words: WordsAlike word twin): word.text = twin.text := calc word.text
  _ = word.blank.text := byComputing
  _ = twin.blank.text := rewrite words
  _ = twin.text := byComputing

theorem followsCtorFieldsEnd ∀ (name nameTwin: Word)
    (names: WordsAlike name nameTwin) (fields twins: FieldsPattern)
    (alike: FieldsPatternAlike fields twins)
    (stops: Tok → Bool) (seen: Option Tok):
    Parse.Follows SameCode PatternsAlike (() => ctorFieldsEnd name fields stops seen) (() =>
      ctorFieldsEnd nameTwin twins stops seen) :=
  match seen with
    | Some kind =>
      match stops kind with
        | True => Parse.followsDone (alikePatternCtorFields name nameTwin names fields twins alike)
        | False => followsFatalAny "braces after `${name.text}` in a pattern take no further arguments" (() =>
          Syntax.fatal "braces after `${nameTwin.text}` in a pattern take no further arguments")
    | None => Parse.followsDone (alikePatternCtorFields name nameTwin names fields twins alike)

theorem followsCtorListEnd ∀ (name nameTwin: Word)
    (names: WordsAlike name nameTwin) (arguments twins: List Pattern)
    (alike: List.All2 PatternsAlike arguments twins):
    Parse.Follows SameCode PatternsAlike (() => ctorListEnd name arguments) (() => ctorListEnd nameTwin twins) :=
  match arguments, twins with
    | [], [] => rewrite wordTextSame name nameTwin names then Parse.followsDone (alikePatternWord _ name nameTwin names)
    | [first, ..rest], [twin, ..restTwin] => Parse.followsDone (alikePatternCtor name nameTwin names _ _ alike)

theorem followsCtorRecordArgument ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (modes: Modes) (name nameTwin: Word)
    (names: WordsAlike name nameTwin) (found foundTwin: List Pattern)
    (founds: List.All2 PatternsAlike found foundTwin):
    Parse.Follows SameCode PatternsAlike (() => ctorRecordArgument pself modes name found) (() =>
      ctorRecordArgument pselfTwin modes nameTwin foundTwin) :=
  let uppers: lastIsUpper name found = lastIsUpper nameTwin foundTwin := calc lastIsUpper name found
    _ = lastIsUpper name.blank (walkPatterns blankPure found) := lastIsUpperDeaf name found
    _ = lastIsUpper nameTwin.blank (walkPatterns blankPure foundTwin) :=
      rewrite names, walkPatternsAlike found foundTwin founds
    _ = lastIsUpper nameTwin foundTwin := Eq.flipped (lastIsUpperDeaf nameTwin foundTwin)
  rewrite uppers then
    match lastIsUpper nameTwin foundTwin with
      | True =>
        followsFatalAny
          "a record pattern after a constructor in an argument of `${name.text}` is written in brackets: `({ … })`"
          (() =>
            Syntax.fatal
              "a record pattern after a constructor in an argument of `${nameTwin.text}` is written in brackets: `({ … })`")
      | False =>
        Parse.followsMap
          (fields => PatternRecord fields)
          (fields => PatternRecord fields)
          (followsFieldsPattern pknot modes)
          (fields fieldsTwin fieldses => alikePatternRecord fields fieldsTwin fieldses)

theorem followsCtorArgMinus ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (more: Nat) (modes: Modes) (name nameTwin: Word) (stops: Tok → Bool) (found foundTwin: List Pattern)
    (founds: List.All2 PatternsAlike found foundTwin) (minus: Bool)
    (rest: ∀ (found foundTwin: List Pattern) => List.All2 PatternsAlike found foundTwin
      → Parse.Follows SameCode (List.All2 PatternsAlike) (() => ctorArgList more pself modes name stops found) (() =>
        ctorArgList more pselfTwin modes nameTwin stops foundTwin)):
    Parse.Follows SameCode (List.All2 PatternsAlike) (() => ctorArgMinus more pself modes name stops found minus) (() =>
      ctorArgMinus more pselfTwin modes nameTwin stops foundTwin minus) :=
  byWalking [followsNegativePattern]

theorem followsCtorArgBrace ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (more: Nat) (modes: Modes) (name nameTwin: Word)
    (names: WordsAlike name nameTwin)
    (stops: Tok → Bool) (found foundTwin: List Pattern)
    (founds: List.All2 PatternsAlike found foundTwin) (brace: Bool)
    (rest: ∀ (found foundTwin: List Pattern) => List.All2 PatternsAlike found foundTwin
      → Parse.Follows SameCode (List.All2 PatternsAlike) (() => ctorArgList more pself modes name stops found) (() =>
        ctorArgList more pselfTwin modes nameTwin stops foundTwin)):
    Parse.Follows SameCode (List.All2 PatternsAlike) (() => ctorArgBrace more pself modes name stops found brace) (() =>
      ctorArgBrace more pselfTwin modes nameTwin stops foundTwin brace) :=
  match brace with
    | True =>
      Parse.followsThen
        (followsCtorRecordArgument pknot modes name nameTwin names found foundTwin founds)
        (entry entryTwin entries => rest [entry, ..found] [entryTwin, ..foundTwin] (Both entries founds))
    | False =>
      followsOn
        (seen => ctorArgMinus more pself modes name stops found (argumentMinus seen))
        (seen => ctorArgMinus more pselfTwin modes nameTwin stops foundTwin (argumentMinus seen))
        (seen others same =>
          rewrite deafOfStripped argumentMinus argumentMinusDeaf seen others same then
            followsCtorArgMinus pknot more modes name nameTwin stops found foundTwin founds (argumentMinus others) rest)

theorem followsCtorArgList ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (fuel: Nat) (modes: Modes) (name nameTwin: Word)
    (names: WordsAlike name nameTwin)
    (stops: Tok → Bool) (found foundTwin: List Pattern)
    (founds: List.All2 PatternsAlike found foundTwin):
    Parse.Follows SameCode (List.All2 PatternsAlike) (() => ctorArgList fuel pself modes name stops found) (() =>
      ctorArgList fuel pselfTwin modes nameTwin stops foundTwin) :=
  followsThenEq (followsPeek modes) (seen =>
    match fuel, seen with
      | Succ more, Some kind =>
        match stops kind with
          | True => Parse.followsDone (List.all2Reverse found foundTwin founds)
          | False =>
            followsCtorArgBrace pknot more modes name nameTwin names stops found foundTwin founds
              (kind == LBrace)
              (found1 found2 founds2 =>
                followsCtorArgList pknot more modes name nameTwin names stops found1 found2 founds2)
      | Zero, Some kind => Parse.followsDone (List.all2Reverse found foundTwin founds)
      | Succ more, None => Parse.followsDone (List.all2Reverse found foundTwin founds)
      | Zero, None => Parse.followsDone (List.all2Reverse found foundTwin founds))

theorem followsCtorArgsOf ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (modes: Modes) (name nameTwin: Word)
    (names: WordsAlike name nameTwin)
    (stops: Tok → Bool) (braced: Bool):
    Parse.Follows SameCode PatternsAlike (() => ctorArgsOf pself modes name stops braced) (() =>
      ctorArgsOf pselfTwin modes nameTwin stops braced) :=
  match braced with
    | True => Parse.followsThen (followsFieldsPattern pknot modes) (fields fieldsTwin fieldses =>
      followsThenEq (followsPeek modes) (seen =>
        followsCtorFieldsEnd name nameTwin names fields fieldsTwin fieldses stops seen))
    | False => Parse.followsThen Parse.followsMark (here hereTwin marks =>
      rewrite <- marks.right.right then
        Parse.followsThen
          (followsCtorArgList pknot (here.left + 1) modes name nameTwin names stops [] [] Trivial)
          (listed listedTwin alike => followsCtorListEnd name nameTwin names listed listedTwin alike))

theorem followsCtorArgs ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (modes: Modes) (name nameTwin: Word)
    (names: WordsAlike name nameTwin) (stops: Tok → Bool):
    Parse.Follows SameCode PatternsAlike (() => ctorArgs pself modes name stops) (() =>
      ctorArgs pselfTwin modes nameTwin stops) :=
  byWalking [followsCtorArgsOf]

-- Patterns of one item, bracketed, tuples and lists.

theorem followsTupleItem ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin) (modes: Modes):
    Parse.Follows SameCode PatternsAlike (() => tupleItem pself modes) (() => tupleItem pselfTwin modes) :=
  byWalking [followsAlternatives]

theorem followsListItemPattern ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin) (modes: Modes):
    Parse.Follows SameCode PatternsAlike (() => listItemPattern pself modes) (() => listItemPattern pselfTwin modes) :=
  byWalking [followsAlternatives]

theorem followsCtorAhead ∀ (modes: Modes):
    Parse.Follows SameCode Same (() => ctorAhead modes) (() => ctorAhead modes) :=
  byWalking [followsWordAhead]

theorem followsQuotOrLower ∀ (modes: Modes) (quot: Bool):
    Parse.Follows SameCode WordsAlike (() => quotOrLower modes quot) (() => quotOrLower modes quot) :=
  byWalking [followsLower]

theorem followsNamedPattern ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin) (modes: Modes):
    Parse.Follows SameCode PatternsAlike (() => namedPattern pself modes) (() => namedPattern pselfTwin modes) :=
  Parse.followsThen followsBump (open openTwin opens =>
    Parse.followsThen (followsLower modes.inBrackets "a field name") (name nameTwin names =>
      Parse.followsThen followsBump (colonEq colonEqTwin colonEqs =>
        Parse.followsThen (pknot { modes = modes.inBrackets, level = PatternPlain }) (value valueTwin values =>
          Parse.followsMap
            (close => PatternNamed open name colonEq value close)
            (close => PatternNamed openTwin nameTwin colonEqTwin valueTwin close)
            (followsExpect modes.inBrackets RBracket "`]`")
            (close closeTwin closes =>
              alikePatternNamed open openTwin name nameTwin colonEq colonEqTwin opens names colonEqs value valueTwin
                  values close closeTwin closes)))))

theorem followsTuplePatternEnd ∀ (modes: Modes) (open openTwin: Word)
    (opens: WordsAlike open openTwin) (pair pairTwin: (List Pattern, Bool))
    (pairs: PairAlike (List.All2 PatternsAlike) Same pair pairTwin):
    Parse.Follows SameCode PatternsAlike (() => tuplePatternEnd modes open pair) (() =>
      tuplePatternEnd modes openTwin pairTwin) :=
  match pair, pairTwin with
    | (items, trailing), (twins, trailingTwin) =>
      Parse.followsMap
        (close => PatternTuple open items trailing close)
        (close => PatternTuple openTwin twins trailingTwin close)
        (followsExpect modes RParen "`)`")
        (close closeTwin closes =>
          rewrite <- pairs.right then
            alikePatternTuple open openTwin opens items twins pairs.left trailing close closeTwin closes)

theorem followsParenPatternOf ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (modes: Modes) (open openTwin: Word)
    (opens: WordsAlike open openTwin) (first firstTwin: Pattern)
    (firsts: PatternsAlike first firstTwin) (comma: Bool):
    Parse.Follows SameCode PatternsAlike (() => parenPatternOf pself modes open first comma) (() =>
      parenPatternOf pselfTwin modes openTwin firstTwin comma) :=
  match comma with
    | True => Parse.followsThen Parse.followsMark (here hereTwin marks =>
      rewrite <- marks.right.right then
        Parse.followsThen
          (followsCommaList modes
            (count => modes.at RParen && count >= 2)
            (count => modes.at RParen && count >= 2)
            (count => followsThenEq (followsAt modes RParen) (stop => Parse.followsDone byComputing))
            (() => tupleItem pself modes)
            (() => tupleItem pselfTwin modes)
            (followsTupleItem pknot modes)
            (here.left + 1)
            first
            firstTwin
            firsts
            []
            []
            Trivial)
          (pair pairTwin pairs => followsTuplePatternEnd modes open openTwin opens pair pairTwin pairs))
    | False =>
      Parse.followsMap
        (close => PatternParen open first close)
        (close => PatternParen openTwin firstTwin close)
        (followsExpect modes RParen "`)`")
        (close closeTwin closes => alikePatternParen open openTwin opens first firstTwin firsts close closeTwin closes)

-- List patterns.

def ListRead (read twin: (List Pattern, Bool, Option (Word, Pattern))): Prop :=
  PairAlike (List.All2 PatternsAlike) (PairAlike Same (Option.Alike (PairAlike WordsAlike PatternsAlike))) read twin

theorem followsListPatternClose ∀ (inner: Modes) (open openTwin: Word)
    (opens: WordsAlike open openTwin) (items twins: List Pattern)
    (alike: List.All2 PatternsAlike items twins)
    (trailing: Bool) (tail tailTwin: Option (Word, Pattern))
    (tails: Option.Alike (PairAlike WordsAlike PatternsAlike) tail tailTwin) (comma: Bool):
    Parse.Follows SameCode PatternsAlike (() => listPatternClose inner open items trailing tail comma) (() =>
      listPatternClose inner openTwin twins trailing tailTwin comma) :=
  match tail, tailTwin with
    | Some pair, Some pairTwin =>
      match comma with
        | True => followsFatalAny "a `..` tail must be the last item of a list pattern" (() =>
          Syntax.fatal "a `..` tail must be the last item of a list pattern")
        | False =>
          Parse.followsMap
            (close => PatternList open items trailing (Some pair) close)
            (close => PatternList openTwin twins trailing (Some pairTwin) close)
            (followsExpect inner RBracket "`]`: a `..` tail must be the last item")
            (close closeTwin closes =>
              alikePatternList open openTwin opens items twins alike trailing _ _ tails close closeTwin closes)
    | None, None =>
      Parse.followsMap
        [alike := PatternsAlike]
        [p := () => inner.expect RBracket "`,` or `]`"]
        [q := () => inner.expect RBracket "`,` or `]`"]
        (close => PatternList open items trailing None close)
        (close => PatternList openTwin twins trailing None close)
        (followsExpect inner RBracket "`,` or `]`")
        (close closeTwin closes =>
          alikePatternList open openTwin opens items twins alike trailing None None Trivial close closeTwin closes)

theorem followsListPatternEnd ∀ (inner: Modes) (open openTwin: Word)
    (opens: WordsAlike open openTwin) (read twin: (List Pattern, Bool, Option (Word, Pattern)))
    (reads: ListRead read twin):
    Parse.Follows SameCode PatternsAlike (() => listPatternEnd inner open read) (() =>
      listPatternEnd inner openTwin twin) :=
  match read, twin with
    | (items, trailing, tail), (twins, trailingTwin, tailTwin) =>
      rewrite <- reads.right.left then
        followsThenEq (followsAt inner Comma) (comma =>
          followsListPatternClose inner open openTwin opens items twins reads.left trailing tail tailTwin
              reads.right.right comma)

theorem followsListPatternNext ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern] (more: Nat)
    (modes: Modes) (found foundTwin: List Pattern)
    (founds: List.All2 PatternsAlike found foundTwin) (item twin: Pattern)
    (items: PatternsAlike item twin) (comma commaTwin: Option Word)
    (commas: Option.Alike WordsAlike comma commaTwin)
    (rest: ∀ (found foundTwin: List Pattern) => List.All2 PatternsAlike found foundTwin
      → Parse.Follows SameCode ListRead (() => listPatternItems more pself modes found) (() =>
        listPatternItems more pselfTwin modes foundTwin)):
    Parse.Follows SameCode ListRead (() => listPatternNext more pself modes found item comma) (() =>
      listPatternNext more pselfTwin modes foundTwin twin commaTwin) :=
  match comma, commaTwin with
    | Some word, Some wordTwin => rest [item, ..found] [twin, ..foundTwin] (Both items founds)
    | None, None =>
      Parse.followsDone (List.all2Reverse [item, ..found] [twin, ..foundTwin] (Both items founds), byComputing, Trivial)

theorem followsListPatternDots ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (more: Nat) (modes: Modes) (found foundTwin: List Pattern)
    (founds: List.All2 PatternsAlike found foundTwin) (dots: Bool)
    (rest: ∀ (found foundTwin: List Pattern) => List.All2 PatternsAlike found foundTwin
      → Parse.Follows SameCode ListRead (() => listPatternItems more pself modes found) (() =>
        listPatternItems more pselfTwin modes foundTwin)):
    Parse.Follows SameCode ListRead (() => listPatternDots more pself modes found dots) (() =>
      listPatternDots more pselfTwin modes foundTwin dots) :=
  match dots with
    | True => Parse.followsThen followsBump (dotsWord dotsTwin dotses =>
      Parse.followsMap
        (tail => (found.reverse, False, Some (dotsWord, tail)))
        (tail => (foundTwin.reverse, False, Some (dotsTwin, tail)))
        (pknot { modes, level = PatternPlain })
        (tail tailTwin tails => (List.all2Reverse found foundTwin founds, byComputing, (dotses, tails))))
    | False => Parse.followsThen (followsListItemPattern pknot modes) (entry entryTwin entries =>
      Parse.followsThen (followsEat modes Comma) (comma commaTwin commas =>
        followsListPatternNext more modes found foundTwin founds entry entryTwin entries comma commaTwin commas rest))

theorem followsListPatternStep ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (more: Nat) (modes: Modes) (found foundTwin: List Pattern)
    (founds: List.All2 PatternsAlike found foundTwin) (closed: Bool)
    (rest: ∀ (found foundTwin: List Pattern) => List.All2 PatternsAlike found foundTwin
      → Parse.Follows SameCode ListRead (() => listPatternItems more pself modes found) (() =>
        listPatternItems more pselfTwin modes foundTwin)):
    Parse.Follows SameCode ListRead (() => listPatternStep more pself modes found closed) (() =>
      listPatternStep more pselfTwin modes foundTwin closed) :=
  match closed with
    | True =>
      match found, foundTwin with
        | [], [] => Parse.followsDone (founds, byComputing, Trivial)
        | [entry, ..tail], [entryTwin, ..tailTwin] =>
          Parse.followsDone (List.all2Reverse found foundTwin founds, byComputing, Trivial)
    | False => followsThenEq (followsAt modes DotDot) (dots =>
      followsListPatternDots pknot more modes found foundTwin founds dots rest)

theorem followsListPatternItems ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (fuel: Nat) (modes: Modes) (found foundTwin: List Pattern)
    (founds: List.All2 PatternsAlike found foundTwin):
    Parse.Follows SameCode ListRead (() => listPatternItems fuel pself modes found) (() =>
      listPatternItems fuel pselfTwin modes foundTwin) :=
  match fuel with
    | Zero => Parse.followsDone (List.all2Reverse found foundTwin founds, byComputing, Trivial)
    | Succ more => followsThenEq (followsAt modes RBracket) (closed =>
      followsListPatternStep pknot more modes found foundTwin founds closed (found1 found2 founds2 =>
        followsListPatternItems pknot more modes found1 found2 founds2))

theorem followsListPattern ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin) (modes: Modes):
    Parse.Follows SameCode PatternsAlike (() => listPattern pself modes) (() => listPattern pselfTwin modes) :=
  Parse.followsThen followsBump (open openTwin opens =>
    Parse.followsThen Parse.followsMark (here hereTwin marks =>
      rewrite <- marks.right.right then
        Parse.followsThen
          (followsListPatternItems pknot (here.left + 1) modes.inBrackets [] [] Trivial)
          (read twin reads => followsListPatternEnd modes.inBrackets open openTwin opens read twin reads)))

-- Bracketed patterns.

theorem followsParenPatternEnd ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (modes: Modes) (open openTwin: Word)
    (opens: WordsAlike open openTwin) (first firstTwin: Pattern)
    (firsts: PatternsAlike first firstTwin):
    Parse.Follows SameCode PatternsAlike (() => parenPatternEnd pself modes open first) (() =>
      parenPatternEnd pselfTwin modes openTwin firstTwin) :=
  byWalking [followsParenPatternOf]

theorem followsParenMinusPattern ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin) (modes: Modes):
    Parse.Follows SameCode PatternsAlike (() => parenMinusPattern pself modes) (() =>
      parenMinusPattern pselfTwin modes) :=
  byWalking [followsTupleItem, followsParenPatternEnd]

theorem followsParenComponent ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (inner: Modes) (isCtor: Bool):
    Parse.Follows SameCode PatternsAlike (() => parenComponent pself inner isCtor) (() =>
      parenComponent pselfTwin inner isCtor) :=
  byWalking [followsCtorArgs]

theorem followsParenOpenPattern ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin) (modes: Modes):
    Parse.Follows SameCode PatternsAlike (() => parenOpenPattern pself modes) (() =>
      parenOpenPattern pselfTwin modes) :=
  Parse.followsThen followsBump (open openTwin opens =>
    Parse.followsThen
      (followsThenEq (followsCtorAhead modes.inBrackets) (isCtor =>
        followsParenComponent pknot modes.inBrackets isCtor))
      (component componentTwin components =>
        Parse.followsThen
          (followsPatternAppend pknot modes.inBrackets component componentTwin components PatternTupleComponent)
          (appended appendedTwin appendeds =>
            Parse.followsThen
              (followsAlternatives pknot modes.inBrackets appended appendedTwin appendeds PatternTupleComponent)
              (first firstTwin firsts =>
                followsParenPatternEnd pknot modes.inBrackets open openTwin opens first firstTwin firsts))))

theorem followsParenPattern ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (modes: Modes) (second: Option Tok):
    Parse.Follows SameCode PatternsAlike (() => parenPattern pself modes second) (() =>
      parenPattern pselfTwin modes second) :=
  match second with
    | Some RParen => Parse.followsThen followsBump (open openTwin opens =>
      Parse.followsMap
        (close => PatternAbsurd open close)
        (close => PatternAbsurd openTwin close)
        followsBump
        (close closeTwin closes => alikePatternAbsurd open openTwin close closeTwin opens closes))
    | Some Minus => followsParenMinusPattern pknot modes
    | _ => followsParenOpenPattern pknot modes

theorem followsBracketPatternOn ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (modes: Modes) (second third: Option Tok):
    Parse.Follows SameCode PatternsAlike (() => bracketPatternOn pself modes second third) (() =>
      bracketPatternOn pselfTwin modes second third) :=
  match second, third with
    | Some Lower, Some ColonEq => followsNamedPattern pknot modes
    | _, _ => followsListPattern pknot modes

theorem followsBracketPattern ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (modes: Modes) (second: Option Tok):
    Parse.Follows SameCode PatternsAlike (() => bracketPattern pself modes second) (() =>
      bracketPattern pselfTwin modes second) :=
  byWalking [followsBracketPatternOn]

theorem followsPlainWord ∀ (kind: Tok):
    Parse.Follows SameCode PatternsAlike (() => PatternWord kind bump()) (() => PatternWord kind bump()) :=
  Parse.followsMap
    (found => PatternWord kind found)
    (found => PatternWord kind found)
    followsBump
    (found foundTwin founds => alikePatternWord kind found foundTwin founds)

theorem followsPlainPatternOn ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (modes: Modes) (seen: Option Tok):
    Parse.Follows SameCode PatternsAlike (() => plainPatternOn pself modes seen) (() =>
      plainPatternOn pselfTwin modes seen) :=
  match seen with
    | Some Upper => followsPlainWord Upper
    | Some Lower => followsThenEq (followsWordAhead modes "Quot.mk") (quot =>
      Parse.followsMap
        (found => PatternWord Lower found)
        (found => PatternWord Lower found)
        (followsQuotOrLower modes quot)
        (found foundTwin founds => alikePatternWord Lower found foundTwin founds))
    | Some Underscore => followsPlainWord Underscore
    | Some Num => followsPlainWord Num
    | Some CharLit => followsPlainWord CharLit
    | Some Str => followsPlainWord Str
    | Some StrStart =>
      followsFatalAny "a text pattern can't interpolate" (() => Syntax.fatal "a text pattern can't interpolate")
    | Some LBrace =>
      Parse.followsMap
        (fields => PatternRecord fields)
        (fields => PatternRecord fields)
        (followsFieldsPattern pknot modes)
        (fields fieldsTwin fieldses => alikePatternRecord fields fieldsTwin fieldses)
    | Some LBracket => followsThenEq (followsPeekAt modes 1) (second => followsBracketPattern pknot modes second)
    | Some LParen => followsThenEq (followsPeekAt modes 1) (second => followsParenPattern pknot modes second)
    | _ => followsFailName modes "a pattern or `=`" (() => modes.failName "a pattern or `=`")

theorem followsPlainPattern ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin) (modes: Modes):
    Parse.Follows SameCode PatternsAlike (() => Syntax.plainPattern pself modes) (() =>
      Syntax.plainPattern pselfTwin modes) :=
  byWalking [followsPlainPatternOn]

-- Components of tuples, lists and alternatives, and the rule's knot.

theorem followsTupleSigned ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (modes: Modes) (minus: Bool):
    Parse.Follows SameCode PatternsAlike (() => tupleSigned pself modes minus) (() =>
      tupleSigned pselfTwin modes minus) :=
  byWalking [followsPlainPattern, followsPatternAppend, followsNegativePattern]

theorem followsTupleComponentOf ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (modes: Modes) (isCtor: Bool):
    Parse.Follows SameCode PatternsAlike (() => tupleComponentOf pself modes isCtor) (() =>
      tupleComponentOf pselfTwin modes isCtor) :=
  byWalking [followsCtorArgs, followsPatternAppend, followsTupleSigned]

theorem followsTupleComponent ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin) (modes: Modes):
    Parse.Follows SameCode PatternsAlike (() => tupleComponent pself modes) (() => tupleComponent pselfTwin modes) :=
  byWalking [followsCtorAhead, followsTupleComponentOf]

theorem followsListComponentOf ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (modes: Modes) (isCtor: Bool):
    Parse.Follows SameCode PatternsAlike (() => listComponentOf pself modes isCtor) (() =>
      listComponentOf pselfTwin modes isCtor) :=
  byWalking [followsCtorArgs, followsPatternAppend, followsTupleComponent]

theorem followsListComponent ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin) (modes: Modes):
    Parse.Follows SameCode PatternsAlike (() => listComponent pself modes) (() => listComponent pselfTwin modes) :=
  byWalking [followsCtorAhead, followsListComponentOf]

theorem followsAltPatternOneOf ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (modes: Modes) (isCtor: Bool):
    Parse.Follows SameCode PatternsAlike (() => altPatternOneOf pself modes isCtor) (() =>
      altPatternOneOf pselfTwin modes isCtor) :=
  byWalking [followsCtorArgs, followsPatternAppend, followsTupleComponent]

theorem followsAltPatternOne ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin) (modes: Modes):
    Parse.Follows SameCode PatternsAlike (() => altPatternOne pself modes) (() => altPatternOne pselfTwin modes) :=
  byWalking [followsCtorAhead, followsAltPatternOneOf]

theorem followsFieldValuePattern ∀ [pself pselfTwin: PatternGoal → {Parse Item} Pattern]
    (pknot: PatternSelfFollows pself pselfTwin)
    (modes: Modes) (isCtor: Bool):
    Parse.Follows SameCode PatternsAlike (() => fieldValuePattern pself modes isCtor) (() =>
      fieldValuePattern pselfTwin modes isCtor) :=
  byWalking [followsCtorArgs, followsPlainPattern]

theorem patternRuleFollows ∀ (pself pselfTwin: PatternGoal → {Parse Item} Pattern)
    (pknot: PatternSelfFollows pself pselfTwin):
    PatternSelfFollows (patternRule pself) (patternRule pselfTwin) :=
  goal =>
    match goal.level with
      | PatternPlain => followsPlainPattern pknot goal.modes
      | PatternTupleComponent => followsTupleComponent pknot goal.modes
      | PatternListComponent => followsListComponent pknot goal.modes
      | PatternAltOne => followsAltPatternOne pknot goal.modes
      | PatternFieldValue =>
        followsThenEq (followsCtorAhead goal.modes) (isCtor => followsFieldValuePattern pknot goal.modes isCtor)

theorem patternOfFollows: PatternOfFollows := modes => followsPattern patternRuleFollows { modes, level = PatternPlain }

theorem altPatternFollows: AltPatternFollows := modes =>
  Parse.followsThen (followsPattern patternRuleFollows { modes, level = PatternAltOne }) (first firstTwin firsts =>
    followsAlternatives (goal => followsPattern patternRuleFollows goal) modes first firstTwin firsts PatternAltOne)

-- The ladder's tiers, built from the facts proved above and the statement-level facts they need.

--| The ladder's tier 0, from the knot.
def atomFactsOf [self selfTwin: Goal → {Parse Item} Expr] (knot: SelfFollows self selfTwin): AtomFacts self selfTwin :=
  { knot = knot, atoms = atomFollows knot, braces = braceFollows knot }

--| The ladder's tier 1, from the knot and the `induct` and `reify` facts that `match` reads.
def matchFactsOf [self selfTwin: Goal → {Parse Item} Expr]
    (knot: SelfFollows self selfTwin)
    (inducts: InductFollows self selfTwin)
    (reifies: ReifyFollows self selfTwin):
    MatchFacts self selfTwin :=
  {
    below = atomFactsOf knot,
    matches = matchFollows knot altPatternFollows inducts reifies,
    clauses = clauseLambdaFollows knot altPatternFollows
  }

--| The ladder's tier 2, from tier 1 and the header's facts.
def lambdaFactsOf [self selfTwin: Goal → {Parse Item} Expr]
    (matched: MatchFacts self selfTwin)
    (header: HeaderFacts self selfTwin):
    LambdaFacts self selfTwin :=
  { below = matched, lambdas = lambdaFollows header patternOfFollows }

--| The ladder's tier 3.
def ifFactsOf [self selfTwin: Goal → {Parse Item} Expr] (lambdas: LambdaFacts self selfTwin): IfFacts self selfTwin :=
  { below = lambdas, ifs = ifFollows lambdas.below.below.knot }

--| The whole ladder's facts, from tier 3, the header's facts and the result-type fact.
def quantifierFactsOf [self selfTwin: Goal → {Parse Item} Expr]
    (ifs: IfFacts self selfTwin)
    (header: HeaderFacts self selfTwin)
    (results: ResultTypeFollows self selfTwin):
    QuantifierFacts self selfTwin :=
  { below = ifs, quantifiers = quantifierFollows header patternOfFollows, results = results }
