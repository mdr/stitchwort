--| The converse of `Parse.sw`: every line written out as a rule is read as that
--| rule, and so is a whole input of such lines.
--
-- From std's lemmas on what parsers do on good input (Std/Parse/Runs.sw).

namespace Aoc.Year2020.Day07.Proofs
import Aoc.Year2020.Day07 (..)
import Aoc.Year2020.Day07.Spec (ColourWritten, ContentWritten, ContentsWritten, RuleWritten, Word)
import Std (Bool, Char, DecEq, Eq, Exists, Fail, List, NonEmptyList, Parse, Result, Text, Void)

theorem runsAsValue ∀ (p: () → {Parse} a) (read rest: List Char) (v w: a)
    (same: v = w)
    (runs: Parse.Runs p read rest v):
    Parse.Runs p read rest w :=
  rewrite same at runs in runs

theorem colourEta ∀ (colour: Colour): { shade = colour.shade, hue = colour.hue } = colour := match colour with
  | { shade, hue } => rfl

theorem ruleEta ∀ (rule: Rule): { colour = rule.colour, contents = rule.contents } = rule := match rule with
  | { colour, contents } => rfl

theorem contentEta ∀ (content: Content): { count = content.count, colour = content.colour } = content :=
  match content with | { count, colour } => rfl

--| A word of a colour, as long as what follows isn't a letter.
theorem runsWord ∀ (text: Text)
    (isWord: Word text) (rest: List Char)
    (stops: rest.takeWhile Char.isAsciiLowercase = []):
    Parse.Runs word text.toList rest text :=
  match isWord with
    | Both nonEmpty letters =>
      let runs :=
        Parse.runsTakeWhile1 "a colour, 'a' to 'z'" Char.isAsciiLowercase text.toList rest nonEmpty letters stops
      rewrite Text.fromToList text at runs in runs

theorem runsColour ∀ (read: List Char) (colourIs: Colour)
    (written: ColourWritten read colourIs) (rest: List Char)
    (stops: rest.takeWhile Char.isAsciiLowercase = []):
    Parse.Runs colour read rest colourIs :=
  match written with
    | Both split (Both shadeWord hueWord) =>
      rewrite split in
        runsAsValue colour _ rest _ colourIs
          (colourEta colourIs)
          (Parse.runsBind word _ colourIs.shade.toList
            ([' ', ..colourIs.hue.toList]) _
            rest
            colourIs.shade _
            rfl
            (runsWord colourIs.shade shadeWord _ rfl)
            (Parse.runsBind
              (() => Parse.char ' ') _
              [' ']
              colourIs.hue.toList _
              rest
              () _
              rfl
              (Parse.runsChar ' ' _)
              (Parse.runsBind word _ colourIs.hue.toList [] _ rest colourIs.hue _
                (Eq.sym (List.appendNil _))
                (runsWord colourIs.hue hueWord rest stops)
                (Parse.runsPure _ rest))))

theorem bagStops ∀ (count: Nat) (rest: List Char):
    ((if count == 1 then " bag" else " bags").toList ++ rest).takeWhile Char.isAsciiLowercase = [] :=
  match count == 1 with
    | True => rfl
    | False => rfl

theorem runsContent ∀ (read: List Char) (item: Content)
    (written: ContentWritten read item) (rest: List Char):
    Parse.Runs content read rest item :=
  match written with
    | Witness digits (Witness colourRead (Both split (Both nonEmpty (Both digitsAll (Both countIs colourWritten))))) =>
      let sameItem: ({ count = Parse.digitsValue digits, colour = item.colour }: Content) = item :=
        rewrite <- countIs in contentEta item
      let split2 := rewrite countIs at split in split
      rewrite split2 in
        runsAsValue content _ rest _ item sameItem
          (Parse.runsBind Parse.nat _ digits
            ([' ', ..colourRead] ++ (if Parse.digitsValue digits == 1 then " bag" else " bags").toList) _
            rest
            (Parse.digitsValue digits) _
            rfl
            (Parse.runsNat digits _ nonEmpty digitsAll rfl)
            (Parse.runsBind
              (() => Parse.char ' ') _
              [' ']
              (colourRead ++ (if Parse.digitsValue digits == 1 then " bag" else " bags").toList) _
              rest
              () _
              rfl
              (Parse.runsChar ' ' _)
              (Parse.runsBind colour _ colourRead
                (if Parse.digitsValue digits == 1 then " bag" else " bags").toList _
                rest
                item.colour _
                rfl
                (runsColour colourRead item.colour colourWritten _ (bagStops (Parse.digitsValue digits) rest))
                (Parse.runsBind
                  (() => Parse.text (if Parse.digitsValue digits == 1 then " bag" else " bags")) _
                  (if Parse.digitsValue digits == 1 then " bag" else " bags").toList
                  [] _
                  rest
                  () _
                  (Eq.sym (List.appendNil _))
                  (Parse.runsText _ rest)
                  (Parse.runsPure _ rest)))))

theorem runsContentList ∀ (read: List Char) (items: List Content) (listed: NonEmptyList Content)
    (written: Parse.SepBy ContentWritten (read2 u => read2 = ", ".toList) read listed)
    (same: items = listed.toList) (more: List Char):
    Parse.Runs contentList read ['.', ..more] items :=
  match listed, written, same with
    | { head, tail }, written2, same2 =>
      runsAsValue contentList read
        ['.', ..more] _
        items
        (Eq.sym same2)
        (Parse.runsMap
          (() => Parse.sepBy1 content (() => Parse.text ", "))
          NonEmptyList.toList
          read
          ['.', ..more]
          (NonEmptyList.cons head tail)
          (Parse.runsSepBy1Of content
            (() => Parse.text ", ")
            ContentWritten
            (read2 u => read2 = ", ".toList)
            (read2 => True = True)
            ['.', ..more]
            (read2 v after ok end => runsContent read2 v ok after)
            (read2 after u isSeparator => rewrite isSeparator in Parse.runsText ", " after)
            (read2 u isSeparator => rewrite isSeparator in List.consNotNil ',' [' '])
            (read2 after u isSeparator => rfl)
            rfl
            (Parse.declinesSepStep content
              (() => Parse.text ", ")
              ['.', ..more]
              (Parse.declinesText ", " ['.', ..more] rfl))
            read
            head
            tail
            written2))

--| A list of contents starts with a digit.
theorem listStartsWithDigit ∀ (read: List Char) (head: Content) (tail: List Content) (sepSpec: List Char → () → Prop)
    (written: Parse.SepBy ContentWritten sepSpec read (NonEmptyList.cons head tail)):
    ∃ (digit: Char) => ∃ (more: List Char) => read = [digit, ..more] ∧ Parse.isDigit digit = True :=
  match written with
    | Witness firstRead (Witness nextRead (Witness firstValue (Both split (Both firstWritten later)))) =>
      match firstWritten with
        | Witness digits (Witness colourRead (Both split2 (Both nonEmpty (Both digitsAll values)))) =>
          match digits, nonEmpty, digitsAll with
            | [], nonEmpty2, digitsAll2 => Void.exfalso (nonEmpty2 rfl)
            | [digit, ..more], nonEmpty2, digitsAll2 =>
              Witness digit
                (Witness
                  ((more ++ ([' ', ..colourRead] ++ (if firstValue.count == 1 then " bag" else " bags").toList))
                    ++ nextRead)
                  (Both (rewrite split, split2 in rfl) digitsAll2.left))

--| "no other bags" doesn't start with a digit.
theorem noOtherAbsent ∀ (digit: Char) (more: List Char)
    (isDigit: Parse.isDigit digit = True):
    Text.stripPrefixChars "no other bags".toList [digit, ..more] = None :=
  match same: Text.sameChar 'n' digit with
    | True => cases
    | False => rfl

theorem runsContents ∀ (read: List Char) (items: List Content)
    (written: ContentsWritten read items) (more: List Char):
    Parse.Runs contents read ['.', ..more] items :=
  match written with
    | Inl (Both noOther same) =>
      rewrite noOther, same in
        Parse.runsOneOfFirst
          (() => Parse.before ([]: List Content) "no other bags")
          [contentList]
          "no other bags".toList
          ['.', ..more]
          []
          (Parse.runsBind
            (() => Parse.text "no other bags")
            (u => ([]: List Content))
            "no other bags".toList
            []
            "no other bags".toList
            ['.', ..more]
            ()
            []
            (Eq.sym (List.appendNil _))
            (Parse.runsText "no other bags" _)
            (Parse.runsPure _ _))
    | Inr (Witness listed (Both listedWritten same)) =>
      match listed, listedWritten with
        | { head, tail }, listedWritten2 =>
          match listStartsWithDigit read head tail _ listedWritten2 with
            | Witness digit (Witness more2 (Both startsWith isDigit)) =>
              Parse.runsOneOfNext
                (() => Parse.before ([]: List Content) "no other bags")
                contentList
                []
                read
                ['.', ..more]
                items
                (Parse.declinesBind
                  (() => Parse.text "no other bags")
                  (u => ([]: List Content))
                  (read ++ ['.', ..more])
                  (Parse.declinesText "no other bags" _
                    (rewrite startsWith in noOtherAbsent digit (more2 ++ ['.', ..more]) isDigit)))
                (runsContentList read items (NonEmptyList.cons head tail) listedWritten2 same more)

theorem runsRule ∀ (read: List Char) (item: Rule) (written: RuleWritten read item): Parse.Runs rule read [] item :=
  match written with
    | Witness colourRead (Witness contentsRead (Both split (Both colourWritten contentsWritten))) =>
      rewrite split in
        runsAsValue rule _ [] _ item
          (ruleEta item)
          (Parse.runsBind colour _ colourRead
            (" bags contain ".toList ++ contentsRead ++ ['.']) _
            []
            item.colour _
            rfl
            (runsColour colourRead item.colour colourWritten _ rfl)
            (Parse.runsBind
              (() => Parse.text " bags contain ") _
              " bags contain ".toList
              (contentsRead ++ ['.']) _
              []
              () _
              rfl
              (Parse.runsText " bags contain " _)
              (Parse.runsBind contents _ contentsRead
                ['.'] _
                []
                item.contents _
                rfl
                (runsContents contentsRead item.contents contentsWritten [])
                (Parse.runsBind
                  (() => Parse.char '.') _
                  ['.']
                  [] _
                  []
                  () _
                  (Eq.sym (List.appendNil _))
                  (Parse.runsChar '.' _)
                  (Parse.runsPure _ [])))))

theorem rulesEta ∀ (rules: Rules): ({ all = rules.all }: Rules) = rules := match rules with | { all } => rfl

--| Input whose lines are rules written out is read as those rules.
theorem parseComplete ∀ (input: Text) (rules: Rules)
    (written: List.All2 RuleWritten (input.lines.map Text.toList) rules.all):
    Fail.toResult (() => parseRules input) = Ok rules :=
  let lines: Fail.toResult (() => Parse.eachLine input rule) = Ok rules.all :=
    Parse.runsEachLine input rule rules.all (List.all2Weaken runsRule _ _ written)
  rewrite Fail.toResultThen (() => Parse.eachLine input rule) (all => ({ all }: Rules)), lines, rulesEta rules in rfl

--| A line is written as at most one rule, because the parser reads it as one.
theorem writtenUnique ∀ (chars: List Char) (a b: Rule)
    (writtenA: RuleWritten chars a)
    (writtenB: RuleWritten chars b):
    a = b :=
  Result.okInjective
    (Eq.trans
      (Eq.sym (Parse.runsRun rule chars a (runsRule chars a writtenA)))
      (Parse.runsRun rule chars b (runsRule chars b writtenB)))

--| ... and an input is written as at most one set of rules.
theorem inputUnique ∀ (input: Text) (a b: Rules)
    (writtenA: List.All2 RuleWritten (input.lines.map Text.toList) a.all)
    (writtenB: List.All2 RuleWritten (input.lines.map Text.toList) b.all):
    a = b :=
  Result.okInjective (Eq.trans (Eq.sym (parseComplete input a writtenA)) (parseComplete input b writtenB))
