--| The converse of `Parse.sw`: passports written out as the batch file has
--| them are read as those passports.
--
-- From std's lemmas on what parsers do on good input (Std/Parse/Runs.sw).

namespace Aoc.Year2020.Day04.Proofs
import Aoc.Year2020.Day04 (..)
import Std (Bool, Char, DecEq, Eq, Exists, Fail, List, NonEmptyList, Parse, Result, Text, Void)

theorem fieldEta ∀ (f: Field): { key = f.key, value = f.value } = f := match f with | { key, value } => rfl

theorem runsAsValue ∀ (p: () → {Parse} a) (read rest: List Char) (v w: a)
    (same: v = w)
    (runs: Parse.Runs p read rest v):
    Parse.Runs p read rest w :=
  rewrite same at runs in runs

--| `pick` reads each key's three letters.
theorem runsKey ∀ (key: Key) (rest: List Char):
    Parse.Runs (() => Parse.pick (keys.map (key2 => (key2.code, key2)))) key.code.toList rest key :=
  match key with
    | BirthYear =>
      Parse.runsPick [] "byr" BirthYear
        [
          ("iyr", IssueYear),
          ("eyr", ExpirationYear),
          ("hgt", Height),
          ("hcl", HairColor),
          ("ecl", EyeColor),
          ("pid", PassportId),
          ("cid", CountryId)
        ]
        rest
        rfl
    | IssueYear =>
      Parse.runsPick
        [("byr", BirthYear)]
        "iyr"
        IssueYear
        [
          ("eyr", ExpirationYear),
          ("hgt", Height),
          ("hcl", HairColor),
          ("ecl", EyeColor),
          ("pid", PassportId),
          ("cid", CountryId)
        ]
        rest
        (Both rfl rfl)
    | ExpirationYear =>
      Parse.runsPick
        [("byr", BirthYear), ("iyr", IssueYear)]
        "eyr"
        ExpirationYear
        [("hgt", Height), ("hcl", HairColor), ("ecl", EyeColor), ("pid", PassportId), ("cid", CountryId)]
        rest
        (Both rfl (Both rfl rfl))
    | Height =>
      Parse.runsPick
        [("byr", BirthYear), ("iyr", IssueYear), ("eyr", ExpirationYear)]
        "hgt"
        Height
        [("hcl", HairColor), ("ecl", EyeColor), ("pid", PassportId), ("cid", CountryId)]
        rest
        (Both rfl (Both rfl (Both rfl rfl)))
    | HairColor =>
      Parse.runsPick
        [("byr", BirthYear), ("iyr", IssueYear), ("eyr", ExpirationYear), ("hgt", Height)]
        "hcl"
        HairColor
        [("ecl", EyeColor), ("pid", PassportId), ("cid", CountryId)]
        rest
        (Both rfl (Both rfl (Both rfl (Both rfl rfl))))
    | EyeColor =>
      Parse.runsPick
        [("byr", BirthYear), ("iyr", IssueYear), ("eyr", ExpirationYear), ("hgt", Height), ("hcl", HairColor)]
        "ecl"
        EyeColor
        [("pid", PassportId), ("cid", CountryId)]
        rest
        (Both rfl (Both rfl (Both rfl (Both rfl (Both rfl rfl)))))
    | PassportId =>
      Parse.runsPick
        [
          ("byr", BirthYear),
          ("iyr", IssueYear),
          ("eyr", ExpirationYear),
          ("hgt", Height),
          ("hcl", HairColor),
          ("ecl", EyeColor)
        ]
        "pid"
        PassportId
        [("cid", CountryId)]
        rest
        (Both rfl (Both rfl (Both rfl (Both rfl (Both rfl (Both rfl rfl))))))
    | CountryId =>
      Parse.runsPick
        [
          ("byr", BirthYear),
          ("iyr", IssueYear),
          ("eyr", ExpirationYear),
          ("hgt", Height),
          ("hcl", HairColor),
          ("ecl", EyeColor),
          ("pid", PassportId)
        ]
        "cid"
        CountryId
        []
        rest
        (Both rfl (Both rfl (Both rfl (Both rfl (Both rfl (Both rfl (Both rfl rfl)))))))

theorem runsFieldPieces ∀ (key: Key) (value: Text)
    (nonEmpty: value.toList ≠ [])
    (values: value.toList.all isValueChar = True) (rest: List Char)
    (stops: rest.takeWhile isValueChar = []):
    Parse.Runs field (key.code.toList ++ [':'] ++ value.toList) rest { key, value = Text.fromList value.toList } :=
  Parse.runsBind
    (() => Parse.pick (keys.map (key2 => (key2.code, key2)))) _
    key.code.toList
    ([':'] ++ value.toList) _
    rest
    key _
    rfl
    (runsKey key _)
    (Parse.runsBind
      (() => Parse.char ':') _
      [':']
      value.toList _
      rest
      () _
      rfl
      (Parse.runsChar ':' _)
      (Parse.runsBind
        (() => Parse.takeWhile1 "a value" isValueChar) _
        value.toList
        [] _
        rest
        (Text.fromList value.toList) _
        (Eq.sym (List.appendNil value.toList))
        (Parse.runsTakeWhile1 _ _ value.toList rest nonEmpty values stops)
        (Parse.runsPure _ rest)))

theorem runsField ∀ (read: List Char) (f: Field)
    (written: FieldWritten read f) (rest: List Char)
    (stops: Parse.CannotStart isValueChar rest):
    Parse.Runs field read rest f :=
  match written with
    | Both split (Both nonEmpty values) =>
      let sameField: ({ key = f.key, value = Text.fromList f.value.toList }: Field) = f :=
        rewrite Text.fromToList f.value in fieldEta f
      rewrite split in
        runsAsValue field _ rest _ f sameField
          (runsFieldPieces f.key f.value nonEmpty values rest (Parse.takeWhileOfCannotStart isValueChar rest stops))

theorem spaceNotValue ∀ (char: Char) (isSpace: Parse.isSpace char = True): isValueChar char = False :=
  match isSpace with
    | Inl space => rewrite space.read in rfl
    | Inr tab => rewrite tab.read in rfl

--| A key's first letter is a value character, so a word starting with it is absent where a space or line break is.
theorem wordAbsent ∀ (first: Char) (others: List Char) (char: Char) (more: List Char)
    (letter: isValueChar first = True)
    (stops: isValueChar char = False):
    Text.stripPrefixChars [first, ..others] [char, ..more] = None :=
  match same: Text.sameChar first char with
    | True =>
      Void.exfalso
        (Bool.trueNotFalse
          (Eq.trans
            (Eq.sym letter)
            (rewrite DecEq.sound (rewrite Text.sameCharEq first char at same in same) in stops)))
    | False => rfl

theorem declinesField ∀ (input: List Char) (stops: Parse.CannotStart isValueChar input): Parse.Declines field input :=
  Parse.declinesBind
    (() => Parse.pick (keys.map (key2 => (key2.code, key2)))) _
    input
    (Parse.declinesPick _ input
      (match input with
        | [] => Both rfl (Both rfl (Both rfl (Both rfl (Both rfl (Both rfl (Both rfl (Both rfl rfl)))))))
        | [char, ..more] =>
          let stop := stops char more rfl
          Both
            (wordAbsent 'b' ['y', 'r'] char more rfl stop)
            (Both
              (wordAbsent 'i' ['y', 'r'] char more rfl stop)
              (Both
                (wordAbsent 'e' ['y', 'r'] char more rfl stop)
                (Both
                  (wordAbsent 'h' ['g', 't'] char more rfl stop)
                  (Both
                    (wordAbsent 'h' ['c', 'l'] char more rfl stop)
                    (Both
                      (wordAbsent 'e' ['c', 'l'] char more rfl stop)
                      (Both
                        (wordAbsent 'p' ['i', 'd'] char more rfl stop)
                        (Both (wordAbsent 'c' ['i', 'd'] char more rfl stop) rfl)))))))))

theorem runsFieldBreak ∀ (read after: List Char) (written: FieldBreak read ()): Parse.Runs fieldBreak read after () :=
  match written with
    | Inl same =>
      rewrite same in
        Parse.runsOneOfFirst (() => Parse.char ' ') [Parse.newline] [' '] after () (Parse.runsChar ' ' after)
    | Inr isBreak =>
      Parse.runsOneOfNext
        (() => Parse.char ' ')
        Parse.newline
        []
        read
        after
        ()
        (match isBreak with
          | Inl same => rewrite same in Parse.declinesChar ' ' '\n' after rfl
          | Inr same => rewrite same in Parse.declinesChar ' ' '\r' ['\n', ..after] rfl)
        (Parse.runsNewline read after isBreak)

--| A round of a passport's fields declines after a line break, where no field starts.
theorem declinesStepAfterBreak ∀ (read after: List Char)
    (isBreak: Parse.LineBreak read)
    (stops: Parse.CannotStart isValueChar after):
    Parse.Declines (() => Parse.sepStep field fieldBreak) (read ++ after) :=
  Parse.declinesAfter fieldBreak
    (u => field())
    read
    after
    ()
    (runsFieldBreak read after (Inr isBreak))
    (declinesField after stops)

theorem declinesFieldBreak ∀ (input: List Char)
    (noSpace: Parse.Declines (() => Parse.char ' ') input)
    (noBreak: Parse.Declines Parse.newline input):
    Parse.Declines (() => Parse.sepStep field fieldBreak) input :=
  Parse.declinesSepStep field fieldBreak input
    (Parse.declinesOneOfTwo (() => Parse.char ' ') Parse.newline input noSpace noBreak)

--| A passport's fields end at line breaks only (the end of the input, or between passports).
theorem declinesStepAtBreaks ∀ (input: List Char)
    (only: Parse.OnlyBreaks input):
    Parse.Declines (() => Parse.sepStep field fieldBreak) input :=
  match input with
    | [] => declinesFieldBreak [] (Parse.declinesCharEnd ' ') (Parse.declinesNewline [] rfl rfl)
    | [char, ..more] =>
      let only1: Parse.OnlyBreaks more := only.right
      match Parse.lineBreakChar char only.left with
        | Inl same =>
          rewrite same in
            declinesStepAfterBreak ['\n'] more (Inl rfl) (Parse.cannotStartAtBreaks isValueChar rfl rfl more only1)
        | Inr same =>
          rewrite same in
            match more with
              | [] =>
                declinesFieldBreak ['\r'] (Parse.declinesChar ' ' '\r' [] rfl) (Parse.declinesNewline ['\r'] rfl rfl)
              | [next, ..later] =>
                let only2: Parse.OnlyBreaks later := only1.right
                match Parse.lineBreakChar next only1.left with
                  | Inl same2 =>
                    rewrite same2 in
                      declinesStepAfterBreak
                        ['\r', '\n']
                        later
                        (Inr rfl)
                        (Parse.cannotStartAtBreaks isValueChar rfl rfl later only2)
                  | Inr same2 =>
                    rewrite same2 in
                      declinesFieldBreak
                        ['\r', '\r', ..later]
                        (Parse.declinesChar ' ' '\r' ['\r', ..later] rfl)
                        (Parse.declinesNewline ['\r', '\r', ..later] rfl rfl)

--| ... or at a blank line.
theorem declinesStepAtBlank ∀ (blank more: List Char)
    (isBlank: Parse.BlankLine blank):
    Parse.Declines (() => Parse.sepStep field fieldBreak) (blank ++ more) :=
  match isBlank with
    | Witness first (Witness middle (Witness last (Both split (Both firstBreak (Both spaced lastBreak))))) =>
      let after := middle ++ (last ++ more)
      let afterCannot: Parse.CannotStart isValueChar after := match middle with
        | [] => Parse.cannotStartAfterBreak isValueChar rfl rfl last more lastBreak
        | [blank1, ..others] => char rest found =>
          rewrite <- List.consInjectiveHead _ _ _ _ found in spaceNotValue blank1 spaced.left
      rewrite split, List.appendAssoc first (middle ++ last) more, List.appendAssoc middle last more in
        declinesStepAfterBreak first after firstBreak afterCannot

theorem declinesStepAtLinesEnd ∀ (input: List Char)
    (end: Parse.LinesEnd input):
    Parse.Declines (() => Parse.sepStep field fieldBreak) input :=
  match end with
    | Inl only => declinesStepAtBreaks input only
    | Inr (Witness blank (Witness more (Both isBlank same))) => rewrite same in declinesStepAtBlank blank more isBlank

theorem runsPassport ∀ (read: List Char) (who: Passport)
    (written: PassportWritten read who) (rest: List Char)
    (end: Parse.LinesEnd rest):
    Parse.Runs passport read rest who :=
  match who with
    | { fields } =>
      match fields, written with
        | { head, tail }, written2 =>
          Parse.runsMap
            (() => Parse.sepBy1 field fieldBreak)
            (fields2 => { fields = fields2 })
            read
            rest
            (NonEmptyList.cons head tail)
            (Parse.runsSepBy1Of field fieldBreak FieldWritten FieldBreak
              (Parse.CannotStart isValueChar)
              rest
              (read2 v after ok stops => runsField read2 v ok after stops)
              (read2 after u written3 => runsFieldBreak read2 after written3)
              (read2 u written3 =>
                match written3 with
                  | Inl same => rewrite same in List.consNotNil ' ' []
                  | Inr isBreak => Parse.lineBreakNotEmpty read2 u isBreak)
              (read2 after u written3 =>
                match written3 with
                  | Inl same =>
                    rewrite same in (char more found => rewrite <- List.consInjectiveHead _ _ _ _ found in rfl)
                  | Inr isBreak => Parse.cannotStartAfterBreak isValueChar rfl rfl read2 after isBreak)
              (Parse.cannotStartAtLinesEnd isValueChar rfl rfl spaceNotValue rest end)
              (declinesStepAtLinesEnd rest end)
              read
              head
              tail
              written2)

theorem declinesPassport ∀ (rest: List Char)
    (stops: Parse.CannotStart isValueChar rest):
    Parse.Declines passport rest :=
  Parse.declinesBind
    (() => Parse.sepBy1 field fieldBreak) _
    rest
    (Parse.declinesSepBy1 field fieldBreak rest (declinesField rest stops))

theorem runsSections ∀ (read: List Char) (first: Passport) (others: List Passport)
    (written: Parse.SepBy PassportWritten (read2 u => Parse.BlankLine read2) read (NonEmptyList.cons first others))
    (ending: List Char)
    (breaks: Parse.OnlyBreaks ending):
    Parse.Runs (() => Parse.sections passport) read ending (NonEmptyList.cons first others) :=
  Parse.runsSectionsOf passport PassportWritten Parse.LinesEnd ending
    (read2 v after ok end => runsPassport read2 v ok after end)
    Parse.linesEndAfterBlank
    (Parse.linesEndAtBreaks ending breaks)
    (Parse.declinesSectionsAtBreaks passport isValueChar declinesPassport rfl rfl ending breaks)
    read
    first
    others
    written

--| The soundness theorem's conclusion: the input is passports written out, a
--| blank line between each two, then any line breaks.
def InputWritten (input: Text) (passports: List Passport): Prop :=
  ∃ (read: List Char) => ∃ (ending: List Char) => input.toList = read ++ ending
    ∧ (∃ (listed: NonEmptyList Passport) => Parse.SepBy PassportWritten (read2 u => Parse.BlankLine read2) read listed
      ∧ passports = listed.toList)
    ∧ ending.all (char => char == '\n' ∨ char == '\r') = True

--| Input that is passports written out is read as those passports.
theorem parseComplete ∀ (input: Text) (passports: List Passport)
    (written: InputWritten input passports):
    Fail.toResult (() => parsePassports input) = Ok passports :=
  match written with
    | Witness read (Witness ending (Both split (Both (Witness listed (Both listedWritten same)) breaks))) =>
      match listed, listedWritten, same with
        | { head, tail }, listedWritten2, same2 =>
          Parse.runsAll input
            (() => Parse.sections passport |> .toList)
            read
            ending
            passports
            split
            breaks
            (runsAsValue
              (() => Parse.sections passport |> .toList)
              read
              ending _
              passports
              (Eq.sym same2)
              (Parse.runsMap
                (() => Parse.sections passport)
                NonEmptyList.toList
                read
                ending
                (NonEmptyList.cons head tail)
                (runsSections read head tail listedWritten2 ending breaks)))

--| Soundness (`parseWritten`) is the converse: the input is written as at most one list of passports.
theorem writtenUnique ∀ (input: Text) (a b: List Passport)
    (writtenA: InputWritten input a)
    (writtenB: InputWritten input b):
    a = b :=
  Result.okInjective (Eq.trans (Eq.sym (parseComplete input a writtenA)) (parseComplete input b writtenB))
