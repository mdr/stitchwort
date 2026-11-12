--| The parser reads exactly the puzzle's format: if `parseRules` reads
--| `input`, each line of it is its rule written out, as `Spec.RuleWritten`
--| says, word by word.

namespace Aoc.Year2020.Day07.Proofs
import Aoc.Year2020.Day07 (..)
import Aoc.Year2020.Day07.Spec (ColourWritten, ContentWritten, ContentsWritten, RuleWritten)
import Std (Fail, List, NonEmptyList, Parse, Result, Text, Void)

theorem readsColour: Parse.Reads colour ColourWritten :=
  Parse.readsThen Parse.readsTakeWhile1 (shadeRead shade (Both shadeNonEmpty (Both shadeLetters shadeIs)) =>
    Parse.readsThen (Parse.readsChar ' ') (spaceRead u space =>
      Parse.readsThen Parse.readsTakeWhile1 (hueRead hue (Both hueNonEmpty (Both hueLetters hueIs)) =>
        Parse.readsDone { shade, hue } _
          (rewrite shadeIs, hueIs, space, List.appendNil hueRead in
            Both rfl (Both (Both shadeNonEmpty shadeLetters) (Both hueNonEmpty hueLetters))))))

theorem readsContent: Parse.Reads content ContentWritten :=
  Parse.readsThen Parse.readsNat (digitsRead count (Both nonEmpty (Both digits value)) =>
    Parse.readsThen (Parse.readsChar ' ') (spaceRead u space =>
      Parse.readsThen readsColour (colourRead colour written =>
        Parse.readsThen (Parse.readsText (if count == 1 then " bag" else " bags")) (bagRead u bag =>
          Parse.readsDone { count, colour } _
            (Witness digitsRead (Witness colourRead
              (Both (rewrite List.appendNil bagRead, space, bag in rfl) (Both nonEmpty (Both digits (Both value written))))))))))

theorem readsContentList:
    Parse.Reads contentList (read contents => ∃ (listed: NonEmptyList Content) => Parse.SepBy ContentWritten (read u => read = ", ".toList) read listed ∧ contents = listed.toList) :=
  Parse.readsMap (() => Parse.sepBy1 content (() => Parse.text ", ")) NonEmptyList.toList _
    (Parse.readsSepBy1 content (() => Parse.text ", ") ContentWritten _ readsContent (Parse.readsText ", "))

theorem readsContents: Parse.Reads contents ContentsWritten :=
  Parse.readsOneOf ContentsWritten [() => Parse.before ([]: List Content) "no other bags", contentList]
    (Both (Parse.readsWeaken (Parse.readsBefore ([]: List Content) "no other bags") (read found (Both text same) => Inl (Both text same)))
      (Both (Parse.readsWeaken readsContentList (read found listed => Inr listed)) ()))

theorem readsRule: Parse.Reads rule RuleWritten :=
  Parse.readsThen readsColour (colourRead colour written =>
    Parse.readsThen (Parse.readsText " bags contain ") (containRead u contain =>
      Parse.readsThen readsContents (contentsRead contents listed =>
        Parse.readsThen (Parse.readsChar '.') (stopRead u stop =>
          Parse.readsDone { colour, contents } _
            (Witness colourRead (Witness contentsRead
              (Both (rewrite contain, stop in rfl) (Both written listed))))))))

--| If `parseRules` reads `input`, each of its lines is a rule written out.
theorem parseWritten (input: Text) (rules: Rules) (parsed: Fail.toResult (() => parseRules input) = Ok rules):
    List.All2 RuleWritten (input.lines.map Text.toList) rules.all :=
  let ran := rewrite Fail.toResultThen (() => Parse.eachLine input rule) (all => ({ all }: Rules)) at parsed in parsed
  match e: Fail.toResult (() => Parse.eachLine input rule) with
    | Ok all => rewrite <- Result.okInjective ran in Parse.eachLineReads input rule RuleWritten all e readsRule
