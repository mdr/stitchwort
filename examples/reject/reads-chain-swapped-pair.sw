-- expect-error: E-REFL
-- A last step that builds the pair the wrong way round is blamed at its
-- proof, not at the chain's first lemma (SW-3281), and the message shows the
-- spec the equation comes from, not an unknown (SW-3299).
import Std (Char, List, Parse)

def twoLetters(): {Parse Char} (Char, Char) :=
  let first := Parse.satisfy "a letter" Char.isAsciiLetter
  let second := Parse.satisfy "a letter" Char.isAsciiLetter
  (first, second)

def Written (read: List Char) (pair: (Char, Char)): Prop := read = [pair.fst, pair.snd]

theorem readsTwo: Parse.Reads twoLetters Written := Parse.readsThen Parse.readsSatisfy (firstRead first (Both firstIs
    letter1) =>
  Parse.readsThen Parse.readsSatisfy (secondRead second (Both secondIs letter2) =>
    Parse.readsDone (second, first) (rewrite firstIs, secondIs)))
