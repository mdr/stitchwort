-- expect-error: E-TYPE-MISMATCH
-- A chain's first lemma about another parser than the goal's first step
-- is blamed at that lemma: the goal's parser starts with `Parse.nat ()`,
-- not the mark. Not at the whole `readsThen`, with `j` and `spec` left
-- unknown by the mistake (SW-3561's review, F2).
import Std (Char, Nat, Parse)

def two(): {Parse Char} Nat :=
  let a := Parse.nat()
  let b := Parse.nat()
  a + b

theorem wrongFirst: Parse.Reads two (taken v => True) :=
  Parse.readsThen Parse.readsMark (r x h => Parse.readsThen Parse.readsNat (r2 y h2 => Parse.readsDone (x + y) byComputing))
