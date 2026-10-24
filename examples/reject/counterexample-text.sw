-- expect-error: E-REFL
-- `Text` and `Char` inputs: small texts over a few characters first, then
-- random ones, with characters outside ASCII (counterexample search
-- stage 2).
import Std (List, Text, Char)

theorem reverseKeeps (t: Text): Text.fromList (List.reverse (Text.toList t)) = t := rfl

theorem asciiOnly (c: Char): Char.toNat c < 128 := rfl
