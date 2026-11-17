-- A theorem whose hypothesis and the lemma's `auto` argument both name the
-- helper (`holds`), so the search finds the hypothesis. The helper holds the
-- match, out of the theorem's scope (docs/proving-guide.md, "A statement that
-- spells out a match").

type Choice = | A | B

def holds (t: Choice): Prop := match t with
  | A => 1 = 1
  | B => 2 = 2

def needs (t: Choice) [auto h: holds t]: Nat := 1

theorem viaHelper ∀ (t: Choice) (h: holds t): needs t = 1 := byComputing
