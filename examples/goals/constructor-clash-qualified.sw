-- Two types share the constructor `Str`, so a goal writes it with its type,
-- `Doc.Str t`, and the goal pastes back; `Line` is unique and stays short.
-- The counterexample's values are written the same way.
type Token = | Str (text: Text) | Name (text: Text)

type Doc = | Str (text: Text) | Line | Cat (a: Doc) (b: Doc)

def mk (t: Text): Doc := Doc.Str t

theorem mkIs ∀ (t: Text): mk t = Doc.Str t := ?
