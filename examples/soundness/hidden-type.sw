-- expect-error: E-PROP-ELIM
-- A type hidden inside a proof can't be extracted: the field is a type, not a
-- proof, so this proposition can't be matched on to produce data.
type HiddenType: Prop =
  | HideType (a: Type)

def reveal: HiddenType -> Type
  | HideType a => a
