-- An own-line comment between an expression `let`'s `:=` and its value
-- keeps its place, so the value starts at the block's column and the `;`
-- after it still belongs to the `let` (SW-4917).
def bracketed: Nat :=
  (let x :=
  -- c
  1; x)

def plain: Nat :=
  let x :=
  -- c
  1; x

-- A trailing comment after the `:=` stays on its line too.
def trailing: Nat :=
  (let x := -- c
  1; x)
