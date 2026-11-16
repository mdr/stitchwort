theorem-- c
 same (t:
 () →
 {e} a): Unit :=
  match reify t with
    | return x => Trivial
