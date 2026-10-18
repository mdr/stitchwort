-- expect-error: E-HANDLER
ability Choose where
  choose : () -> {Choose} Bool

def first (prog : () -> {Choose | e} a) : {e} a :=
  handle prog () with
    | choose u, k => k True
