-- expect-error: E-HANDLER
ability Choose where
  choose : () -> {Choose} Bool

first : (() -> {Choose | e} a) -> {e} a
first prog =
  handle prog () with
    | choose u => k -> k True
