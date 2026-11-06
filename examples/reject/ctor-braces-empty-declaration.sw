-- expect-error: E-PARSE
-- A brace declaration lists fields; a constructor without any is `| C`.

type T = | C {}
