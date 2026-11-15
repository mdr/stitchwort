namespace Both

import Lexer (..)
import Printer (..)

-- A file that imports both types sees `Str` twice. Only code that really
-- uses both should import both; this one names a type's constructor.
test "str" := Str "a" == Str "a"
