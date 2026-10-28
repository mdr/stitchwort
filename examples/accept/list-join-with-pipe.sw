-- `List.joinWith` takes the list first, so it pipes and works with dot
-- notation; `Text.joinWith` is the same function.

import Std (List, Text)

def commaSeparated (values: List Nat): Text := values.map (value => "${value}") |> .joinWith ","

def spaced (words: List Text): Text := words.joinWith " "

def printed (values: List Nat): {IO} () := IO.print (values.map (value => "${value}") |> .joinWith ", ")

test "commaSeparated" := commaSeparated [4, 6, 3] == "4,6,3"

test "spaced" := spaced ["a", "b"] == Text.joinWith ["a", "b"] " "

test "empty" := commaSeparated [] == ""
