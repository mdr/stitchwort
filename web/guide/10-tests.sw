-- A test is a named `Bool` expression that must be `True`. Run them from
-- the Tests tab. Each result is remembered until something it depends on
-- changes.
def isLeap (year: Nat): Bool :=
  (year % 4 == 0 && year % 100 != 0) || year % 400 == 0

test "2024 is a leap year" := isLeap 2024
test "1900 is not" := !(isLeap 1900)
test "2000 is" := isLeap 2000
-- A comparison shows both sides when it fails. Change 2023 to 2024 to
-- see this one pass.
test "2023 is wrong on purpose" := isLeap 2023 == True
