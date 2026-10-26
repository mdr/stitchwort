-- A call of an effect-polymorphic library function (`find`, `map`, `filter`,
-- `foldLeft`) can start a pipe or dot chain that ends in a call performing
-- operations (`.orAbort`, `.orFail`): the call runs first, then the rest of
-- the chain on its result, as if it were bound by a `let`.
import Std.Abort (toOption)
import Std.Fail (toResult)
import Std (Abort, Fail, IO)

type Book = { title: Text, pages: Nat, borrowed: Bool }

def isLong (book: Book): Bool := book.pages > 300

def isAvailable (book: Book): Bool := !book.borrowed

def addPages (total: Nat) (book: Book): Nat := total + book.pages

-- Pipes ending in `.orAbort`.
def firstLongBook (shelf: List Book): {Abort} Book := shelf.find isLong |> .orAbort

def firstTitle (shelf: List Book): {Abort} Text := shelf.map (book => book.title) |> .head |> .orAbort

def firstAvailableTitle (shelf: List Book): {Abort} Text :=
  shelf.filter isAvailable |> .map (book => book.title) |> .head |> .orAbort

-- The same, as dot chains.
def firstLongBookDotted (shelf: List Book): {Abort} Book := (shelf.find isLong).orAbort

def firstTitleDotted (shelf: List Book): {Abort} Text := (shelf.map (book => book.title)).head.orAbort

-- The `let` form the chains stand for.
def firstLongBookByLet (shelf: List Book): {Abort} Book :=
  let found := shelf.find isLong
  found.orAbort

-- Inside a block, with a fold whose result is then checked.
def totalPagesOfLongBooks (shelf: List Book): {Abort} Nat :=
  let longBooks := shelf.filter isLong
  let firstLong := longBooks.find isLong |> .orAbort
  let total := longBooks.foldLeft 0 addPages
  firstLong.pages + total

-- `.orFail`, with a message.
def longBookOrFail (shelf: List Book): {Fail} Book := shelf.find isLong |> .orFail "no long book"

def availableTitleOrFail (shelf: List Book): {Fail} Text :=
  (shelf.filter isAvailable |> .map (book => book.title)).head.orFail "every book is out"

def biggestShelfOrFail (shelves: List (List Book)): {Fail} Nat :=
  shelves.map (shelf => shelf.foldLeft 0 addPages) |> .find (total => total > 0) |> .orFail "every shelf is empty"

-- A callback that performs operations: it runs for each book up to the one
-- found, before `.orAbort` looks at the result.
def firstLongBookLogged (shelf: List Book): {IO, Abort} Text :=
  shelf.find (book =>
    IO.print book.title
    isLong book)
      |> .orAbort
      |> .title

def novel: Book := { title = "Long Novel", pages = 420, borrowed = False }
def guide: Book := { title = "Short Guide", pages = 90, borrowed = True }
def atlas: Book := { title = "Atlas", pages = 310, borrowed = True }

def shelf: List Book := [guide, novel, atlas]

test "find, then orAbort" := toOption (() => firstLongBook shelf) == Some novel
test "nothing found" := toOption (() => firstLongBook [guide]) == None
test "map, head, then orAbort" := toOption (() => firstTitle shelf) == Some "Short Guide"
test "an empty shelf" := toOption (() => firstTitle []) == None
test "filter, map, head, then orAbort" := toOption (() => firstAvailableTitle shelf) == Some "Long Novel"
test "nothing available" := toOption (() => firstAvailableTitle [guide, atlas]) == None
test "as a dot chain" := toOption (() => firstLongBookDotted shelf) == Some novel
test "map then head as a dot chain" := toOption (() => firstTitleDotted shelf) == Some "Short Guide"
test "the same as the let form" :=
  toOption (() => firstLongBook shelf) == toOption (() => firstLongBookByLet shelf)
    ∧ toOption (() => firstLongBook [guide]) == toOption (() => firstLongBookByLet [guide])
test "in a block" := toOption (() => totalPagesOfLongBooks shelf) == Some 1150
test "in a block, nothing found" := toOption (() => totalPagesOfLongBooks [guide]) == None
test "find, then orFail" := toResult (() => longBookOrFail shelf) == Ok novel
test "orFail's message" := toResult (() => longBookOrFail [guide]) == Err "no long book"
test "filter and map, then orFail" := toResult (() => availableTitleOrFail [guide, atlas]) == Err "every book is out"
test "fold in a map, then orFail" := toResult (() => biggestShelfOrFail [[], [guide]]) == Ok 90
test "every shelf empty" := toResult (() => biggestShelfOrFail [[], []]) == Err "every shelf is empty"
test "callback runs first, in order" :=
  IO.simulate [] (() => toOption (() => firstLongBookLogged shelf)) == (["Short Guide", "Long Novel"], Some "Long Novel")
test "callback runs for every book when none is found" :=
  IO.simulate [] (() => toOption (() => firstLongBookLogged [guide])) == (["Short Guide"], None)
