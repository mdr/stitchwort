-- An ability is a set of operations a function may perform; they appear in
-- its type between braces. Code using them is written in the ordinary
-- direct style.
ability Log where
  say: Text -> {Log} ()

def checkout (items: Nat): {Log} Nat :=
  say "checking out ${items} items"
  items * 5

-- A handler decides what the operations mean. Here, they collect the
-- messages in a list instead of printing them.
def collectLog (prog: () -> {Log | e} a): {e} (a, List Text) :=
  let run: List Text -> {e} (a, List Text) :=
    handle prog() with
      | return x     => acc => (x, acc)
      | say msg, k   => acc => k () (acc ++ [msg])
  run []

test "result" := (collectLog (() => checkout 3)).fst == 15
test "messages" := (collectLog (() => checkout 3)).snd == ["checking out 3 items"]
