-- expect-error: E-UNKNOWN-NAME
-- `T.f.update.g` names a generated lemma; one that doesn't exist is an
-- unknown name, with the lemmas there are, not dot notation on `T.f`.

type Event =
  | Meeting (title: Text) (startTime: Nat)
  | Call (title: Text) (startTime: Nat) (number: Text)

def Event.ends (event: Event): Nat := event.startTime + 1

theorem moved (event: Event): ({ event | startTime = 1 }).startTime = 1 :=
  rewrite Event.startTime.update.ends in rfl
