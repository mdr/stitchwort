-- expect-error: E-REFL
-- `match e: expr` replaces `expr` where the goal shows it, as written or
-- computed. `Token.extra t` is stuck on `t`, and `note` exists only inside
-- its body, so the scrutinee `t.note` never appears in the goal and
-- `byComputing` fails; the note says what reaches it (SW-3678). A `match` on
-- `t` (a record pattern) gets there: `| Word _ note => match note with …`.
import Std (Nat, Option)

type Token = | Word (text: Nat) (note: Option Nat)

def Token.extra: Token -> Nat
  | Word _ note =>
    match note with
      | Some n => n
      | None => 0

theorem extraOfNone ∀ (t: Token) (none: t.note = None): Token.extra t = 0 := match t.note with
  | None => byComputing
  | Some _ => byComputing
