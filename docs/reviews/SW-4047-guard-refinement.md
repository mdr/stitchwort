# SW-4047: SW-4024's four proof-tactic findings (lane report, Opus, 20 Nov 2026)

Items 2-4 did not reproduce in small files (variants in the lane report); item 1 still fails and is filed as SW-4375.

## Item 1 ticket text

Repro:

```
def weight (c: Char): Nat := if c == '(' then 1 else 2
theorem weightOpen ∀ (c: Char): 1 <= weight c := match c with
  | c if c == '(' => byComputing   -- E-REFL
  | c => byComputing
```

Cause: check_guard (crates/elab/src/lib.rs) checks the arm as a proof if (check_proof_if, Decidable.elimProof with a constant motive): binds cond = True without generalising the goal or hypotheses.

Suggested change: in a proof goal read `| p if c => a | rest` as `| p => match g: c with | True => a | False => <rest>`, reusing matching.rs generalisation (generalised_now, hypothesis copying, motive check) via an entry point taking arms as closures. About 4 existing proof arms use guards (GoodItemProofs.sw:395, pattern-guards.sw:144, pattern-guard-proofs.sw:26, catch-all-facts.sw:62); an arm rewriting with its guard equation may hit E-REWRITE-NOTHING. Theorem terms change for guarded proof arms; programs do not. Medium; proposal note first (user-visible proof semantics).
