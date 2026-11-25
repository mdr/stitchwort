# SW-4786: where the proofless hash leaves out a proof

From the SW-4786 lane report (Opus, 25 Nov 2026). The lane fixed `J`'s proof in
`crates/core/src/hash.rs`: a cast into data now keeps its ends (the equation
annotating its proof), because rule K computes with them. The test is
`hash::a_proofless_hash_keeps_a_casts_ends` in `crates/core/tests/it/hash.rs`.
Before the fix, two casts whose ends differed shared the proofless hash
`#804fab0df76d`. The full hashes and the `hash_stability` snapshots, which
record only full hashes, did not change.

For every other place, the question is whether the kernel reads any
surrounding data that the hash drops. The lane's verdicts:

| Where | Verdict |
|---|---|
| `J`'s proof | Fixed. The one place where the kernel reads the proof's type (its ends) and nothing else in the hash fixes them. The motive and the base don't determine them. |
| An argument at a proof parameter of a definition | Safe. Its type comes from the function's type and the earlier arguments, which are hashed. |
| A data type's proof parameter, a constructor's proof field | Safe. Their types come from the data declaration and the earlier arguments. |
| `Quot.lift`'s fifth argument | Safe. Its type is fixed by arguments 0 to 3. |
| A whole proof term (a call of a theorem, `Quot.ind`, `Quot.sound`) | Safe. Its type is fixed by its context (an annotation, a `let`'s type, a parameter, a polymorphic type argument), which is all hashed. The only exception was `J`'s proof. |
| A definition whose result is a proof (hashed as its type alone), a stated theorem, the members of a recursive group that are proofs | Safe. Theorems are sealed. |
| A projection of a proof, a proof applied as a function | Safe. The result is a proof, and its type matters only to a consumer at one of the positions above. |
| Rule S (a match on a proof variable) | Not a place where a proof is left out. The variable's type comes from its binder, which is hashed. |
| A `J` into a proposition | Safe. Its result is a proof, which rule I treats as equal to any other of the same type, and that type is fixed by its context. |

The "safe" verdicts rest on one argument: a proof that is left out always has
its type fixed by hashed context. SW-4793, a Fable paper lane, reviews that
argument.
