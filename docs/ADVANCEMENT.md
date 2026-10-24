# Execution plan after the Verdi/Jepsen review

This supplements PLAN.md and issues #2–#4; it does not renumber R00–R17.
Implementation progress and mathematical discharge are separate.

| Order | Existing wave | Concrete artifact / exit | Current state |
| --- | --- | --- | --- |
| 1 | R00 | Reproduce pinned 43.1 + PR #117 foundation and inspect hosted CI separately | 167 baseline checks reproduced locally; published kernel guard retained |
| 2 | R01 | Exact root/subject/dependency/assumption/judgment binding with hostile substitutions | Implemented for existing Boolean/propositional domains; generic obligations open |
| 3 | R01 / issue #3 | Inert bounded artifact decoding with independent byte vectors and truncation corpus | VOR-DATA/0 byte-list codec implemented; no stream service or Rust peer |
| 4 | R02 | Fixed first-order logic, scoped equality/substitution, root inventory and rule corpus | Implemented 20-rule kernel, reserved tree induction, typed claims, hostile corpus and independent finite/Kripke checks; metatheory open |
| 5 | R03–R05 | Admitted Shen subset, evaluator adequacy, induction, exact arithmetic, generic construction contracts | Open; do not replace with checked examples |
| 6 | R06–R10 / #2 | Generic transfer, preservation and effects; dedup transformer with explicit no-crash boundary | Open; recovery and external effects need separate theorems |
| 7 | R13 / #3–#4 | Versioned independent checker process, concurrent observation map, real service faults/reduction | Open; local byte decoding is not this integration |
| 8 | R14–R17 | Concrete simulation, deployment preservation, acceptance-kernel proofs, fresh-image release | Open |

The claim layer deliberately rejects unsupported proof kinds. It can bind a
finite-model certificate or concrete propositional derivation today without
pretending to admit unrestricted Shen source. The codec's small explicit wire
domain avoids silent numeric coercions while the future protocol is specified.
See CLAIMS.md for exact grammar, APIs, assumptions, and limits.

The first assumption corpus targets today's boundary: malformed artifacts,
substituted evidence, reader/evaluator injection attempts, budget exhaustion,
and intermediate invariant failures. Storage/retry/client fault campaigns will
be added once their modeled outcomes and adapters exist; no current VOR/0
acceptance is extended to those domains.

R01 is not complete merely because its executable schema exists. Identity and
assumption-composition proofs await the R02–R05/R16 facilities. All 54 original
roadmap goals and three added R01 codec/correspondence goals remain mathematically
open (57 total). The registry records requirements, not completed proofs.


R02's concrete artifacts and executable exit corpus are now available. Its
trusted-root interpretation and generic soundness/termination proofs remain
explicit in LOGIC-METATHEORY.md. The next implementation dependency is R03:
closed admitted Shen syntax, ordered clause/evaluation semantics, and a reference
evaluator. First-order derivations can express quantified logical theorems;
application correctness still needs that execution meaning and R04/R05 proofs.


R03 now has closed reader-level source normalization, explicit pure small-step
semantics, reference execution, indexed ground evaluation evidence, exact claim
binding, and a process-service regression. Its finite native agreement and
witness checks do not complete the generic preservation/adequacy theorems.
Next are R04's admitted inductive data/exact arithmetic principles and the
R05 contracts/termination machinery needed to prove constructors for all inputs.
