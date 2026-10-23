# Execution plan

Correctness gates precede expansion. Work estimates do not select the design.

## Implemented foundation

- Closed Boolean transition semantics with strict data validation.
- Independent finite-closure certificate checking and bounded BFS production.
- Exact trace conformance and partial-observation belief updates.
- Explicit propositional proofs and indexed System S evidence judgments.
- Pinned Chez-based Shen-Scheme host with kernel PR #117.
- Hostile cases and an independent finite-state oracle.

## Next: establish the core's mathematics

Write the denotational and operational rules in full, prove validation and
evaluation lemmas, then transition adequacy and finite-certificate soundness.
Choose a proof-checking route deliberately; do not label tests as formal
soundness. Keep proof search outside acceptance. Validate the implementation
against the formal definitions, not just a second copy of itself.

## Richer state and explicit outcomes

Add algebraic data and exact integers with explicit semantics. Add result
forms for normal return, error, emitted effect request, pending observation,
and resource exhaustion. Divergence needs a semantic relation; a timeout is
not proof of divergence. Preserve the Boolean conformance corpus unchanged.

## Inductive reasoning beyond finite closure

Add explicit substitution, binders, quantification, algebraic induction, and
checked invariant-preservation obligations. Prove capture avoidance and rule
soundness. Integrate solver/prover search only through checked evidence; reject
unknown and unsupported proof steps.

## ShenLogic integration

Define the exact semantic projection and its adequacy obligations. Bind
source and theory identities to theorem statements. Require independent proof
checking for any claim promoted into the acceptance kernel.

## ShenCheck integration

Start with a versioned trace adapter using the shared transition model. Add
uncertain effects and retries only after their outcomes are modeled. Reuse
fault execution, replay, shrinking, and provenance without inheriting their
status labels as proof. Establish adapter conformance before asserting it.

## Implementation refinement

Define concrete-to-abstract state relations, initial-state correspondence,
step simulation including stuttering, and environment assumptions. Prove these
for each supported adapter/implementation. Add liveness separately with stated
fairness and progress assumptions. Binary verification is a later, distinct
trust-boundary project.
