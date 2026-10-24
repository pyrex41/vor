# R03 preservation and adequacy obligations

The following universal claims remain open. The executable checks and finite
native comparisons below are evidence; they do not discharge these theorems.
They correspond to PLAN.md R03, R04/R05 admission, and R16 acceptance proofs.

## Normalization preservation

For the exact versioned admitted source grammar:

1. Accepted headers uniquely resolve every saturated call and fix every arity.
2. Ordered clause parsing preserves clause order, body/guard boundaries, and
   the declared pattern arity. No unsupported form receives an implicit meaning.
3. Pattern indexing preserves first binding, repeated-variable equality, cons
   structure, wildcard independence, and left-to-right binding order.
4. Expression indexing preserves lexical references and shadowing. A let value
   cannot see its new binding; a let body sees it at index zero.
5. Every accepted normalized program is closed and formed. Every indexed local
   used after a successful match has a corresponding value.
6. Normalized evaluation agrees with the specified reader-level Shen subset,
   including strict argument order, lazy if branches, guard errors/fallthrough,
   no-match outcomes, and the declared primitive error abstraction.
7. A checked normalization certificate binds the source and normalized program
   whose behavior the theorem concerns. Hash labels alone cannot provide this.

There is no generic native compiler theorem in this PR. Native execution in an
ambient mutable image, macro expansion, redefinition, code generation, and
optimized replacements need their own preservation arguments. This admission
subset rejects unsupported constructs instead of reusing the entire host
compiler as an unexplained semantic oracle.

## Evaluation formation, determinism, and adequacy

Let `P |- State -> Next` denote the fixed small-step relation.

- Initial formation: a valid closed program and valid call yield a formed
  initial machine with correctly sized arguments.
- Step preservation: every successor of a formed nonterminal state is formed,
  or is one of the explicitly modeled terminal errors. Closure/arity/slot
  formation must establish which internal errors are unreachable.
- Determinism: a formed nonterminal state has exactly one next state. Terminal
  states do not step. Ordered matching and guard evaluation cannot skip a
  higher-priority enabled clause or evaluate a lower-priority body.
- Producer adequacy: a returned evaluated witness is a legal finite path from
  the exact initial call to the recorded outcome; resource exhaustion does not
  establish a terminal outcome.
- Acceptance soundness: a checked witness is such a path, with no substituted
  code, inputs, endpoints, or missing edge.
- Evaluator/witness correspondence: the runner and acceptance walk implement
  that relation. Sharing executable step rules removes a second algorithm,
  but does not independently prove those rules implement the intended semantics.
- Public judgment correspondence: normalization, evaluation claims, and indexed
  System S judgments imply exactly the documented concrete claims, under the
  named root/host assumptions.

Recursive evaluation remains a relation with finite path evidence. A fuel limit
bounds visits, not the amount of work in matching, source validation, primitive
structural equality, or allocation. Total correctness of arbitrary admitted
recursive definitions is not claimed. R04/R05 must add well-founded measures,
coverage, contracts, and generic derivations before accepting those claims.

## Trusted root and remaining runtime assumptions

The new trusted source includes spec/program.shen, spec/evaluation.shen, and
runtime/reference.shen. Source normalization, finite-data predicates, lexical
indexing, pattern matching, primitive dispatch, machine stepping, and literal
proof decoding all need the generic contracts above.

Selected value operations use trusted host implementations, including cons,
head/tail, structural equality, number/string/symbol predicates, and the numeric
operations used for indices/fuel. Their binding/ABI/compilation preservation is
not proved here. The configured shared Shen-Scheme/Chez runtime, Shen kernel,
compiler, and stable checker image remain assumptions. Frozen program function
resolution is not complete runtime dependency closure or protection against
concurrent rebinding of trusted checker/primitive definitions. Buri/native host
qualification and R15 remain distinct work.

The checked program cannot invoke arbitrary effects, host functions, globals,
loading, evaluation, mutation, or user-supplied proof rules. It can still consume
resources. Library validation and semantic fuel are not a secure host sandbox.
The process service's independent deadlines/limits do not prove semantic or
compiler correctness.

## Native differential evidence

The test-only oracle evaluates a bounded fixture-generated grammar through
native eval-kl and compares its value/error abstraction with reference execution.
No untrusted artifact can reach that oracle, and no acceptance module invokes
it. It covers literals, primitive applications, conditional combinations, and
lexical bindings. Compiled native Shen fixture functions additionally check
ordered patterns, repeated variables, guards, and protected symbols.

This is a finite differential corpus, not a compiler proof or a second
production application implementation. Both paths share host value primitives,
so agreement does not independently validate those primitive implementations.
The native oracle and the reference evaluator do have different control/binding
execution paths, making this useful backpressure on normalization and stepping.

Witness-mutation, source-tampering, closed-resolution, and process-service tests
exercise the independent producer/acceptance boundary. Subsequent stages must
retain these while adding actual generic preservation and contract proofs.


## Optional runtime and translation proofs

The audit now proves soundness/completeness of the deterministic finite path
checker model, runner-receipt acceptance and unique terminal outcomes. It also
proves big-step/CEK adequacy for R05 expression control, with a fixed pure callee
interface, and compiler/independent translation-validator preservation for that
fragment. Generated certificates bind twelve actual symbolic source bodies and
their compiled instructions, quantifying over every environment/call interpretation.
This is stronger than sampled native agreement, but does not complete the full
source/CEK, ordered-clause/guard, callee or host correspondence above. The exact
interfaces and residuals are recorded in audit/README.md.
