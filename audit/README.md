# Soundness and preservation audit

This optional Rocq/Coq audit supplies checked universal theorems alongside the
Shen implementation. The application source and acceptance authority remain Shen.
Rocq is not required by `make test`, admission or the process service. This is an
independent audit, as permitted by PLAN.md; it does not introduce another
application specification or claim to verify Chez.

```sh
make bootstrap-audit     # optional Linux x86_64, Ubuntu-24.04-compatible binaries
make test-metatheory
make compiler-demo
```

The audit pins **Coq 8.18.0** (the predecessor name of Rocq), with OCaml 4.14.1.
`toolchain.lock.json` records 18 exact archive URLs and SHA-256 digests from the
2026-08-28 Ubuntu snapshot. Bootstrap extracts them under `.tools/`; it does not
install system packages. Alternatively supply `COQC` and `COQCHK` for that version.
Other operating systems should use a local compatible installation. Production
Shen keeps its unchanged shared Chez/kernel43.1/PR117 toolchain.

The command compiles nine modules, checks the global assumptions of twenty named
theorems, and independently rechecks the compiled modules with `coqchk`. There
are no `Admitted`, postulated semantic axioms, classical logic imports or unchecked
native casts. Function/model/certificate premises are **explicit theorem
parameters**; being closed under the global context does not make those premises
true of the Shen implementation automatically.

## Proven statements and their interfaces

| Module | Universal theorem scope | Explicit boundary |
| --- | --- | --- |
| Checker.v | Acceptance yields a finite derivation; remainder never exceeds fuel; one shared node budget; added budget preserves successful checking | Any fixed rule expander; semantic validity requires its local soundness |
| Propositional.v | All eleven quantifier-free constructive rules, arbitrary propositions/valuations/contexts, checker soundness and rejection of closed bottom | Atoms stand for zero-arity predicates; quantifiers, equality, tree/data rules are outside this module |
| Runtime.v | Finite-path acceptance soundness/completeness, exact terminal outcomes, runner receipts check, unique outcome for deterministic paths | Parameterized by frozen step/outcome functions; it does not prove those functions implement Shen |
| Admission.v | Well-founded rank/measure calls; construction implies existence of a finite evaluation satisfying the postcondition and correctness of every evaluation outcome | Requires actual construction derivations. `State` retains full input values; rank/measure are projections, not a replacement for argument identity |
| Compiler.v | Every successful evaluation of the constructor/local/let/call fragment compiles to the same result, preserves environment/stack/frame suffixes and argument order | Fixed pure partial call interpretation shared by both sides; no claim about a native compiler |
| Validation.v | The independent prefix validator accepts exactly the compiler's instruction prefix; checked complete code inherits preservation, totality and all-outcome correctness | Applies to the reflected expression/code, conditional on the stated source/callee semantics |
| CEK.v | Big-step expression evaluation has a finite R03-style CEK execution and every terminating CEK outcome agrees | Constructor/local/let/argument control only; callees are summarized by the same fixed oracle, not an unproved clause-selection algorithm |
| Certificates.v (generated, versioned) | Twelve exact symbolic function bodies have checked translation certificates and preservation for **every** environment and call interpretation | Generated from the exact normalized Shen program and actual compiler output through the source-locked reifier |
| Assumptions.v | Reports dependencies of twenty named generic theorems | The driver rejects unexpected global axioms; ordinary quantified premises remain visible |

The eleven logical rules are hypothesis, top, conjunction introduction and both
projections, implication introduction/elimination, both disjunction introductions,
cases, and bottom elimination. Their model uses constructive `Prop`; no finite
truth table establishes these results. The source scheduler now uses the same
ordered work-list control as Checker.v. Every existing rule remains in the Shen
dispatcher, including the unaudited first-order/algebra extensions.

Admission's call order compares definition rank first, then the size of the
measured input. Earlier definitions may receive arbitrarily large arguments;
self calls require strict decrease. Other typed arguments may change. The
constructor-field size lemma covers every field of an encoded finite constructor,
not a sample of lists. The calculus threads the exact callee and returned value
through its continuation and only assumes that callee's postcondition. This
justifies expanding the executable fragment to accumulator-style recursion,
subject to the remaining checker-to-calculus correspondence below.

## Translation validation is per artifact, preservation is universal

`runtime/compile.shen` is an untrusted compiler producer plus an independent
prefix-consuming checker. It compiles R05 bodies to push/get/join/enter/leave/call
instructions. The checker does not call the producer. Exact function names,
arities, clause patterns, literal true guards, body code and source identity
are retained. Changed operands, lost scope restoration, reordered instructions,
wrong call names/arity, extra instructions and changed program identity fail.

The audit exports the actual normalized definitions and code as inert VOR-DATA/0.
`render_certificates.py` assigns distinct opaque atom IDs to different scalar
classes/names, reifies each symbolic body and its actual instructions, and emits
Rocq terms. Local indices and arities must be natural numbers; artifact strings
never become Rocq source. Booleans and numeric 0/1 are not conflated. The generated
certificate proves `validate Body ActualCode = Some []`. The generic validation
and compiler theorems then give preservation for **all input environments** and
all fixed call interpretations for that body. No ground input table substitutes
for these theorems. Four changed symbolic-code artifacts must fail inside the
Rocq proof kernel: missing instruction, reordered constructor evaluation, wrong
call arity and lost let scope.

The checked bodies include recursive addition, identity, composition/lexical
binding, list length/append and accumulator reversal. The artifact includes the
complete source/program; the generated file records the exact fixture digest.
`build/audit/report.json`, `assumptions.txt`, `coqchk.txt` and generated sources
are reproducible local outputs. The driver also compares generated certificate
source to the versioned audit/rocq/Certificates.v, failing on drift. Regenerate
that file with the export/reifier commands under source review when definitions
change. These outputs are not self-authenticating release claims.

`vor.check-compilation P Artifact` also fits the exact R01 claim and inert
transport boundary. Its acceptance is a syntactic translation certificate under
the reviewed root. It is not a proof of native execution, source normalization
or host compiler correctness. `vor.compiled-outcome` is a qualification executor;
calls use frozen reference evaluation with checked R03 witnesses. It returns a
`compiled-value` candidate, never a generic Vör acceptance. It does not replace
reference execution or discharge callee/whole-machine correspondence by testing.

## Remaining proof closure

This work proves the stated models/calculi and validates the exact compiled
symbolic artifacts. It does **not** close the complete end-to-end soundness claim:

1. Prove the source/reifier/decoder correspondence and Shen implementation of
   the reflected validators, scheduler and machine operations. `source-lock.json`
   makes drift visible; a hash pin is identity evidence, not this theorem.
2. Extend local soundness to the full typed first-order/algebra kernel, including
   de Bruijn weakening/substitution/quantification and constructor induction.
3. Prove that `vor.construct-check` acceptance reconstructs the actual calculus
   derivation: pattern coverage, matcher environments, lexical slots, argument
   typing and exact decreasing-call indices. Then connect checked logical posts
   to the calculus's semantic postcondition premises.
4. Prove closed-program call resolution, ordered matching/guards and the full
   R03 CEK adequacy/normalization correspondence. The shared call oracle in
   the current compiler/CEK theorems is an explicit interface, not a callee proof.
5. Prove the native Shen/KLambda translation and runtime operations that remain
   in scope; the actual Chez compiler/runtime and physical execution stay named
   assumptions. No native-code preservation theorem is asserted here.

The production checker remains trusted pending those bridges. The 57 roadmap
obligations are not automatically marked complete. The audit has moved concrete
universal theorem boundaries; it has not turned tests, an adapter or an assumed
predicate into a proof of the entire system.
