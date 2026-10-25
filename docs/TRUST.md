# Trust boundary

The authoritative transition meaning is `shen/core.shen`. The invariant
acceptance kernel is `shen/certificate.shen`. The explorer is an evidence
producer and is deliberately outside the finite-certificate acceptance path.
Observation and trace checking use the same successor semantics.

Current trusted components are the reviewed Vör source, Shen compiler and
System S where used, the Shen-Scheme backend, Chez runtime, and the host that
executes them. Propositional acceptance additionally trusts `shen/proof.shen`
and its literal decoder. There is no independently verified machine-code path.

Tests and cross-checks are evidence, not a mechanized soundness theorem. No
Lean/Rocq proof was included in the original foundation. An optional Rocq/Coq
audit is now included for the specific metatheory described in audit/README.md. Vör does not claim a smaller trusted base
merely because some source files are short.

Models and proof objects passed to public APIs are inert finite data. Loading
an arbitrary `.shen` file is execution of trusted code and can redefine the
kernel, proof rules, or host bindings. It is not an untrusted artifact loader
or sandbox. An acceptance result is valid only for an unchanged trusted image.

Hash-checked bootstrap downloads establish the selected shared Shen-Scheme
artifact identity, not that an artifact is correct. The exact PR #117 typechecker
overlay is checksum-checked and loaded on every invocation; helper arities are
also checked. The release binary is not assumed to embed those helpers. This is a
runtime reproducibility and regression gate, not a proof of the compiler,
Chez, or typechecker implementation.

Unsupported domains are rejected rather than approximated. VOR/0 has Boolean
states and atomic abstract actions; it does not model OS threads, I/O errors,
partial functions, crashes, resource budgets of the SUT, or dynamic loading.
Those need explicit outcomes and semantics before they can enter a claim.

Pending refinement proofs, checking an implementation's recorded traces does
not imply all implementation executions are permitted. A specification may
also faithfully express the wrong requirements.


The R01 claim boundary additionally trusts `spec/claims.shen`,
`kernel/identity.shen`, and `kernel/artifact.shen`. Expected root and claim must
come from trusted verifier configuration, not from the submitted envelope.
Root strings declare identity; they do not measure or authenticate this image.
Declared dependencies/assumptions are retained as data, not proved true or
admitted transitively. The indexed claim datatype delegates to the same checker
and is not an independent kernel. See CLAIMS.md for the restricted codec domain
and the distinction between syntactic budgets and process resource isolation.


R02 additionally trusts `spec/logic.shen` and `kernel/proof.shen`, including typed
formation, de Bruijn operations, all 20 fixed rules, and the initial-algebra
meaning of the reserved finite-tree sort. First-order symbols are mathematical
names, never host callbacks. The System S first-order judgment delegates to the
same kernel. The root is explicitly stronger than the original propositional
fragment; artifact/label equality alone does not attest a running root version.
See LOGIC-METATHEORY.md for residual semantic and encoding premises.


R03 additionally trusts the syntax/closure normalizer in spec/program.shen,
the small-step relation in spec/evaluation.shen, and the runner/witness checker
in runtime/reference.shen. Program names resolve in frozen definitions; this
is not protection against rebinding trusted checker/primitive implementations
or a proof of complete native dependency closure. Selected host value operations
remain trusted. Native eval-kl is used only by controlled test fixtures, never
by admission, reference evaluation, or artifact acceptance. PROGRAM-METATHEORY.md
states the still-open generic preservation, determinism, and adequacy claims.


R04/R05 extend the trusted root with spec/data.shen, the version-1 signature
formation clauses, the data-induct/inject/disjoint rule expansions in
proofs/induction.shen, spec/contracts.shen, and kernel/admit.shen. The finite
initial-algebra interpretation and the structural-construction/equation link
to R03 execution are explicit premises pending the metatheory in ADMISSION.md.
The integer ground decision additionally trusts constructor arithmetic in
proofs/arithmetic.shen. Its generic proof builders and construct/ producers
have no privileged acceptance path. The 20-rule R02 inventory alone no longer
describes the full loaded root; vor.algebra-root-inventory adds the three algebra
rules, and kernel/admit.shen defines the separate construction/admission rules.
Generic application proofs are available relative to that root; the root's own
generic soundness/termination, R03 adequacy and host preservation remain open.


The work-list scheduler, expanded structurally decreasing call rule (construction
root v2), stack translation validator and qualification executor are additional
reviewed Shen code. The optional audit supplies twenty named assumption-free
model/calculus theorem checks and per-body universal preservation certificates;
"assumption-free" here excludes global postulates, not explicit theorem parameters.
Source/model, full first-order rule, checker/calculus, callee and host bridges
remain visible in audit/README.md. The source hash manifest is a drift detector,
not a proof of these bridges. No Chez compiler implementation was changed or
removed from the trusted base. The qualification executor's compiled-value tag
is not accepted as theorem evidence by any Vör claim route.


The next audit stage now checks the complete original twenty-rule many-sorted
first-order model, generic weakening/substitution semantics, and raw encoding/
binding refinements. The actual captured KLambda body of vor.fol-at has a checked
universal contract and a representation-parametric bridge to formal variable
lookup. Every generated Shen work-list sequent is now formation-checked. See
audit/FIRST-ORDER-CORRESPONDENCE.md for exact interfaces and validation. The three
user-algebra extension rules, the remaining literal compiled helpers/dispatcher,
construction/callee bridges and native backend preservation remain open. The
46 named theorem checks are not a claim of full implementation/release closure.
