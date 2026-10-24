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
Lean/Rocq proof is currently included. Vör does not claim a smaller trusted base
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
