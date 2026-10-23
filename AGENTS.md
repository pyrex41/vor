# Working on Vör

- Read README.md, docs/SEMANTICS.md, docs/TRUST.md, and
  docs/PROOF-OBLIGATIONS.md before changing acceptance semantics.
- Use tizoc/shen-scheme on Chez with Shen-Language/shen-sources PR #117.
  `make bootstrap` installs pinned artifacts; `make test` is the main gate.
- Keep models/proofs inert. Never evaluate artifact-supplied code.
- Keep producers outside acceptance. No budget exhaustion, host error,
  missing observation, or unsupported feature may become proof of safety.
- State exactly what each acceptance result establishes. Trace conformance,
  model invariants, and implementation refinement are distinct claims.
- Treat new datatype rules and side conditions as changes to the trusted base.
- Add meaningful negative and independent-reference checks for semantic changes.
- Preserve dirty checkouts and existing evidence; pin external references.
