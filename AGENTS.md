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
- Follow PLAN.md and the stage/obligation registry in plan/roadmap.shen.
  Read docs/CONSTRUCTION.md before implementing admission or new proof rules.
- The admitted Shen definition is the executable specification. Avoid a second
  hand-written implementation; prove correspondence for necessary translations.
- Keep generic proofs, concrete witnesses, finite proofs, tests, and assumptions
  distinct. No test result or caller-supplied Boolean discharges a generic theorem.
