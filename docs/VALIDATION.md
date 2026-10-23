# Initial foundation validation

The selected shared runtime is pyrex41/shen-scheme `v0.52-pyrex41.5`, with
source archive SHA-256
`c57f47586894534b9797daf5c0cc65c58dc6fb89d6ea6f0c2b48ac64de66d010`, based on
Shen-Scheme `8d261518db17fbfec32d1b268b40ed216b925c74` and kernel commit
`ec16a9fa4fc2e87e2aa336fb1ae30e8ac2266394`. Linux source builds and the
macOS arm64 binary use this same lock; no alternate Shen runtime is accepted.

- `make bootstrap`: passed release archive verification and runtime identity checks.
- `make test`: **151 checks passed**.
- Of those, 64 compare generated finite Boolean models with an independent
  four-state bitset closure oracle. Safe results require kernel acceptance;
  unsafe results require rechecking the generated counterexample as a trace.
- Other checks exercise simultaneous updates, exact/exhausted budgets,
  initial violations, malformed inputs, missing closure edges, stale models,
  forged acceptance records, trace labels, partial observations, proof scope,
  indexed transition witnesses, System S agreement, and inert proof handling.
- `sh -n scripts/bootstrap scripts/shen`: passed.
- Upstream Shen-Scheme kernel suite at
  `8d261518db17fbfec32d1b268b40ed216b925c74`, using the same release runtime
  and the pinned 43.1 kernel: **134 passed, 0 failed**.

The upstream suite was invoked from its own clean checkout with:

```sh
/path/to/shen-scheme eval -l /path/to/t-star-pr117.shen \
  -l scripts/run-shen-tests.shen
```

macOS bootstrap is configured with the published archive checksum but has not
been executed in this validation. No cross-port or compiler correctness claim
is made. CI repeats Vör conformance on the primary Linux/Chez host.

## Construction-plan addition

After adding the executable roadmap and detailed construction design,
`make test` passes **167 checks**: the original 151 plus 16 planning-contract
checks. The roadmap contains 18 stages and 54 required evidence goals, all
reported open. Its negative cases reject dependency cycles, missing/forward
dependencies, duplicate stages/goals, improper data, unknown evidence kinds,
and self-reported completion fields. These are planning checks, not new proofs
of Vör's mathematical correctness. No acceptance-kernel semantics changed.
