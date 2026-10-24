# Historical foundation validation

The following receipts predate the shared-runtime migration. They apply to the
original upstream v0.52 host plus PR #117 overlay and are not current-host
qualification.

Tested on Linux x86_64 with the checksum-pinned Tizoc Shen-Scheme v0.52 binary
and the complete `t-star.shen` from Shen kernel PR #117 merge commit
`ec16a9fa4fc2e87e2aa336fb1ae30e8ac2266394` loaded before Vör.

- `make bootstrap`: passed archive verification and kernel overlay verification.
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
  and PR #117 overlay: **134 passed, 0 failed**.

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

## R01 claim and artifact boundary

On the same pinned Linux x86_64 host (ShenOSKernel 43.1 with PR #117):

- The unchanged foundation reproduced **167 passing checks** before edits.
- `make test`: **795 checks passed** after adding exact-claim binding, indexed
  claim evidence, inert byte-list encoding/decoding, and assumption regressions.
- The corpus includes all 256 one-byte inputs, every proper prefix of a complete
  propositional envelope, independent fixed byte vectors, exact/exhausted budget
  edges, unsupported values, forged acceptance, substituted dependencies and
  assumptions, literal injection attempts, and transient invariant failures.
- `make boundary-demo`: the encoded finite certificate was checked against the
  separately supplied expected claim; a forged acceptance payload was rejected.
- `make test-kernel`: **134 upstream assertions passed, 0 failed** against the
  clean pinned source checkout at `8d261518db17fbfec32d1b268b40ed216b925c74`.
  The runner retains the upstream harness counters instead of its final reset,
  then checks the exact counts in Shen. It does not change assertion bodies or
  the kernel. stdin is closed so a failure cannot wait for interactive input.
- `git diff --check` and shell syntax validation passed.

The upstream suite is now an executable Make target and a hosted workflow step.
The previously published hosted runs did not start: GitHub's annotation reported
account payment/spending-limit restrictions. Local results do not establish
hosted CI success, and this change does not alter account billing settings.

All original proof obligations remain open. Three additional R01 obligations
record codec round-trip, codec totality, and indexed-bound correspondence (57
registry goals total). No tests above discharge those generic theorems.

## R02 scoped first-order kernel

Validated with the same checksum-pinned Linux x86_64 Shen-Scheme host,
ShenOSKernel 43.1, and PR #117 overlay:

- `make test`: **74,130 checks passed**. This includes the existing 795 checks,
  161 additional targeted rule/scope/claim/budget/demo checks, 7,168 classical
  finite-model sequent checks, 61,440 semantic substitution/weakening checks,
  30 resulting-formula scope checks, and 4,536 two-world Kripke sequent checks.
  These counts describe bounded engineering evidence, not theorem strength.
- Every one of the 20 rules has a positive and negative case through the explicit
  and indexed checking paths. Tests reject capture, eigenvariable escape,
  assumption leaks, forged equality, incorrect arity/sorts, circular-reference
  objects, arbitrary axioms, arbitrary-sort induction, and executable-looking data.
- The indexed-claim wrapper preserves unknown for proof-fuel exhaustion, rather
  than converting it into an invalid-evidence verdict.
- `make logic-demo`: checked the closed quantified implication-distribution
  theorem, including the indexed System S judgment. Eight fuel units suffice;
  seven return unknown. This is an actual derivation relative to the fixed root,
  not a sample-based proof of the theorem.
- `make test-kernel`: **134 upstream assertions passed, 0 failed**.
- Isolated source mutations were tested against copies using the same pinned
  runtime; the working sources were not modified by the mutation runs:

| Mutation | Observed rejecting regression |
| --- | --- |
| Omit universal-context raising | bad-generalization: expected rejected, got accepted |
| Omit existential conclusion raising | witness-escape: expected rejected, got accepted |
| Omit lifting a substituted term below binders | substitution-capture produced captured v0 instead of free v1 |
| Accept arbitrary equality endpoints as reflexive | equality-forged: expected rejected, got accepted |
| Replace the induction step target by its left hypothesis | tree-induction positive corpus no longer derived the intended theorem |

The mutation runs detect these specific regressions; they do not establish
complete mutation coverage or generic soundness. The finite interpreters are
independent from checker execution and binder transformations, but are themselves
unverified test code. LOGIC-METATHEORY.md describes the exact finite model families
and the remaining universal constructive-soundness/termination obligations.

The initial finite-tree algebra and root rules are explicitly trusted premises.
The implementation does not prove its own consistency, syntax/derivation
encoding adequacy, generic application admission, or compilation preservation.


## Shared-runtime migration: 2026-10-23

Current host: `pyrex41/shen-scheme v0.52-pyrex41.5`, with the archive hashes
and source/upstream-basis identities in `toolchain.lock.json`. The complete
`ec16a9f` typechecker is loaded separately, SHA-256
`480e26c610b593b66f87118ea2fbeacaf34201e42f2279a09decfb9481879168`.
The published binary's version banner does not establish PR #117 inclusion.

- macOS arm64: verified binary archive, `make bootstrap`, `make test`
  (**167 passed**) and `make demo`.
- Ubuntu 24.04 x86_64, existing `shen-ci` guest: verified source archive,
  built Chez/Shen-Scheme, checked overlay helper arities, and ran `make test`
  (**167 passed**). Source build has a ten-minute deadline plus kill grace.
- `sh -n scripts/bootstrap scripts/shen` and `git diff --check` passed.

These are fresh runtime/conformance results. The historical upstream 134-test
receipt above has not been rerun as a current-host kernel qualification. No
mathematical obligation, compiler correctness claim, application integration,
or implementation refinement gate is promoted by this runtime change.

## Combined R01/R02 and shared runtime: 2026-10-24

The integrated tree combines the claim/artifact and first-order kernel changes
with the shared `v0.52-pyrex41.5` runtime. On macOS arm64, the checksum-pinned
archive and exact PR #117 overlay passed:

- `make test`: **74,130 checks passed**.
- `make test-kernel`: **134 passed, 0 failed**, using the pinned upstream test
  checkout and the same shared runtime/overlay.
- `make demo boundary-demo logic-demo plan`: passed, retaining all generic
  proof obligations as open.
- Whitespace and shell syntax checks passed.

The integration preserves the explicit kernel 43.1 guard and the Chez/helper
checks. The upstream-test launcher now reads the platform-specific host-path
cache used by bootstrap. Earlier sections remain historical at their stated
hosts; this does not retroactively refresh their evidence. The exact-head hosted
checks for the integration are separate from this local receipt. Independent
review found no concrete first-order scope/fuel defect, while retaining the
documented operational limits around symbol interning and physical resources.
This is no claim of generic soundness, application admission or refinement.

## R03 closed execution on the shared runtime

Base: integrated main at `16b5b5580f19ff76180621acac50ea6581f64edc`.
Runtime: checksum-pinned `pyrex41/shen-scheme v0.52-pyrex41.5` source archive,
ShenOSKernel 43.1, and the exact PR #117 overlay from toolchain.lock.json.
The Linux x86_64 source build used `TAR_OPTIONS=--no-same-owner` because this
workspace cannot restore the archive's original uid/gid; source and archive
identities were unchanged. No runtime source patch or old-host substitution
was used. The integrated pre-R03 suite reproduced **74,145 passing checks**.

- `make test`: **75,081 checks passed**, retaining all prior suites. The R03
  additions cover normalization/closure, repeated patterns, guarded priority,
  lexical scope, recursive/mutually recursive calls, modeled errors, strictness,
  host-name rebinding, proof identity, transition tampering, typed/byte claims,
  and evaluation-fuel uncertainty.
- The bounded native expression grammar produces 395 cases, each compared
  against native eval-kl and followed by witness rechecking. Compiled native
  fixtures independently cover the supported pattern/guard/protect behavior.
  Test-only native evaluation is unreachable from artifact acceptance.
- `make program-demo`: the one inert append definition returned `[a b c d]`
  and its concrete witness checked. The demo does not supply a second native
  application implementation or a generic all-input contract.
- `make test-kernel`: **134 upstream assertions passed, 0 failed**, on this
  shared runtime and overlay.
- `make test-service`: **14 tests passed**. The new semantic-process case checks
  a closed-program evaluation witness, rejects its skipped transition, and
  preserves unknown when checking fuel is exhausted.
- Five isolated source mutants were detected by copies of the test suite:

| Mutation | Observed regression |
| --- | --- |
| Reverse normalized primitive arguments | cons returned an improper wrong-value result |
| Omit the new let scope | a bound variable was rejected as unbound |
| Remove repeated-pattern equality | unequal arguments matched the same-variable clause |
| Ignore witness-edge equality | a skipped transition was incorrectly accepted |
| Skip normalization recomputation | a modified normalized body retained acceptance |

Shell syntax, Python test syntax, and `git diff --check` passed. The only
`eval-kl` occurrences in the three acceptance modules are inert reserved-name
entries; no host evaluation or source loading is invoked there.

These are concrete derivations and bounded engineering evidence. All generic
normalization preservation, formation/step preservation, determinism, evaluator
adequacy, totality, and native/compiler correspondence obligations remain open
as specified in PROGRAM-METATHEORY.md. Frozen application names do not establish
complete trusted runtime dependency closure or concurrent root-rebinding safety.
