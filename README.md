# Vör

Executable semantics. Checked evidence.

Vör is a new Shen verification core. One closed transition semantics drives
execution, trace conformance, finite invariant certificates, and partial
observation tracking. Shen's programmable type system checks evidence indexed
by the exact model, state, transition endpoints, or logical proposition.

**Status: implemented foundation, not a verified Shen compiler or a proof of
arbitrary application correctness.** Supported domains are finite Boolean state
machines, explicit constructive first-order derivations, and a restricted
structurally recursive total Shen fragment. See [the trust boundary](docs/TRUST.md) before
interpreting an acceptance result.

## Run

The primary host is the shared **pyrex41 Shen-Scheme on Chez** runtime used by
ShenCheck. Bootstrap pins release `v0.52-pyrex41.5` by archive SHA-256. The
release source is based on upstream Shen-Scheme `8d261518`. The published
macOS binary lacks PR #117 helpers, so the launcher always loads the complete
checksum-pinned typechecker from kernel commit `ec16a9f` and checks its helper
arities. The launcher requires ShenOSKernel 43.1 before applying the overlay.
The lock records host and kernel identities separately. No JavaScript runtime is used.

```sh
make bootstrap
make test
make test-kernel
make demo
make boundary-demo
make logic-demo
make program-demo
make admission-demo
```

The published release includes a macOS arm64 binary; Linux is built from the
same checksum-pinned source when a binary is unavailable. `toolchain.lock.json`
records provenance. Downloads and host files remain in `.tools/`. `scripts/shen`
checks the selected runtime identity on every invocation and never silently
falls back to another Shen implementation.

## A model and its evidence

Models are inert Shen data. Boolean expressions contain only literals,
variables, negation, conjunction, and disjunction. Rules have a label, guard,
and simultaneous assignments. Unassigned variables keep their values.

```shen
(load "vor.shen")
(load "examples/mutex.shen")
(vor.verify (mutex.model) 4)
\\ [accepted finite-invariant 3]

(vor.verify (mutex.broken) 4)
\\ [counterexample [[initial [false false]]
\\   [step alice-enter [true false]] [step bob-enter [true true]]]]

(vor.verify (mutex.model) 2)
\\ [unknown state-budget]
```

The explorer produces a finite state-set certificate. The acceptance kernel
separately checks model identity, state validity, initial-state inclusion,
closure under **every** enabled transition, and the invariant at every member.
An inductive superset is allowed; the checker does not trust a reachability
claim from the producer. A searched trace is recheckable with `vor.trace`.

| API | Claim |
| --- | --- |
| `vor.next Model State` | All labelled successors of a valid state, possibly unreachable |
| `vor.explore Model Bound` | A candidate certificate, counterexample, or explicit uncertainty |
| `vor.check-certificate Model Certificate` | A finite inductive invariant for this exact model |
| `vor.verify Model Bound` | Search followed by certificate checking |
| `vor.trace Model Trace` | Conformance and invariant safety of this finite prefix |
| `vor.observe Model Belief Label Fields Bound` | All compatible successor states given a partial observation |
| `vor.proof Context Proposition Evidence Depth` | An intuitionistic propositional derivation under the stated context |
| `vor.typecheck Evidence Judgment` | Acceptance of a supported indexed evidence judgment by System S |

`consistent` observation results are not global safety proofs. Trace-prefix
acceptance is not implementation refinement. Invariant acceptance does not
establish termination, deadlock freedom, or liveness.

## Proofs as behavioral types

```shen
(vor.proof empty [implies [atom p] [atom p]] [intro [hyp]] 30)
\\ [accepted derivation]

(vor.typecheck [intro [hyp]]
  [vor-proves empty [implies [atom p] [atom p]]])
\\ [accepted typed-evidence]

(vor.typecheck [step alice-enter [true false]]
  [vor-step (mutex.model) [false false] alice-enter [true false]])
\\ [accepted typed-evidence]
```

Contexts are `empty` or `[assuming Proposition Context]`. The judgments carry
their assumptions and endpoints; a bare Boolean or a forged `accepted` record
is not evidence. The inference rules and the bounded explicit proof checker
are in `shen/proof.shen`. Annotated elimination rules decode literal syntax and
delegate to that checker; these are not independent proof kernels.

## Closed Shen execution and witnesses

R03 adds a pure first-order Shen subset with ordered clauses, repeated patterns,
guards, lexical let/if, saturated closed calls, and selected primitives.
`vor.normalize` freezes source and definitions; `vor.run` executes those exact
definitions and returns a finite machine-path witness. `vor.check-evaluation`
rechecks every transition and exact outcome, also through indexed types and
claim envelopes.

`make program-demo` evaluates the single recursive append definition and checks
its witness. See [the admitted syntax and semantics](docs/PROGRAM.md) and
[remaining adequacy/preservation obligations](docs/PROGRAM-METATHEORY.md).
This is concrete execution evidence, not generic all-input correctness or
termination admission. Effects and higher-order forms remain unsupported.

## Algebraic data and generic contracts

R04/R05 add monomorphic positive initial algebras, induction, constructor
injection/disjointness, Peano arithmetic, canonical signed integers, and checked
construction/admission of a structurally recursive total subset. Generic proofs
for addition, recursive identity, composition and append bind the exact Shen
source that runs. `make admission-demo` checks these contracts and executes it.

See [data and arithmetic](docs/DATA.md) and [admission](docs/ADMISSION.md) for
rules, APIs, examples and limitations. These quantified application derivations
are checked relative to the reviewed construction root. Generic implementation
soundness, the main admission metatheorem and compiler preservation remain open.

## First-order proof kernel

R02 adds a fixed 20-rule constructive first-order kernel with sorted signatures,
de Bruijn scopes, capture-avoiding instantiation, equality, quantifiers, and a
reserved finite-tree induction principle. `vor.fol-check` checks explicit proof
trees; `vor.fol-typecheck` checks the exact indexed System S judgment.

`make logic-demo` checks a closed quantified implication theorem from eight
proof nodes. See [the logic contract](docs/LOGIC.md) and
[metatheory/root obligations](docs/LOGIC-METATHEORY.md). The accepted derivations
are relative to this trusted implementation and root theory; generic checker
soundness, the admission metatheorem, and host preservation remain open.

## Exact claims and inert artifacts

`vor.check-claim` binds an existing finite certificate, trace, or propositional
witness to the verifier's exact expected claim, including root identity,
dependencies, assumptions, domain, and judgment. `vor.typecheck-claim` exposes
that binding as an indexed System S judgment. `vor.check-artifact` decodes a
bounded inert byte-list envelope before checking it; no source reader or eval
is used. The verifier supplies the expected claim separately from the artifact.

See [the grammar and trust limits](docs/CLAIMS.md) and the
[current execution plan](docs/ADVANCEMENT.md). This is the R01 foundation for
existing domains, not generic program admission or the ShenCheck wire service.

## Relationship to existing projects

Vör establishes the semantic authority. **ShenLogic** is a future proof
translation consumer, subject to its translation obligations. **ShenCheck** is
a future execution and counterexample producer. Neither integration is
implemented yet. Existing evidence is not relabelled as Vör proof.

See [semantics](docs/SEMANTICS.md), [architecture](docs/ARCHITECTURE.md),
[proof obligations](docs/PROOF-OBLIGATIONS.md), and [execution plan](PLAN.md).

## Construction roadmap

The target is proof-producing Shen definitions: the executable specification
constructs its result and correctness evidence under a checked generic contract.
The [detailed plan](PLAN.md) defines 18 dependency-ordered waves, exact artifacts,
theorem obligations, hostile cases, and exit gates. The
[construction design](docs/CONSTRUCTION.md) explains the admission theorem,
indexed transfer example, effects, and the trusted root.

`make plan` executes the Shen roadmap registry and lists its open obligations.
Registry validity is a planning check, not proof that a wave is complete. The
current foundation does not yet prove generic program correctness by construction.

The experimental [one-shot checker transport](service/README.md) accepts inert
VOR-DATA/0 frames under a trusted startup configuration. Run `make test-service`
for its hostile process corpus. This is a transport prerequisite; ShenCheck and
BEAM refinement remain open.
