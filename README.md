# Vör

Executable semantics. Checked evidence.

Vör is a new Shen verification core. One closed transition semantics drives
execution, trace conformance, finite invariant certificates, and partial
observation tracking. Shen's programmable type system checks evidence indexed
by the exact model, state, transition endpoints, or logical proposition.

**Status: implemented foundation, not a verified Shen compiler or a proof of
arbitrary application correctness.** The initial semantic domain is finite
Boolean state machines. See [the trust boundary](docs/TRUST.md) before
interpreting an acceptance result.

## Run

The primary host is **Tizoc's Shen-Scheme on Chez**. Bootstrap pins upstream
v0.52 by archive SHA-256 and loads the exact typechecker from
[Shen kernel PR #117](https://github.com/Shen-Language/shen-sources/pull/117),
also by SHA-256. No JavaScript runtime is used. PR #117 belongs to the kernel
repository, not to shen-scheme.

```sh
make bootstrap
make test
make demo
```

Pinned binaries are provided for Linux x86_64 and macOS arm64. Linux is the
initial tested platform. `toolchain.lock.json` records provenance. Downloads and
host files remain in `.tools/`. `scripts/shen` installs and checks the PR #117
helpers on every invocation; it does not assume the release already has them.

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

## Relationship to existing projects

Vör establishes the semantic authority. **ShenLogic** is a future proof
translation consumer, subject to its translation obligations. **ShenCheck** is
a future execution and counterexample producer. Neither integration is
implemented yet. Existing evidence is not relabelled as Vör proof.

See [semantics](docs/SEMANTICS.md), [architecture](docs/ARCHITECTURE.md),
[proof obligations](docs/PROOF-OBLIGATIONS.md), and [execution plan](PLAN.md).
