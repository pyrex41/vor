# Vör: proof-producing Shen

## Destination

The specification is an executable Shen program whose permitted constructions
carry their correctness evidence. Write a function once. Its behavioral judgment
describes what may be constructed from its inputs; its body constructs the
result and a derivation of that judgment. Execution, simulation, and verification
refer to that same admitted definition.

For the pure total fragment, the target theorem is:

`admitted(f, contract, proof) AND pre(args)` implies every evaluation of this
exact f on args terminates with a result satisfying `post(args, result)`.

For stateful programs, judgments additionally bind the initial state, action,
new state, observations, and requested effects. Global safety follows from
checked initial validity and preservation. Termination, liveness, refinement,
and external-effect correctness remain distinct theorems.

All specifications, executable semantics, proof rules, admission logic, proof
construction, and verification orchestration are to be Shen. Tizoc's
Shen-Scheme on Chez, including Shen kernel PR #117, is the primary host. Small
OS/bootstrap scripts may launch the image and capture bytes; they must not
decide theorem validity. Lean/Rocq are not prerequisites. If later used for an
independent audit, they must not become a second application specification.

The correctness claim is conditional on a specified admitted fragment and named
trusted base. Using one language does not prove all unrestricted Shen, the
compiler, or the physical world correct.

## Backpressure reference and the change

Reference: `pyrex41/Shen-Backpressure` at
`6b9dde09b3a98ee5d20d0a6556acceacad4657d8`. Its actual name contains a hyphen.
This plan draws on its README, payment and tenant specifications,
manifest-driven gates, discharge-report schema, and trust model. Exact links
and the construction design are in [CONSTRUCTION.md](docs/CONSTRUCTION.md).

Keep explicit premise chains, deterministic gates, per-obligation discharge,
counterexamples, source identity, and agent feedback. Strengthen their meaning:

| Backpressure | Vör target |
| --- | --- |
| Spec lowers to target-language guard constructors | Admitted Shen definitions directly inhabit behavioral judgments |
| Constructor checks a predicate for one value | A derivation proves the indexed fact; universal contracts need a generic proof |
| Guard type threads prior validation | Evidence binds the exact principal, tenant, state version, action, and program |
| Derived tests compare implementations on samples | The same definition executes; optimized replacements require equivalence/refinement proofs |
| `verified` premise or external `Check*` wrapper | A derivation, checked decision procedure, or explicit environmental assumption |
| Mixed discharge report | Generic proofs, finite proofs, concrete checks, traces, tests, and assumptions stay separate |

A payment check for transaction A must not authorize B. Membership in one
tenant must not authorize another. A balance proof at version v must not
authorize a write after an incompatible state change. These bindings belong
in the judgment; a suggestive type name is insufficient.

## Starting point: implemented versus proved

PR #1 supplies Boolean transitions, finite-closure certificates, exploration,
trace checking, belief updates, propositional evidence, and indexed System S
judgments. Its recorded baseline is 151 checks, including 64 reference models,
and 134 upstream kernel assertions with PR #117 loaded.

It does not yet meet the destination:

- Most implementation modules are under `tc -`.
- Several datatype rules trust executable Boolean side conditions.
- Annotated propositional elimination shares the explicit proof checker.
- Generic admission, quantification/induction, dependency closure, compiler
  preservation, and effect refinement are not implemented.
- An untrusted artifact reader and sealed release image do not exist.
- Test counts do not discharge these missing theorems.

Retain the Boolean lane for compatibility and independent reference checks.
It need not dictate the final representation. A replacement needs checked
correspondence rather than preservation of accidental implementation details.

`plan/roadmap.shen` is the executable stage/obligation registry. Its validator
checks registry shape, uniqueness, dependency order, and evidence categories.
It does not certify completion. All new mathematical obligations start open.
The original short plan is retained as [INITIAL_PLAN.md](docs/INITIAL_PLAN.md).

## Semantic architecture

One admitted definition contains canonical Shen source, closed dependencies,
operational outcomes, a contract, and checked evidence. Admission freezes name
resolution. Redefining a symbol creates a new program identity and cannot
inherit an old proof merely by retaining a name.

The same definition supports three related uses:

1. Execution by the reference evaluator.
2. Reasoning about its evaluation relation.
3. Construction by rules that compose admitted definitions and their proofs.

Different representations are allowed for efficiency, but every normalizer,
macro expansion, compiler, solver embedding, and adapter then has a preservation
obligation. Being written in Shen does not eliminate that obligation.

Begin with an admission subset of ordinary Shen: pure data, specified ordered
patterns, lexical binding, selected total primitives, and structural recursion.
This is an admission discipline, not a competing general-purpose language.
Unrestricted eval, loading, mutation, redefinition, FFI, and arbitrary Prolog
execution remain outside admitted application definitions until modeled.

## Judgment families

These are planned contracts, not APIs already present:

| Judgment | Evidence required |
| --- | --- |
| well-formed definition/environment | Scope, constructors, primitives, pattern/guard validity |
| evaluates program/inputs/outcome | An evaluation derivation for pinned code and dependencies |
| total program/domain/measure | A termination argument for every input in the domain |
| satisfies program/pre/post | Generic proof connecting evaluation and the predicates |
| preserves program/invariant | Initial validity, transition preservation, frame conditions |
| permits world/principal/action | Facts bound to this version, principal, resources, and action |
| effects program/allowed-effects | Every possible request belongs to the allowed effect algebra |
| refines concrete/abstract/relation | Initial correspondence and simulation of all relevant steps |

Evidence is rechecked. Shen lists are forgeable data, not opaque capabilities.
A trusted host can redefine functions; artifact ingestion must not load code or
new inference rules. A caller-supplied `true` or term named `verified` does not
become a theorem.

Checking one output establishes that concrete result's claim. Proving a recursive
constructor always produces such an output requires a generic function theorem,
termination, and semantic preservation. We want both and report them separately.

## Execution waves

Each wave names implementation artifacts, mathematical obligations, demonstrations,
negative cases, and an exit gate. Later demonstrations cannot waive soundness
dependencies. Registry edges order implementation artifacts, not theorem validity.
For example R01 freezes identity contracts before the proof kernel exists; its
generic obligations remain open until the relevant R02–R05 facilities can check
them. The final admission/release gates require the complete acyclic proof
dependency closure. Starting a child stage never marks its parent proved.

### R00 — Reproduce the foundation

**Artifacts:** existing modules/fixtures, toolchain lock, validation report,
reproducible evidence directory.

Capture exact source/runtime identities and raw counterexamples. Automate the
kernel suite rather than relying on report text. Resolve hosted CI independently
of theorem acceptance. Retain the PR #117 source/host relationship in the bundle.

**Negative cases:** a missing closure edge, modified model, wrong trace label,
or exhausted search cannot yield invariant acceptance.

**Exit:** a fresh Chez image reproduces the baseline. Classify it as tested and
finite-checked, not generic-program-proved.

### R01 — Bind claims, definitions, and assumptions

**Artifacts:** `spec/claims.shen`, `kernel/identity.shen`,
`tests/claim-binding.shen`, inert artifact grammar.

Define claim records carrying rule-set version, canonical program, dependencies,
assumptions, domain, theorem, and evidence kind. Compare canonical structures for
semantic binding; hashes are cache/transport indices unless collision resistance
is an explicit assumption. Specify parser limits and malformed-input outcomes.

**Proofs:** identity cannot substitute differently bound code; report composition
retains all assumptions; no dependency or environmental premise disappears.

**Negative cases:** stale proof/source, wrong inputs/version, dependency rebinding,
and theorem substitution fail before execution.

**Exit:** a proof for A cannot authorize B by changing a symbol, file, or report.

### R02 — Specify a terminating proof kernel in Shen

**Artifacts:** `spec/logic.shen`, `kernel/proof.shen`, primitive-rule inventory,
positive/negative derivations for every rule.

Choose a typed first-order constructive logic with equality and explicit
assumptions. Use an unambiguous scoped binder representation, such as de Bruijn
indices. Specify substitution, freshness, contexts, weakening, and equality. The root inventory
must include the fixed structural-induction principles needed for syntax and
finite derivations; generalized user datatype/induction admission waits for R04.
Proofs are finite data; checking is structurally
recursive. Search may diverge; checking has a total semantics on its domain.

**Proofs:** state context/substitution preservation, per-rule soundness, and
checker termination precisely. Mechanize the available fragments in Shen; carry
remaining obligations explicitly into R04/R16. Identify bootstrap axioms and root
primitive rules explicitly. Self-checking is not independent evidence for the
consistency of the root logic. Turing completeness does not establish consistency.

**Negative cases:** capture, dangling variables, invalid elimination, assumption
leaks, circular derivations, malformed DAGs, unchecked axioms.

**Exit:** the reviewed root rules, formation contracts, and concrete rule corpus
check in a fresh image. The report identifies every unproved metatheory statement
and root assumption. Full checker soundness/totality is an R16 release gate.

### R03 — Define admitted Shen and its evaluation relation

**Artifacts:** `spec/program.shen`, `spec/evaluation.shen`,
`runtime/reference.shen`, normalization certificates.

Formalize clause priority, strictness, guards, lexical scope, primitive outcomes,
and call resolution. Normalize inert source through one versioned route.
Unsupported constructs are rejected. Function references resolve to admitted
definitions, not mutable global bindings.

**Proofs:** normalization preserves meaning; evaluation derivations agree with
the running evaluator; deterministic evaluation where claimed. Recursive
evaluation is a relation, not an inconsistent total equation. Budget exhaustion
is not proof of divergence.

**Negative cases:** overlapping clauses, guard error, repeated pattern variables,
evaluation order, wrong arity, recursive junk results, injected host code.

**Exit:** every admitted form has a semantic rule, and the reference evaluator
has adequacy evidence for precisely those forms.

### R04 — Algebraic data, induction, and exact arithmetic

**Artifacts:** `spec/data.shen`, `proofs/induction.shen`,
`proofs/arithmetic.shen`, constructor/recursion certificates.

Add finite lists, products, sums, naturals, and exact integers. Begin arithmetic
proofs with Peano naturals. Efficient host-integer reasoning needs a checked
correspondence. Specify inductive formation/elimination and positivity; reject
negative occurrences and arbitrary self-referential proof types.

**Proofs:** constructor injectivity/disjointness, induction validity, binder
substitution, arithmetic-certificate soundness, and the Boolean embedding.

**Negative cases:** a nondecreasing termination measure, circular induction,
cyclic values, and silent mixing of floating and exact arithmetic.

**Exit:** generic list/arithmetic lemmas check without sampling or an unnamed
external arithmetic oracle. Floating point remains outside this wave.

### R05 — Proof-producing definitions and admission

**Artifacts:** `spec/contracts.shen`, `kernel/admit.shen`,
`construct/definitions.shen`, `proofs/composition.shen`.

Contracts quantify over input domains and require an existential result plus
evaluation/postcondition evidence. Construction rules require proofs for each
expression, branch, recursive call, and return. Admission checks the generic
proof; execution can additionally check a concrete output witness.

**Proofs:** construction-rule soundness, composition, pattern coverage, totality,
and the main admission theorem. Primitive failure and termination measures belong
in the contract. An optimization needs equivalence evidence before reusing it.

**Negative cases:** right output shape/wrong value, unrelated witness, changed
branch condition, or wrong recursive call cannot be admitted.

**Exit:** an admitted constructor satisfies its contract for every input in its
domain, relative to R02–R04 and the named runtime assumptions.

### R06 — The complete generic transfer demonstration

**Artifacts:** `examples/transfer/program.shen`, checked proof terms, runnable
demo, and mutations with named rejected obligations.

Implement a ledger transfer once in Shen. Bind authority to source/destination,
amount, exact ledger, and version. Distinct accounts are a precondition or the
same-account case has explicit semantics. Insufficient funds is an explicit
outcome. Immutable updates preserve unrelated accounts. Persistence is not yet
claimed.

**Generic theorems:** totality on valid ledgers, nonnegative balances,
conservation of funds, exact debit/credit, frame preservation, account binding,
and validity preservation. Execute the exact admitted definition on success
and rejection paths.

**Negative cases:** omit credit, debit wrong account, swap a permission, change
amount, reuse stale version, or exploit unhandled aliasing. Every mutant must
fail the relevant construction/proof gate.

**Exit:** generic proofs check and the admitted definition runs. A finite test
table cannot substitute for these theorems.

### R07 — Invariant-preserving machines

**Artifacts:** `spec/transitions.shen`, `proofs/reachable-safety.shen`,
`construct/machines.shen`.

Derive state machines from admitted transition definitions. Require checked
initial validity and preservation for every action, including frame/effect
conditions. Define reachability inductively. Finite certificates remain another
decision route, not the only way to prove safety.

**Proofs:** generic reachable-safety, finite-certificate soundness, and
correspondence between constructed machines and executable definitions.

**Negative cases:** an action omitted from preservation, changed invariant,
silently strengthened precondition, or unmodeled result branch.

**Exit:** safety for unbounded execution length follows from checked induction;
finite exploration is complementary evidence.

### R08 — Effects, errors, and ambiguity

**Artifacts:** `spec/effects.shen`, `spec/outcomes.shen`,
`runtime/effect-boundary.shen`, effect-preservation proofs.

Represent pending requests, acknowledgements, rejection, known failure, unknown
outcome, retries, crash/restart, and cancellation. Requests include operation
identity, authority, version, and replay constraints. Proofs govern permitted
requests. The host's actual execution of them is a separate assumption or
refinement target.

**Proofs:** effect closure, freshness, uncertainty retention, safe reconciliation.
A timeout never means no effect. Exactly-once external claims require a durable
protocol and sufficient operational assumptions.

**Negative cases:** lost acknowledgement, duplicate delivery, stale lease,
controller loss after dispatch, cancellation after possible execution.

**Exit:** every observation has an explicit interpretation and cannot erase a
possible state to make a proof succeed.

### R09 — Concurrent composition

**Artifacts:** `spec/composition.shen`, `proofs/interference.shen`, examples of
versioned authority and resource ownership.

Specify atomic abstract actions, scheduling, shared resources, interference,
and environment contracts. Use a checked rely/guarantee discipline or an equally
explicit alternative. Ordinary proof terms are reusable unless admission
enforces a resource policy. Model revocation/versioning; lists are not linear
tokens. Add liveness only with explicit fairness and progress assumptions.

**Proofs:** invariant-preserving composition, interference closure, and any stated
well-founded progress theorem.

**Negative cases:** check/use races, revoked authority, double consumption,
unproved atomicity, unfair runs declared live.

**Exit:** checked interleaving theorems with named assumptions. Actual database
transactions/OS scheduling wait for concrete refinement.

### R10 — Certified finite search, traces, and observations

**Artifacts:** certified explore/trace/observe functions and correspondence
proofs connecting VOR/0 with the admitted program semantics.

A searcher may remain untrusted when the kernel rechecks its certificates and
counterexamples. Prove that belief updates retain every allowed explanation.
Prove minimization preserves the failing claim rather than inventing one.

**Proofs:** finite-closure acceptance, legal counterexamples, observation
soundness/completeness in the stated domain, and reduction preservation.

**Negative cases:** fabricated edges, incomplete successor sets, false
linearizations, dropped ambiguity, and claim-changing shrink results.

**Exit:** faster search improves discovery without gaining theorem authority.
Exhaustion remains unknown; failed explanation search is not automatically a
concrete illegal trace.

### R11 — ShenLogic and THORN assist proof construction

**Artifacts:** `search/shenlogic.shen`, `search/thorn.shen`, obligation export,
proof reconstruction/import formats.

Submit obligations from admitted definitions. THORN, Prolog, SMT, and agents
may propose lemmas or proofs. Reconstruct them in Vör's rules. Unsupported
reconstruction remains external evidence, never a kernel theorem.

**Proofs:** any translation entering acceptance preserves scope, partiality,
arithmetic, and meaning. A prover's `true` or `unsat` status is not a derivation.

**Negative cases:** changed conjecture, inconsistent theory, lost definedness,
foreign axioms, and unknown/timeouts promoted into proofs.

**Exit:** a nontrivial generic obligation is solved externally, reconstructed,
and independently checked by the Shen kernel.

### R12 — The Backpressure loop and reports, in Shen

**Artifacts:** `workflow/gates.shen`, `workflow/report.shen`,
`workflow/context.shen`, immutable obligation/evidence records.

Tasks derive from missing premises and dependencies. An agent edits application
definitions, proposes proofs, and runs search. Changing contracts, domains,
root rules, or assumptions requires an explicit change record; a weaker theorem
is not proof of the original theorem.

**Gates:** identity/formation; admitted dependencies; construction/totality;
contract/invariant proofs; effects/refinement where claimed; negative cases;
deterministic package binding. Shen data declares and Shen code executes them.

**Reports:** exact claim, code/dependency identity, rules, proof terms,
assumptions, evidence kind, missing premises, counterexample, release identity.
One record drives human and agent views. Tests never satisfy generic-proof goals.

**Exit:** repair an invalid program through proof feedback, retaining a checked
derivation for the original contract. Deleting a premise cannot turn the gate green.

### R13 — ShenCheck executes and finds counterexamples

**Artifacts:** `adapters/shencheck.shen`, versioned trace mapping, conformance
fixtures for uncertainty/replay/shrinking.

Reuse drivers, controlled transport, agents, fault cleanup, replay, and reduction.
Interpret histories against the admitted Shen transitions rather than another
hand-written semantics. Bind adapter identity and observation coverage.

**Proofs:** observation mapping and uncertainty preservation. Full implementation
refinement is R14; campaigns cannot establish it alone.

**Negative cases:** incomplete histories, retries counted as independent effects,
erased unobserved operations, wrong incarnation, misleading replay classification.

**Exit:** a faulty real service produces a retained rejected history and reduced
reproduction. Passing campaigns retain their finite scope.

### R14 — Concrete effects and implementation refinement

**Artifacts:** concrete/abstract relations, driver contracts, storage/transaction
assumptions, simulation proofs.

Prove initial correspondence and an abstract explanation for every concrete step,
including stuttering or multiple abstract steps where appropriate. Preserve
observable effects and pending outcomes. Persistence needs atomic commit,
recovery, durability, and a failure model. Remote effects need explicit
acknowledgement/idempotency protocols.

**Proofs:** concrete-to-program simulation. Every concrete-service theorem names
the environmental guarantees it consumes.

**Negative cases:** hidden side effects, incorrect transaction boundaries,
lost durable updates, or concrete steps with no simulation case.

**Exit:** one concrete implementation has checked refinement evidence under
named assumptions; integration tests do not stand in for the simulation proof.

### R15 — Optimization and deployment

**Artifacts:** proof-preserving transformations, Chez native build metadata,
closed dependency bundles, fresh-image replay.

Admitted reference execution is the baseline. Staging, specialization, caching,
compilation, and tree shaking require preservation/refinement of behavior and
assumptions. Rebinding invalidates affected admissions until rechecked.

**Proofs:** transformation preservation and exact artifact binding. Name the
Shen-Scheme/Chez compiler/runtime assumptions until proved; conformance tests do
not establish compiler correctness.

**Negative cases:** stale caches, altered primitive bindings, post-proof mutation,
serialization changes, omitted effects.

**Exit:** an exact artifact is admitted and executed in a fresh trusted image,
with its remaining host trust boundary stated.

### R16 — Apply construction to Vör itself

**Artifacts:** `proofs/kernel/*`, admitted checker/evaluator definitions, root
inventory, bootstrap report.

Construct validators, substitution, evaluator, inference checker, finite
certificate checker, and workflow acceptance decisions under their own formal
contracts. Minimize executable side conditions; prove decision procedures where
retained. Derive public judgments from shared rules rather than trusting two
manually synchronized checkers.

**Proofs:** discharge the applicable existing proof obligations with exact code
bindings. Identify unavoidable bootstrap primitives. Checking a checker in
itself does not establish foundational consistency; residual trust remains.

**Exit:** acceptance implementation has checked construction/preservation
evidence relative to the documented root logic and runtime. No zero-trust-base
or unconditional self-verification claim.

### R17 — Release with the proof in the executable code

**Artifacts:** admitted examples, generic proofs, mutants, execution transcripts,
dependency manifests, and one reviewer command.

Required demonstrations: generic transfer; an invariant-preserving machine;
versioned tenant authorization; ambiguous effects/retry; admitted optimization;
kernel construction evidence. Each includes exact claims, source binding,
checked derivations, assumptions, and failing mutations.

**Exit:** a reviewer starts with the pinned host, checks the root inventory,
replays proofs, executes those exact programs, and sees the mutants rejected.
Every claim has a derivation or an explicit weaker evidence/assumption label.

## Evidence policy and definition of done

A construction milestone is complete only when executable artifacts exist,
theorems/assumptions are frozen, proof terms check in a fresh image, code binding
is verified, and negative cases fail for the stated reasons. Unit tests, PBT,
and campaigns remain required engineering evidence but cannot change proof status.

Evidence categories are not a single strength ranking. Retain `generic-proof`,
`finite-proof`, `concrete-derivation`, `trace-check`, `test`, `assumption`, and
`open`. Only a matching judgment discharges a proof premise. Any changed
dependency invalidates its dependent claims until rechecked.

The first full construction demo must establish:

**This exact Shen definition, for every input in this domain, constructs only
outcomes satisfying this contract and terminates under this checked measure,
relative to these named primitive/runtime assumptions.**

That is the standard for calling an admitted Vör program correct by construction.
