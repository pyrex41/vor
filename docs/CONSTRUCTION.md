# Construction design: the spec is the program

## The important distinction

A conventional workflow defines an ideal function, writes another function,
and tests whether they agree. Vör's default should instead admit the executable
definition itself under a checked behavioral contract. Proof-producing
construction assembles that definition and the derivation together.

The contract is still needed: one executable program can correctly implement
the wrong requirement. The duplication we remove is the second executable
algorithm, not the distinction between behavior and requirements.

Three questions must be answered separately:

1. Does this value have a valid derivation of the requested judgment?
2. Does this constructor produce a valid result for every input in its domain?
3. Does the actual deployed artifact execute that admitted constructor's meaning?

The current Vör implementation addresses concrete instances of the first
question. R05/R06 address the second; R14/R15 address concrete deployment of the
third. R16 binds the acceptance implementation itself to its formal contract.

## The single authoritative unit

A proposed admitted definition contains these fields. This is a design sketch,
not an implemented file format or a new API:

```text
Definition = canonical Shen source
Environment = closed mapping of names to admitted definitions/primitives
Contract = input domain + outcomes + postcondition + effect/frame conditions
Proof = derivation that this Definition in this Environment satisfies Contract
Admission = checked(Definition, Environment, Contract, Proof, RootAssumptions)
```

An admission check must bind all fields. It must not return a freestanding
`safe` flag that callers may attach to different code. Hashing the fields is
useful for indexing; semantic identity is the canonical structure unless the
cryptographic assumption is part of the claim.

Execution initially interprets that admitted definition with the reference
semantics. It does not invoke whichever live global happens to have the same
symbol. Native compiled execution becomes an admitted replacement when its
preservation argument and exact artifact binding are supplied. Until compiler
preservation is proved, the compilation path remains a named assumption.

## What Shen's sequent calculus does here

System S can express judgments indexed by values, program terms, contexts,
states, and results. A rule can require another derivation before constructing
its conclusion. We should use that expressiveness directly rather than flatten
the domain into nominal wrappers with Boolean flags.

For example, the following is logical notation for planned rules, **not
copy-paste Shen syntax**:

```text
ValidLedger(L)
Account(L, source, sourceBalance)
Account(L, target, targetBalance)
Distinct(source, target)
Natural(amount)
AtMost(amount, sourceBalance)
Permitted(world, principal, transfer(source,target,amount), version(L))
--------------------------------------------------------------------
AuthorizedTransfer(world, principal, L, source, target, amount)
```

The corresponding construction rule must carry the same indices throughout:

```text
AuthorizedTransfer(world, principal, L, source, target, amount)
DebitCreditEvaluation(transferDefinition, L, source, target, amount, L2)
ConservationDerivation(L, L2)
NonnegativeDerivation(L2)
FrameDerivation(L, L2, source, target)
--------------------------------------------------------------------
TransferResult(transferDefinition, world, principal, L, action, L2)
```

These are theorem obligations, not trusted axioms we can add just to make a
program typecheck. Prove the debit/credit constructor generically using its
recursive definition and arithmetic/ledger lemmas. Then ordinary composition
can reuse that checked theorem. Ground execution also returns a replayable
evaluation witness for the result it actually constructs.

This closes several specific holes:

- A witness about source A cannot be paired with a debit from B.
- A witness for amount 10 cannot authorize amount 100.
- A witness for ledger L cannot authorize L2 after a conflicting update.
- A proof that the total balance is unchanged cannot conceal a debit and
  credit applied to the wrong accounts; exact-value and frame properties are
  separate premises.
- A successful abstract transfer does not assert that two real database writes
  were atomic; that belongs to concrete refinement.

## Generic construction theorem

For inputs in the declared domain, an admitted total function must establish
existence of both a result and its derivation, and correctness of every modeled
evaluation outcome. In logical notation:

```text
forall args.
  Pre(args) ->
    exists result, evaluationProof, postProof.
      Evaluates(definition, environment, args, result, evaluationProof)
      and Post(args, result, postProof)

forall args, outcome.
  Pre(args) and Evaluates(definition, environment, args, outcome)
    -> AllowedOutcome(args, outcome)
```

The first statement supplies total correctness for a deterministic total
fragment when paired with evaluation determinism. The second makes the
all-outcomes requirement explicit when errors or nondeterminism are introduced.
No proof of existence of one safe result may hide another illegal result.

Each recursive constructor must provide coverage, a well-founded decreasing
measure, hypotheses only for smaller inputs, and branch-local proofs. Calling
the same function on an unchanged argument cannot be justified by simply
assuming the desired contract. General recursion stays representable in a
partial-correctness relation, but cannot enter the total fragment without a
termination derivation.

For composition, the intermediate value and witness from f are exactly the
inputs to g. Require a proof that f's postcondition entails g's precondition.
If a function has declared error outcomes, those are composed explicitly;
returning an error to avoid required work does not satisfy a success-only
contract.

## Small trusted kernel, large untrusted construction space

Agents, THORN, Shen Prolog, finite search, and external solvers can explore
freely. None gets a privileged `prove true` entry point. They submit inert
derivations to a fixed rule set. The kernel checks rule identity, premises,
substitution, scope, and the target conclusion.

An artifact cannot extend the inference rules that check itself. New axioms,
primitives, or datatype-rule modules change the trusted base and invalidate the
affected release identity. An agent cannot fix a failed theorem by weakening
the contract without producing a visible specification change.

Initially the kernel and selected semantics are trusted Shen source. The
construction plan progressively supplies their own contract/preservation
derivations. The final report must identify which primitive logical rules,
host behavior, and bootstrap code remain assumed. A self-checking system does
not establish its own foundational consistency merely by accepting itself.

## Behavioral types do not make mutable facts timeless

An authorization derivation proves a statement about a world or snapshot.
If authority can be revoked, later use must require the same relevant version,
an interference theorem, or revalidation. The effect executor must enforce
the corresponding commit/version condition.

Similarly, a proof value does not become a one-use resource by convention.
An executable admitted resource discipline must track use, ownership, or
version changes if the property requires them. These facts are especially
important for retries, leases, payments, and concurrent actors.

## Gate feedback as part of the executable workflow

Each missing premise becomes a structured obligation with an exact claim and
dependency set. The Shen workflow gives the agent the failing rule, relevant
input/branch, expected judgment, supplied witness, and any checked counterexample.
Do not turn "could not find proof" into "program is false".

The workflow distinguishes:

| Outcome | Meaning |
| --- | --- |
| checked generic derivation | The quantified contract follows under its assumptions |
| checked finite certificate | The specified finite/inductive-set claim follows |
| checked ground derivation | This input/result or transition is justified |
| rejected proof | This submitted proof does not establish its claimed judgment |
| checked counterexample | A legal execution violates the stated property |
| unknown | Budget, missing evidence, or unsupported reconstruction prevents a result |
| sampled agreement | Tests agreed on the named sample; no universal discharge |

The report retains exact evidence kinds and assumptions. It cannot compress
all of them into an undifferentiated `verified: true` field.

## Proof in the pudding: reviewer acceptance script

The planned release command must do all of the following in a fresh image:

1. Validate the root-rule inventory and exact admitted source/dependencies.
2. Replay generic contracts and construction derivations, including termination.
3. Execute those definitions on concrete inputs and check output witnesses.
4. Demonstrate rejection of unrelated, stale, and substituted witnesses.
5. Reject each mutated constructor at the relevant proof obligation.
6. Replay effect/refinement proofs separately from empirical fault histories.
7. Emit a claim-bound report including the remaining host/root assumptions.

A passing output table alone cannot complete this script. Neither can an
arithmetic proof detached from the definition that is actually executed.

## Case analysis and derived equality (untrusted producers)

`construct/cases.shen` and `construct/derive-eq.shen` are proof and source
producers. They add no rule, side condition or axiom. Their output goes
through the same `vor.normalize`, `vor.construct-check`, `vor.admit` and
`vor.check-constructed-theorem` routes as hand-written input. The trusted
root inventories are unchanged; `tests/cases.shen` checks this.

**Case analysis.** `vor.prove-script Sig Vars Gamma Goal Script Fuel` consumes
the goal's leading quantifiers with `gen` or `induct` (data-induct; each branch
continues the script), then searches:

- `imp`: `intro`. An equality hypothesis is normalized in the context *before*
  it is added, so it cannot rewrite itself. Distinct constructor normal forms
  close the goal with `exfalso` and `disjoint`. Otherwise a normalized copy is
  introduced with `apply`/`intro`, so it acts as a rewrite rule.
- Equality: rewrite both sides with the bounded rewriter. If the normal forms
  differ, try a ground hypothesis that normalizes to distinct constructors,
  constructor congruence (`subst` chains), backchaining through a hypothesis
  `forall Xs. Pre -> L = R`, and finally a case split.
- Case split on an enumeration-sorted, non-constructor subterm `T` of the goal
  or of a ground hypothesis: prove `forall Z. T = Z -> Goal` by data-induct,
  instantiate `Z := T` and discharge `T = T` by `refl`.

A search failure leaves `[search-failed]` in the term and the kernel rejects
it. Depth bounds nesting (at most 2^Depth split branches); fuel bounds each
rewrite. Contract posts may already be implications (R05 Post is any formed
formula over `[Result | Inputs]`); this producer is what makes conditional
posts and theorems with a decidable hypothesis practical. It is not a
precondition: the contract domain is still every value of the input sorts.

**Derived structural equality.** `vor.derive-eq Data [Truth Yes No] Sorts`
emits ordinary R05 source: `derive.and`, a constructor test
`derive.is.C`, field projections `derive.get.C.I` (a fixed default value for
other constructors) and `derive.eq.S` per sort, with `[top]` contracts. It also
emits, per sort, `forall X. eq(X,X)=yes` and
`forall X Y. eq(X,Y)=yes -> X=Y` with proof scripts.
`vor.derive-lemma-proof` proves lemma K with all earlier lemmas proved and
introduced first. Every field sort must be the sort itself or derived
earlier. The generated equality is a definition like any other; soundness is
a checked theorem about it, not a property of the generator.

`make cases-demo` runs `examples/scoping.shen`: identifier equality soundness,
the tenant scoping theorem without hand lemmas, `find(T,C,P)=some(R) ->
company(R)=C`, a conditional contract post, and the derived equality bundle.
The always-yes equality and a lookup without its company check admit as total
functions, run to return another company's row, and fail every scoping
theorem, both through the producer and when the accepted proofs are replayed.

## Reference material examined

All Backpressure references below are pinned to the same reviewed snapshot:

- [README](https://github.com/pyrex41/Shen-Backpressure/blob/6b9dde09b3a98ee5d20d0a6556acceacad4657d8/README.md)
- [Payment spec](https://github.com/pyrex41/Shen-Backpressure/blob/6b9dde09b3a98ee5d20d0a6556acceacad4657d8/examples/payment/specs/core.shen)
- [Tenant authorization spec](https://github.com/pyrex41/Shen-Backpressure/blob/6b9dde09b3a98ee5d20d0a6556acceacad4657d8/examples/multi-tenant-api/specs/core.shen)
- [Manifest-driven gates](https://github.com/pyrex41/Shen-Backpressure/blob/6b9dde09b3a98ee5d20d0a6556acceacad4657d8/thoughts/shared/research/2026-05-05-wave-1-manifest-driven-gates.md)
- [Discharge-report schema](https://github.com/pyrex41/Shen-Backpressure/blob/6b9dde09b3a98ee5d20d0a6556acceacad4657d8/thoughts/shared/research/2026-05-05-discharge-report-schema.md)
- [Trust model](https://github.com/pyrex41/Shen-Backpressure/blob/6b9dde09b3a98ee5d20d0a6556acceacad4657d8/docs/TRUST-MODEL.md)

The plan borrows the engineering pattern, not every strength claim or historical
status statement from those documents. Vör's claims must be justified by its
own exact derivations and assumptions.
