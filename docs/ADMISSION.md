# Total construction and generic admission (R05)

The admitted program remains the exact R03 normalized Shen definition. R05 does
not introduce a second application implementation. `make admission-demo` checks
the generic contracts and executes the same source through the reference machine.

## Contract and evidence

A contract is `[contract Name InputSorts ResultSort MeasureIndex Post]`.
`Post` is a constructive first-order formula scoped by
`[ResultSort | InputSorts]`, nearest first. All input sorts must be declared finite
initial algebras. This first total fragment uses the entire typed input domain;
there is no implicit precondition, hidden error allowance or external axiom.
The measure selects an input argument by zero-based position. At least one input
is currently required. Contract names/order must exactly cover the frozen program.

An admission signature is `[fol-signature 1 [] Functions [] Data]`, where
`Functions` is exactly the contract function list. Constructor collisions,
uninterpreted or foreign functions, hidden predicates and undeclared sorts fail.
All constructor fields must also use these declared algebras; opaque/reserved-tree
fields await their own operational value encoding and are excluded from admission.
Thus every mathematical application function has an exact executable definition.

Evidence is:

```text
[vor-admission 0 ExactProgram ExactSignature ExactContracts
  [[definition Name [[case Constructor ExpressionProof] ...]] ...]
  [[post Name GenericProof] ...]]
```

`vor.admit Program Signature Contracts Evidence Fuel` rechecks the exact identities,
construction derivations and every generic proof. Success is
`[accepted total-admission]`. The generic postcondition theorem replaces the
result binder with the mathematical function application to the input variables
and universally quantifies those inputs. Construction provides the separate
existence/totality justification and the equations connecting that function to
the executable body. For multiple input sorts, quantifiers wrap in reverse input
order so the body retains the declared input-index order.

`vor.construction-root-inventory` records the additional construction rules and
side conditions. `make test-construction-mutations` exercises five independent
mutants in disposable copies, leaving the working tree untouched.

## Reviewed construction rules

This is deliberately a restricted total subset of R03, not an admission claim
for every R03 form. Each function has one clause per constructor of its selected
argument, in constructor declaration order. The selected pattern is exactly that
constructor with distinct variable fields; other input patterns are distinct
variables. Guards normalize to literal `true`. Wildcards, repeated/deep field
patterns, arbitrary guards and incomplete/overlapping coverage are unsupported.
The exact source and every clause are checked, including unused functions.

| Expression evidence | Source construction | Obligations |
| --- | --- | --- |
| `[local]` | A lexical variable | Exact scope/slot and algebraic type |
| `[constructor C Proofs]` | A nullary tag or its canonical cons representation | Exact tag, spine, arity and every field proof/type |
| `[let ValueProof BodyProof]` | A lexical let | Value in old scope; exact value/type prepended for the body |
| `[call Name Proofs]` | A saturated frozen call | Every argument proof, exact signature and dependency/recursion rule |

An ordinary call must target an **earlier** constructed function. Self calls must
use an immediate self-sort field of this clause's selected constructor as the
measure argument, and must preserve the other input terms exactly. This proves
strict structural decrease. Functions may combine several decreasing calls;
nondecreasing calls, fabricated smaller inputs, changed parameters, forward calls
and mutual recursion are rejected. The unchanged-parameter restriction is a
current fragment limitation, not a claim that other terminating programs diverge.
R03 if, general guards, primitives such as hd/tl/equality, higher-order functions,
effects and general recursion are outside this initial construction fragment.

The checker reconstructs a sorted symbolic term for the body from these proofs.
The pattern environment binds exact symbolic values to R03 lexical slots; let
substitutes the same symbolic intermediate value into later calls. It derives
one universally quantified defining equation per exact clause. No artifact may
submit extra defining axioms. Constructor coverage/disjointness and structural
recursion justify interpretation as a total function, relative to the reviewed
construction root and initial-algebra meaning.

`vor.construct` is an untrusted producer of these syntax-directed expression
proofs. `vor.construct-check` rechecks them and returns the reconstructed equations.
`vor.admit` then checks every postcondition proof using only these equations in
its context. A shape-correct wrong result can pass type construction and still
fail the postcondition proof. There is no shortcut named `verified`, `admit` or
an artifact-defined inference rule. `proofs/composition.shen` supplies a generic
constructive composition derivation; the executable composed demo also binds the
exact intermediate value, calls and source equations.

`vor.check-constructed-theorem P Sig Contracts Construction Theorem Proof Fuel`
allows additional closed generic theorems under the same checked equations.
It first checks construction; no caller-added assumption context is accepted.
The equations returned by a helper alone are forgeable data. Calling the general
first-order checker with a context proves only a theorem **under that context**;
the source-bound constructed-theorem API is the route that checks its provenance.

## Execution and transport

`vor.run-admitted P Sig Contracts Evidence Name Args ProofFuel RunFuel` rechecks
admission, verifies exact input domains, runs the R03 definition, checks the
result type and replays the concrete evaluation witness. Success is
`[executed-admitted [value Result] EvaluationEvidence]`. It is not itself an
admission certificate. Mathematical totality on arbitrary finite data does not
remove physical time/memory limits or the explicit execution budget. Exhaustion
returns unknown. An unexpected error/type disagreement also returns unknown,
never a successful contract result.

`vor.admission-typecheck` checks the indexed System S judgment
`[vor-admits P Sig Contracts]` through a literal-only evidence decoder and the
same checker. It is not an independent kernel.

R01 claims use subject `[total-program P Sig Contracts]`, domain `total-shen-1`,
kind `generic-proof`, and judgment `[total-contracts]` or `[theorem ClosedFormula]`.
The former carries admission evidence; the latter carries
`[constructed-theorem 0 Construction Proof]`. The external expected root/claim
must still come from trusted verifier configuration. Dependencies/assumptions
remain bound metadata, not automatically discharged premises. VOR-DATA/0 and the
one-shot service handle these artifacts without source evaluation or new symbol
interning; process tests independently construct valid and hostile fixtures.

## Demonstrations and remaining theorem obligations

`examples/admission.shen` defines addition, recursive identity, a composition,
length and append **once** as inert ordinary Shen definitions. Checked contracts
include add(X,Y)=X when Y=zero, copy(X)=X, twice(X)=add(X,X), total natural-valued
length, and length(append(X,Y))=add(length(X),length(Y)). Additional checked generic
lemmas prove addition associativity and append(X,nil)=X. None enumerates inputs.
The append contract is the stated length law; it does not alone specify element
order. The separate right-identity lemma also does not claim full list equivalence.

These are actual quantified derivations checked by the current trusted root.
They are distinct from a mechanized proof that the **implementation of this
root** is sound. Remaining generic metatheory includes:

1. Declaration/encoding formation, initial-algebra induction validity and binder
   substitution preservation for the new sorts/rules.
2. Soundness of constructor arithmetic decisions and correspondence to
   mathematical signed integers; efficient host-integer reasoning is absent.
3. Pattern coverage/environment correspondence to the R03 matcher and lexical
   evaluator; expression-construction soundness and preservation of strictness.
4. Well-founded totality of constructed definitions, equation adequacy and
   composition; the main all-input/all-outcome admission theorem.
5. Generic soundness/termination of the extended checker and literal/System S
   correspondence, plus the R03 normalization/evaluation and R15 host obligations.

The trust statement is conditional on this reviewed root. No test or example
proof discharges those implementation-wide statements; the roadmap registry
retains its open obligations. The next application stage is R06's exact transfer
contract; it must provide its own conservation, debit/credit, frame and authority
proofs rather than treating these arithmetic/list lemmas as a transfer proof.
