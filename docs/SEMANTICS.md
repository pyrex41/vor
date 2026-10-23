# VOR/0 semantic contract

## Models

`[vor-model 0 Variables InitialStates Rules Invariant]` is the complete model
identity. Every field is compared structurally, including rule order and the
invariant; certificates have no mutable registry name to resolve.

Variables are distinct non-Boolean symbols. States are proper lists of exactly
one Boolean per variable. InitialStates is a nonempty, duplicate-free list of
states. There are at most 2^n states for n variables.

Expressions are `[lit true]`, `[lit false]`, `[var Name]`, `[neg E]`,
`[conj E F]`, and `[disj E F]`. Unknown variables and unknown constructors are
rejected. Expressions are total over validated finite states. There is no
host eval, callback, arithmetic, recursion, external effect, or implicit clock.

`[rule Label Guard Assignments]` uses a distinct non-Boolean symbol label.
Assignments are `[Variable Expression]` pairs with no repeated variable. Each
enabled rule contributes a successor; all guards read the old state, and all
assignment right-hand sides read that same old state. Variables not assigned
retain their values. Every enabled rule is considered; rule order does not
encode priority. Self-loops are explicit transitions.

## Certificates and induction

`[vor-certificate 0 ExactModel States]` proposes a finite inductive set C. For
initial set I, transition relation R, and invariant Inv, acceptance requires:

1. Model and all states are well formed, and C has no duplicate states.
2. I is a subset of C.
3. For every s in C and every enabled labelled edge R(s,l,t), t is in C.
4. For every s in C, Inv(s) is true.

Induction on execution length gives the intended theorem: every state reachable
from I through R satisfies Inv. This mathematical argument does not yet prove
the Shen implementation meets its definitions; see PROOF-OBLIGATIONS.md.
Unreachable states in C are allowed if they meet closure and safety conditions.

The BFS producer can stop with `unknown state-budget`. It does not emit an
accepted partial certificate. A real counterexample may be returned before a
budget check because it already demonstrates a violation. The checker has no
search budget: its work is finite in the supplied certificate and model size.
Process time/memory exhaustion is not an acceptance result.

## Observations and traces

A trace is `[[initial State] [step Label State] ...]`. Its initial state must
be in I and every recorded edge must be in R. No stuttering is inserted.
Acceptance establishes a safe finite prefix only. An invalid edge is rejected;
a legal edge reaching an unsafe state is a violation. An unsafe initial state
is also a violation.

Partial observation updates take a nonempty set B, one observed rule label l,
and a duplicate-free list of `[Variable Boolean]` fields. The successor belief
is exactly `{t | exists s in B. R(s,l,t) and t matches every observed field}`.
All compatible states are retained. Empty output is forbidden-observation;
exceeding the configured input or output state bound yields unknown. The API
does not establish that a caller-supplied B was reachable. Multiple states are
uncertainty about an abstract state, not a distribution of probabilities.

## Propositional proof objects

Formulas: `[atom Name]`, `[truth]`, `[falsehood]`, `[both P Q]`, and
`[implies P Q]`. Contexts: `empty`, `[assuming P Context]`.

| Object | Rule |
| --- | --- |
| `[hyp]` | The target formula occurs in the context |
| `[unit]` | Truth introduction |
| `[pair A B]` | Conjunction introduction |
| `[intro A]` | Implication introduction, checking A under one additional assumption |
| `[apply P A B]` | Implication elimination with an explicit antecedent P |
| `[left Q A]`, `[right P A]` | Conjunction elimination with the other conjunct annotated |
| `[absurd A]` | Derive the target from a proof of falsehood |

The depth limit bounds proof-tree height, not total nodes or elapsed time.
There is no admit, external axiom, recursion, classical excluded-middle rule,
or unification of arbitrary host programs with propositions.

System S's public `vor-proves` judgment validates the formula and context before
using internal `vor-derives` rules. Internal judgments are not public claims.
Introduction, hypothesis, and falsehood-elimination rules are explicit datatype
rules. Annotated eliminations pass through a literal-only cons-syntax decoder
and the same explicit proof checker with depth 1000. Thus System S can reject
a deeply nested proof accepted with a larger explicit depth limit. Errors in
the public typechecking service become unknown, never acceptance.

`vor-initial`, `vor-step`, and `vor-safe` are indexed by the exact model and
states. A `vor-safe` witness is state-local; it does not assert reachability.
