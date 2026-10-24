# R02: constructive first-order evidence

R02 adds a many-sorted first-order acceptance kernel implemented in Shen.
Signatures, terms, formulas, contexts, and proof trees are inert data. The
kernel has a fixed inventory of 20 rules; artifacts cannot add rules or axioms.
The existing VOR/0 and propositional services remain compatible.

This supplies the R02 executable rule inventory, formation contracts, scoped
operations, and positive/negative rule corpus. It does not discharge generic
checker soundness, termination, or compiler-preservation obligations. Those
metatheory claims remain explicit R04/R16 work. See LOGIC-METATHEORY.md.

## Signature and typed scope

```text
[fol-signature 0 Sorts Functions Predicates]
Functions  = [[Name [ArgumentSort ...] ResultSort] ...]
Predicates = [[Name [ArgumentSort ...]] ...]
Term       = [v Index] | [app Name [Term ...]]
```

User sort and symbol names are non-Boolean Shen symbols. Sort names and names
within each function/predicate namespace are unique; function and predicate
namespaces are separate. Function arguments/results and predicate arguments
must use declared sorts or the fixed `vor.tree` sort. Arity and every argument
sort are checked; arbitrary Shen calls/values are not terms.

`Vars` is an ordered list of variable sorts, nearest/newest first. `[v 0]`
refers to its head. Indices must be natural numbers and in range. A quantifier
adds one sort at the head. There are no implicit free variables, named-variable
substitutions, metavariable unification, or name-resolution callbacks.

The fixed sort `vor.tree` is not user-declared. Its only constructors are
`[app vor.leaf []]` and `[app vor.node [Left Right]]`. A signature cannot
redeclare those names or add functions returning `vor.tree`. Functions may
consume trees and produce other sorts. This deliberately reserves the algebra;
user datatype admission waits for R04.

## Formula grammar

```text
[top] | [bottom] | [pred Name [Term ...]]
[equal Sort Left Right]
[and P Q] | [or P Q] | [imp P Q]
[forall Sort Body] | [exists Sort Body]
```

Equality requires both terms to have the specified sort. A context `Gamma` is a
proper list of formed formulas over the same signature and variable scope.
The target and all assumptions are validated before checking evidence.

Logical assumptions in Gamma remain in the theorem's statement. Envelope
Assumptions are separate environmental metadata; neither sort of assumption is
a proof that an external fact currently holds.

## Binding and substitution

Internal `vor.fol-shift P Amount Cutoff` raises term-variable indices at or
above Cutoff and increases Cutoff when crossing a quantifier.
`vor.fol-sub Body Term Depth` removes the binder at Depth:

- Replace that index with Term raised by Depth.
- Decrement indices above the removed binder.
- Leave lower indices (inner binders) alone.
- Increase Depth beneath a quantifier.

For example substituting the outer variable in `forall y. r(x,y)` with a free
variable does not turn it into `forall y. r(y,y)`. The same operations handle
both universal/existential rules and equality motives.

The public `vor.fol-instantiate Sig Vars Sort Body Term` checks the signature,
scope, motive formation, and replacement sort, then returns `[ok Formula]` or
explicit rejection. Internal operations require formed syntax; they are not
public parsers for arbitrary host objects.

## Fixed inference inventory

In this table, all judgments share the same signature. `shift(G,n)` raises all
free indices in G by n. `P[t]` removes P's distinguished binder using the
capture-avoiding substitution above. Formula annotations and witness sorts are
checked before constructing premises.

| Evidence | Target and required premises |
| --- | --- |
| `[hyp i]` | Target equals exactly Gamma[i] |
| `[top]` | Target is top |
| `[pair a b]` | P and Q proofs for target P and Q |
| `[fst Q e]` | Proof of P and Q for target P |
| `[snd P e]` | Proof of P and Q for target Q |
| `[intro e]` | Prove Q under P::Gamma for target P implies Q |
| `[apply P a b]` | Prove P implies Q and P for target Q |
| `[inl e]` | Prove P for target P or Q |
| `[inr e]` | Prove Q for target P or Q |
| `[cases P Q e a b]` | Prove P or Q; prove target under each branch assumption |
| `[exfalso e]` | Prove bottom under the same context |
| `[gen e]` | For forall S.P, prove P in S::Vars with shift(Gamma,1) |
| `[inst S Body t e]` | Prove forall S.Body; target must equal Body[t] |
| `[witness t e]` | For exists S.Body, t has sort S and e proves Body[t] |
| `[unpack S Body e branch]` | Prove exists S.Body; branch proves shifted target under Body::shift(Gamma,1) in S::Vars |
| `[refl]` | Target is equality of the same formed term |
| `[sym e]` | Prove reversed equality |
| `[trans middle a b]` | Prove left=middle and middle=right, with a correctly sorted middle |
| `[subst S Motive l r eq body]` | Prove l=r and Motive[l]; target must equal Motive[r] |
| `[tree-induct base step]` | Fixed finite-tree induction, described below |

Hypothesis indices select logical assumptions; term-variable indices select
Vars. They are distinct namespaces. There is no admit, arbitrary axiom, proof
reference, cyclic graph, excluded-middle, double-negation-elimination, or
induction-over-an-arbitrary-sort constructor. Evidence uses finite trees;
proof-DAG ingestion/reconstruction is not implemented.

### Fixed structural induction

`[tree-induct Base Step]` applies only to `[forall vor.tree P]`. It requires:

1. Base proves `P[leaf]` in the original variable/context scope.
2. Step introduces fresh left/right children in `[vor.tree vor.tree | Vars]`.
   Its first two assumptions are P(left), P(right), followed by Gamma raised
   by two indices. Step must prove P(node(left,right)).

The motive's distinguished binder is retained while its outer variables are
raised; instantiation then removes that binder. This prevents capture of outer
variables in the two-child step. The conclusion cannot export a fresh child.

This is an explicit primitive principle for the finite leaf/node initial
algebra, not a theorem about arbitrary uninterpreted sorts or all unrestricted
Shen values. Finite syntax and derivations can be represented by finite trees;
proving their encodings, shape predicates, and corresponding induction lemmas
is still R03/R04/R16 work. Constructor disjointness/injectivity and arbitrary
user inductive definitions are not added as undocumented axioms.

## Checking and resource outcomes

```shen
(vor.fol-check Sig Vars Gamma Target Proof Fuel)
(vor.fol-typecheck Sig Vars Gamma Target Proof)
(vor.fol-typecheck-bounded Sig Vars Gamma Target Proof Fuel)
```

Successful explicit checking returns `[accepted first-order-derivation]`.
Fuel is a natural at most 65535, counting proof nodes across the whole tree;
branch premises consume the remaining fuel sequentially. Zero/exhausted fuel
returns `[unknown proof-fuel]`. Malformed sequents, invalid rules, and invalid
annotations are rejected. Host errors return uncertainty, never acceptance.

Fuel bounds proof-rule visits, not formula validation, substitution work, CPU,
stack, or allocation. The finite data contract and the byte-codec input limits
remain relevant. No in-process service sandbox or totality theorem follows
from a numeric fuel argument.

The System S judgment is `[vor-fol-proves Sig Vars Gamma Target]`, with a
literal-only decoder and a fixed checker-backed datatype rule. The public
typechecking API first checks evidence and propagates uncertainty, then asks
System S to check the exact indexed judgment. Its default fuel is 65535. This
is the same kernel, not independent verification of that kernel.

The existing bound-claim typechecking wrapper now also propagates checker
uncertainty before inference. In particular a proof exceeding its fixed 1000
budget remains unknown rather than being mislabeled an invalid proof.

## Claim envelopes and runnable theorem

The added claim domain is:

```text
Subject  = [first-order ExactSignature Vars]
Domain   = constructive-first-order
Judgment = [derives Gamma ExactTarget]
Kind     = concrete-derivation
```

The R01 envelope binds the full signature, variable scope, logical assumptions,
conclusion, declared dependencies, root, and environmental assumptions. Existing
byte artifact decoding supports these finite data objects unchanged. Root labels
still do not measure the executable image; adding this kernel changes the
trusted source inventory and needs a newly reviewed release identity.

`make logic-demo` checks and typechecks this closed theorem from explicit proof
data in `examples/first-order.shen`:

```text
(forall x. P(x) implies Q(x)) implies
  ((forall x. P(x)) implies (forall x. Q(x)))
```

The proof uses eight nodes; seven units of fuel produce unknown. Logical
quantification is now supported, but admitting an application definition under
a generic execution contract still requires R03–R05.
