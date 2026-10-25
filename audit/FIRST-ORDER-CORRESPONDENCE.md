# First-order soundness and the first native implementation bridge

The optional audit now checks **all twenty original R02 rules**, instead of
only their quantifier-free subset. It also proves raw binding refinements and
an implementation theorem about the actual captured KLambda body of
`vor.fol-at`. These are distinct results with the following composition:

1. A concrete raw signature, context, formula and proof are decoded inside Rocq.
2. The typed twenty-rule checker uses those decoded inputs and a shared fuel
   budget. Acceptance implies the input sequent's semantic validity.
3. The capture-avoiding operations satisfy generic representation and semantic
   substitution/weakening equations, including nested binders and free indices.
4. Separately, the actual native lookup body satisfies its contract for every
   proper inert list and exact natural index. Its output agrees with the formal
   variable-typing lookup for every context/index under an injective encoding
   of sort identifiers. This is a checked implementation bridge, not a callee
   oracle and not a bounded test table.

## The twenty-rule theorem

`FirstOrderSyntax.v` defines finite terms/formulas and binder operations. General
renaming and simultaneous substitution are factored through explicit variable
maps and their binder lifts. The source-style cutoff shift and binder-removing
substitution are proved to obey their precise binder equations; replacement
terms shift beneath binders and outer indices decrement once.

`FirstOrderSemantics.v` uses arbitrary value carriers, total function
interpretations, proposition-valued predicates and sort-membership predicates.
Quantifiers range over the stated sort. Function interpretations must respect
their declared argument/result sorts. Environments carry explicit variable-sort
conditions. This is a many-sorted constructive interpretation in `Prop`, not a
classical truth-table approximation. No excluded-middle, choice, function
extensionality, proposition extensionality or postulated rule-soundness axiom
is needed.

The module proves term typing soundness, term/formula renaming and substitution,
weakening, and the binder-substitution semantic equation. These hold for all
finite syntax, arbitrary contexts/interpretations and all binder depths.

`FirstOrderKernel.v` gives the actual rule expansions for hypothesis, top,
conjunction, implication, disjunction, bottom, universal/existential quantifiers,
reflexivity/symmetry/transitivity/substitution, and finite-tree induction. Its
local-soundness proof covers all twenty cases. The checker soundness theorem
then follows from the already checked work-list theorem, without assuming the
rule dispatcher is sound.

The finite-tree rule is proved by Rocq structural induction over finite trees.
The model interface states that the reserved sort contains encoded finite trees
and that the reserved leaf/node functions have their stated meanings. This is
the named semantic meaning of the root algebra, not an assumption that its
induction rule is sound. These model interfaces, and function typing, remain
ordinary explicit premises of the theorem.

The Shen scheduler now validates **each generated sequent**, in addition to the
entry sequent. Thus a malformed generated scope/context cannot silently become
accepted evidence while implementation-wide formation preservation is still
being established. It retains exact node-fuel behavior and failure distinctions.
The Rocq checker uses the same per-node formation gate. This is a reviewed
acceptance implementation change, not a new logical axiom or weakened contract.

## Raw data and binder correspondence

`FirstOrderEncoding.v` decodes signatures, names, terms, formulas, proof objects
and goals from inert cell/atom data. It supports the original signature version
0, including the reserved tree functions. Signature names/arities/sorts and
reserved names are checked. Python does **not** interpret a proof or resolve a
logical variable index: it only serializes raw quoted data into fixed Rocq data
constructors. The trusted proof kernel evaluates the decoder and checker.

Encoding/decoding round trips and injectivity for terms/formulas are universal
checked theorems. `raw_checker_sound` connects raw checker acceptance through
that decoder to the semantic sequent theorem. Unknown constructors, extra fields,
improper lists and wrong scalar classes cannot acquire a logical meaning by
being named suggestively. Strings, symbols, Boolean values, natural numbers and
invalid numeric values occupy distinct constructors.

`FirstOrderRaw.v` proves that the source-style raw term/formula walkers for
cutoff shifting and binder removal refine the logical operations for **every**
encoded term/formula, amount/replacement and binder depth. This closes the raw
representation/operation equation. It does not on its own prove that every
compiled Shen walker body implements that raw algorithm; that native/source
bridge remains separate. Source hashes and finite comparisons are not promoted
to this missing universal implementation theorem.

The audit additionally exports the actual Shen checker results for the original
rule corpus. Rocq decodes each raw sequent/proof and checks **504** acceptance
comparisons across budgets (163 accepted). All twenty original rules appear.
Negative and nonintegral indices are quoted as invalid-number atoms, preserving
their distinction from natural indices rather than coercing them through the
restricted production wire codec. Nonacceptance includes both rejection and
unknown; it is not a proof that a formula is false. These 504 comparisons are
finite implementation evidence, distinct from the universal soundness theorem.

## Actual KLambda lookup preservation

`audit/export-native.shen` obtains `ps vor.fol-at` from the loaded pinned Shen
image and exports that compiler-produced definition as inert data. The reifier
preserves its operator/operand/parameter structure; fresh parameter names are
encoded injectively. Name-to-local-slot resolution happens inside Rocq, not in
the reifier. `NativeCapture.v` is a versioned, checked certificate that this
captured definition decodes to the body whose contract is proved.

`NativeLookup.v` defines the relevant KLambda operations, lexical argument
slots, conditionals, short-circuit conjunction, list operations, exact natural
comparisons/subtraction, and calls back to that exact body. There is no external
recursive-call oracle. It proves totality and determinism on proper finite lists
and exact natural indices, and that every evaluation returns the correct found
value or missing result. The complete two-argument ABI is part of the capture.

`LookupBridge.v` obtains the evaluated body from the actual capture, then proves
its result agrees with the formal first-order variable lookup for arbitrary
contexts and indices. The bridge is parameterized by the encoding of sort
identifiers; injectivity is required for the found-result iff statement. It
therefore does not confuse the logical signature's identifier numbers with the
native capture's atom numbering. This proves the lookup stage of variable typing;
it does not pretend to prove the remaining native typechecker branches.

These are KLambda-level preservation/correspondence theorems for the actual
captured body. The meaning of the supported primitive operations, accurate
source capture, stable runtime bindings, and preservation by the Shen-Scheme
backend/host remain named execution assumptions. Integer-valued floating-point
representations and physical time/stack/heap bounds are not silently included
in the exact-natural model. No theorem here verifies the Chez compiler.

## Reproducible checks and remaining closure

`make test-metatheory` checks 46 named theorem dependencies, 18 modules with
`coqchk`, the 12 earlier symbolic-body certificates, the 504 first-order
comparisons, and 19 strict serializer tests. It rejects four bad stack
translations, two corrupt actual KLambda captures, and two binding/quantifier
implementation mutants against the existing proofs. Old positive reports and
exports are archived before a new run so stale files cannot substitute for a
failed export. The source manifest is still an identity/drift check only.

Remaining work is now more specific:

- Prove the compiled implementations of the other binder/typing/dispatcher
  helpers refine the raw and sorted operations, then compose that with the
  literal Shen checker control. A universal proof of the entire Shen checker
  has not been inferred from the 504 comparisons.
- Extend raw signature support and local rule soundness to the three R04
  user-algebra extension rules: data induction, injection and disjointness.
  The original twenty-rule theorem does not include them.
- Connect construction checking to the already proved admission calculus and
  close the program normalization/callee/ordered-guard and full CEK bridges.
- Prove the relevant Shen-to-KLambda and KLambda-to-Scheme/runtime translations
  beyond the captured lookup body. The actual Chez compiler remains assumed.

The 57 roadmap requirements remain requirements; scoped theorem and bridge
results are recorded individually rather than marking full release closure.
