# Algebraic data and exact arithmetic (R04)

`[fol-signature 1 Sorts Functions Predicates Data]` extends the R02 signature;
version 0 retains its meaning. `Data` is an ordered list of
`[data Sort [[Constructor FieldSorts] ...]]` declarations. Constructor names are
globally unique and cannot collide with ordinary functions or the reserved tree
constructors. Fields are individual sort names, never arrow types or proof
judgments. Each declaration may refer to itself and earlier sorts only, and
needs a constructor without a self field. Empty types, uninhabited recursion,
negative occurrences, forward/mutual recursion and malformed fields are rejected.
This is a monomorphic strictly positive fragment, not general datatype admission.
A list with another element type needs its own sort and constructor names.

The meaning is the finite initial algebra: no infinite/cyclic values, extra
constructors, or quotients. Arbitrary first-order functions map into this algebra;
they do not extend its constructors. This interpretation is a named root premise.

`vor.standard-data` declares Peano naturals, canonical exact integers, Booleans,
natural lists, natural products and natural sums. Nullary values are constructor
symbols (`zero`, `nil`); nonnullary values are `[Constructor Field ...]`. For
example `[cell [succ zero] nil]`. These are ordinary R03 inert Shen values. The
encoding is injective within the declared sort; `[zero]`, floats and host numbers
are not Peano naturals. `vor.algebra-value-term` converts a checked value to a
sorted first-order term. Recursive values must be finite host data; the inert
codec has no pointer/reference constructor capable of encoding cycles.

## Fixed inference rules

The existing first-order checker, indexed type and claim route check these three
new rules. `vor.algebra-root-inventory` records their additional root identity;
`vor.fol-root-inventory` remains the inventory of the original 20 R02 rules.
An image containing this extension has a larger trusted root.

| Evidence | Checked conclusion |
| --- | --- |
| `[data-induct [[C Proof] ...]]` | `forall Sort. P`, with exactly one branch per constructor in declaration order |
| `[inject [C LeftArgs RightArgs] Index Proof]` | Equality of the specified field, from equality of the complete constructor applications |
| `[disjoint LeftTerm RightTerm Proof]` | Bottom, from equality of distinct constructors of the same declared algebra |

In induction, fresh field variables enter the scope **in field order**, followed
by the previous variables. Induction hypotheses enter the context in field order
for self-sort fields only; the previous context follows, shifted by the field
count. The motive is shifted beneath fresh variables before instantiation. The
base branch receives no induction hypothesis. Missing/duplicate/reordered cases,
arbitrary-sort induction, circular base proofs and escaped eigenvariables fail.
Every branch consumes the existing shared proof-node budget. Exhaustion remains
`unknown proof-fuel`.

Injection checks the constructor declaration, argument sorts and lengths, field
index, both selected endpoints, and the equality premise. It is unavailable for
uninterpreted functions. Disjointness checks both argument vectors and the common
result sort; repeating one constructor cannot produce a contradiction.

## Arithmetic and proof production

Naturals are `zero` and `[succ N]`. Integers are `[nonnegative N]` for N and
`[negative N]` for -(N+1); there is exactly one representation of zero.
`vor.integer-add` computes using Peano recursion and signed cancellation.
`vor.check-integer-add A B C [integer-add 0 A B C]` validates all three values,
binds the exact operands/result and recomputes the constructor arithmetic. Its
`accepted exact-integer-sum` result is a **ground decision**, not a generic
arithmetic theorem. There is no host numeric coercion, floating point, bounded
word arithmetic, SMT oracle or efficient-host-integer correspondence in this path.

`proofs/arithmetic.shen` produces explicit equality/quantifier/induction terms.
`construct/equality.shen` is an untrusted bounded rewrite/congruence producer;
it can fail or exhaust its search, and cannot authorize a theorem. It emits only
existing checked rules. Definition equations used in the demonstrations come
from the R05 construction checker applied to the **same executable definitions**.
They are not caller-supplied arithmetic axioms or a second addition implementation.

The checked demonstrations include, for all finite values:

- Addition's right-zero law and associativity.
- Append's right-nil law and preservation of the sum of list lengths.
- The identity contract of a recursively reconstructed natural.
- Exhaustiveness of the two Boolean constructors, plus injection/disjointness.

The Boolean encode/decode implementation has complete two-case regression checks;
the generic exhaustiveness proof concerns the declared Boolean algebra. Their
correspondence to host Boolean evaluation is still a metatheory obligation.
Likewise tests against host signed integers are independent engineering evidence,
not proofs of the arithmetic checker implementation. See ADMISSION.md for the
construction root under which the generic application lemmas are checked.
