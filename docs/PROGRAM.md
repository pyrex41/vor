# R03: closed Shen definitions and concrete evaluation witnesses

R03 adds a first-order pure Shen admission subset, one versioned normalization
route, an executable small-step relation, a reference runner, and a finite
execution-witness checker. The definition is written once as inert source data;
execution and witness checking use that exact normalized definition.

This is syntax/closure admission and concrete evaluation evidence. It is not
R05 generic correctness-contract admission, a totality proof, or a proof of
Shen-Scheme compilation preservation. PROGRAM-METATHEORY.md states the remaining
normalization/adequacy/determinism obligations. Existing proof obligations remain
open until matching generic derivations exist.

## Source contract

```text
[shen-source 0 [Definition ...]]
Definition = [define Name Pattern ... -> Body [where Guard] ...]
```

The optional guard notation above is explanatory, not a nested list in the
actual token stream. A definition contains one or more ordered clauses. Body
and Guard are each one reader-level expression tree. The arrow and optional
`where` delimit each clause. All clauses in a definition have the same arity;
zero-argument definitions are allowed. Duplicate function names are rejected.

This is ordinary reader-level Shen syntax for the supported forms, not raw text
or an unrestricted Shen reader. The caller supplies inert AST data. A cons/list
pattern or expression uses the reader-level `[cons H T]` tree; bracket notation
must already have been expanded into those constructors by a trusted frontend.
There is no source text reader, macro loader, or host evaluation in admission.

Pattern forms:

- `_`: wildcard, independently ignored at every occurrence.
- Uppercase-initial ASCII symbols: variables. First occurrence binds a slot;
  repeated occurrence requires structural equality with that same value.
- Scalars and empty list: literal patterns.
- `[cons HeadPattern TailPattern]`: recursively match any cons cell, including
  an improper tail. Variables are collected head first, left to right.

Bodies and guards support scalar/empty-list literals, scoped variables,
`[if Condition Then Else]`, `[let Variable Value Body]`, saturated direct calls,
and `[protect Symbol]` as a literal-symbol form. Let has one binding in this
version; its value uses the old scope and its body adds a new nearest binding.
It may shadow a pattern variable or an outer let binding.

Values are Booleans, symbols, strings, integral naturals through 65535, empty
list, and finite cons trees over those values. Fractional/negative/wider numeric
literals and host closures/vectors are rejected. Arithmetic and richer inductive
value theories wait for R04; small integral literals are not a proof of a host
integer ABI. Strings/symbols accepted by the in-memory API may exceed the
existing transport codec's narrower ASCII/proper-list domain.

Primitive whitelist:

| Primitive | Arity | Meaning |
| --- | --- | --- |
| cons | 2 | Construct a cons cell |
| hd / tl | 1 | Select from a nonempty cons; other inputs give a domain error |
| cons? | 1 | Cons-cell predicate |
| empty? | 1 | Equality with empty list |
| number? / string? / symbol? | 1 | Predicates over the admitted values, using the trusted host value primitives |
| = | 2 | Structural equality |

Program calls must resolve within the complete definition set, including forward
references and mutual recursion, or to this fixed primitive table. Call arity
must match exactly. No partial application, computed calls, lambda/freeze/thaw,
arbitrary macros, effects, eval, loading, global lookup, exception handlers, or
Prolog execution is admitted. If/let/protect have their declared syntax; unknown
forms are rejected. Core primitive/macro names and the vor./shen. namespaces
cannot be declared as program functions. Merely returning executable-looking
symbols/lists does not execute them.

## Normalization and identity

```shen
(vor.normalize Source)
(vor.program? Program)
(vor.check-normalization Source Certificate)
```

Normalization returns `[ok [vor-program 0 ExactSource Definitions]]` or explicit
rejection. Each function has an arity and ordered normalized clauses. Patterns
become wildcards, literals, cons patterns, or indexed binding/equality slots.
Expressions become literals, indexed locals, branches, lexical binds, explicit
user invocations, or primitive calls. The complete program is closed before
execution; it does not consult host globals named after program functions.

The exact source remains in the identity. Renaming a bound variable may produce
similar indexed code, but still changes the program identity. This is a
repeatable versioned normalization, not semantic equivalence or canonicalization
modulo all program transformations.

A normalization certificate is `[vor-normalization 0 ExactSource Program]`.
Checking recomputes the fixed normalization and compares the entire result.
`vor.program?` does the same before public execution. A caller cannot edit the
normalized body, binding index, clause order, primitive, or dependency target
beneath an old source identity. This checker is not an independent proof that
the normalization preserves all native Shen semantics.

## Small-step operational contract

The authoritative operational function is `vor.machine-step` in
spec/evaluation.shen. A state is `[machine Control Continuation]`.

| Control / frame | Next behavior |
| --- | --- |
| literal/local expression | Return that value / the exact lexical slot |
| branch expression | Evaluate its condition first, retaining the two unevaluated branches |
| branch frame with true/false | Evaluate only the selected branch |
| branch frame with another value | Terminate with nonboolean-condition |
| lexical bind | Evaluate the value first, then evaluate the body with the value prepended to its environment |
| user/primitive call expression | Begin evaluation of its arguments |
| argument list/frame | Evaluate arguments strictly from left to right, retaining the same lexical environment |
| complete user call | Resolve only in Program's frozen definitions |
| clause choice | Match patterns; mismatch advances to the next clause without evaluating its guard/body |
| matched clause | Evaluate its guard in the pattern environment |
| true guard | Evaluate the body; do not inspect later clauses |
| false guard | Continue with later clauses |
| non-Boolean or failing guard | Terminate with an explicit error; never treat it as false |
| primitive call | Apply the fixed operation or emit its domain error |
| exhausted clauses | Terminate with no-clause |

Continuations retain the clause environment, remaining arguments/clauses, and
function identity explicitly. Recursive calls are ordinary transitions; there
is no implicit termination axiom. Both a recursive function and a recursive
guard can exhaust fuel without establishing divergence or safety.

Terminal outcomes are `[value Value]` or `[error Reason]`. Modeled errors include
primitive-domain, nonboolean-condition, nonboolean-guard, and no-clause. Internal
invalid-local/call-arity/unknown-function cases are also explicit; formation
preservation is needed to prove them unreachable for admitted calls. Host errors
and exhausted budgets return unknown rather than a modeled successful outcome.

## Execution and rechecking

```shen
(vor.run Program Name Args Fuel)
(vor.check-evaluation Program Name Args Outcome Witness Fuel)
(vor.execution-typecheck Program Name Args Outcome Witness Fuel)
```

The runner returns:

```text
[evaluated Outcome
  [vor-evaluation 0 ExactProgram Name ExactArgs Outcome [State ...]]]
```

The witness starts at `[machine [call Name Args] []]`. The checker independently
walks the supplied path, checking each edge against the same deterministic
operational relation. It does not trust the producer's output label, terminal
value, or status. The path must end at the exact claimed terminal outcome;
truncation, extra steps after termination, substituted identity, and skipped or
altered transitions are rejected. A finite nonterminating prefix proves nothing.

Fuel counts transitions, is a natural at most 65535, and is threaded through the
whole run/check. A terminal state requires no extra transition. Exhaustion yields
`[unknown evaluation-fuel]`. It is not an application error or a proof of
nontermination. Full-state witnesses can use substantial memory; these are not
proved physical time/stack/memory bounds or a process sandbox.

The indexed System S judgment is `[vor-evaluates Program Name Args Outcome]`.
It uses literal decoding and the same witness checker; the public typed wrapper
prechecks the requested fuel and preserves uncertainty. It is not a second
independent operational semantics or a soundness proof of this implementation.

Acceptance of an error outcome establishes that this exact evaluation reached
that error. It does not establish that the application's required contract was
satisfied. No generic all-inputs contract, totality, invariant, authorization,
external effect, or implementation-refinement claim is implied.

## Claims, process service, and demo

R01 now supports `admitted-shen-0` claims with kind `concrete-derivation`:

- Subject `[program P]`, judgment `[evaluates Name Args Outcome]`.
- Subject `[source Source]`, judgment `[normalizes Program]`.

All fields remain structurally bound to the verifier's expected claim. The
existing process service can recheck a byte-encoded evaluation witness under a
trusted fixed configuration/symbol whitelist; its transport protocol is unchanged.
The service regression includes acceptance, a skipped-step rejection, and fuel
uncertainty. Transport status 0 means the configured evidence claim checked,
including when that claim names a modeled error; it is not generic program safety.

The VOR-DATA/0 codec still cannot encode improper cons values or arbitrary
Unicode/wider integers. Those library evaluations are explicitly outside that
wire domain; no coercion or silent conversion was added.

`make program-demo` evaluates the single inert recursive append definition in
examples/program.shen and rechecks its witness. Expected result:
`[[value [a b c d]] [accepted evaluation]]`.
