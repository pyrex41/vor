# Effects-model signature: plan

Status: proposal for #15. Nothing here is implemented, and no acceptance
semantics change until each step lands with its own tests and negative checks.

## Goal

A consumer keeps its own authoritative Shen effects model. It plugs into the
existing exporter, TLA generation, reference/TLC qualification and history
checking by declaring an **effects-model signature**: inert data, never
evaluated code. `examples/effects-protocol.shen` becomes one instance of the
signature, not a special case.

## Signature value (VOR/0-compatible first cut)

```text
[effects-signature 0
  [model <VOR/0 model value>]                     \\ unchanged; still the authority
  [properties [<name> <expr>] ...]                \\ conjunction must equal the model invariant
  [roles [<role> <variable>] ...]                 \\ mutation | obligation | lease | worker-knowledge
                                                  \\ | sink | response; advisory to tooling only
  [mutants [<mode> <rule-label> <replacement-rule> <expected-property>] ...]]
```

The first cut keeps VOR/0 Boolean state. Typed finite domains (enumerations,
bounded integers, records, keyed maps), parameterised actions, fairness and
temporal properties are later steps. Each later step needs its own encoding,
bounds, and translation obligations.

Well-formedness, checked by the admitted Shen definition and independently by
the consumer:

1. `model` passes the existing VOR/0 checks.
2. The property names are distinct symbols. Their ordered conjunction is
   structurally equal to the model's invariant, so naming the properties
   cannot change what is checked.
3. Each role names a declared variable. Roles are documentation for adapters
   and history projection. They never weaken or replace a property.
4. Each mutant replaces exactly one existing rule label and keeps the action
   skeleton. Its expected property must be declared. The mutant model is
   derived from `model` by that one replacement, never supplied separately.

## What changes downstream

- Exporter: `--signature <file> --mode healthy|<declared mutant>`. The healthy
  model and each mutant are derived from the signature. The exported envelope
  carries the signature and its source identities.
- TLA generation: one `INVARIANT` per declared property, using the declared
  name rather than a conjunct index. The name is rendered through an indexed
  alias table, so user names cannot inject TLA syntax.
- Qualification: the cohort is healthy plus every declared mutant. A mutant
  matches only if both the reference explorer and TLC report a violation and
  TLC names the mutant's expected property. A missing or extra mutant, an
  unparseable name, or an incomplete reference search is UNKNOWN, never
  validation.
- History checking: unification with the fenced-job format stays with #3 and
  the later history step. It is not part of the first cut.

## Steps

| Step | Change | Acceptance |
| --- | --- | --- |
| S1 | Signature datatype and well-formedness in Shen. The example declares its 7 properties and 4 mutants. | The example's exported model is byte-identical to today. A negative corpus covers a mismatched conjunction, an unknown variable, a duplicate name, an unknown rule label and an undeclared expected property. |
| S2 | The exporter accepts a signature file and declared modes. The fixed `--mode` list is derived from the signature. | The existing export tests pass. A long-list signature round-trips. A consumer-supplied file is never evaluated. |
| S3 | ShenCheck consumes the declared property names and mutant expectations. | Qualification fails when a mutant violates the wrong property, and is UNKNOWN on missing data. |
| S4 | A non-trivial instance: two tenants, two workers, lease generations, and two sinks with different contracts. It needs finite domains or a Boolean encoding with stated bounds. | The healthy model qualifies, every mutant names its property, and the bounds are part of the model's identity. |
| S5 | Fairness and temporal properties, exported as `PROPERTY` with named fairness conjuncts. | Liveness stays a separate OPEN or checked claim. It never upgrades a safety result. |

## Claims stay separate

Finite model safety, observed-trace conformance, general inductive safety,
liveness under named fairness, multi-request composition and implementation
refinement remain distinct obligation lines. Declaring a signature establishes
none of them by itself.
