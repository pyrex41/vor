# Exact claims and inert artifacts (R01 foundation)

The claim boundary binds the VOR/0 and propositional APIs and the R02
first-order extension described below. The boundary itself does not implement
generic Shen program admission, compiler preservation, implementation refinement,
or the proof rules; it delegates to the selected semantic kernel. R01's generic obligations
and the existing soundness obligations remain open.

## One expected claim, one submitted witness

```text
[vor-root 0 RuleIdentity HostIdentity]
[vor-claim 0 Root Subject Dependencies Assumptions Domain Judgment Kind]
[vor-evidence 0 ExactClaim Evidence]
```

RuleIdentity and HostIdentity are nonempty strings selected by the verifier.
The root is an identity label, not an authenticated manifest or a measurement
of the current image. A dishonest host can lie about it or redefine the checker.
A production release still needs R15's artifact binding and sealed image.

Dependencies and Assumptions are ordered lists of `[Name InertValue]`, with
unique non-Boolean symbol names. Order is part of identity. No normalization,
hash equality, name lookup, dynamic loading, or dependency resolution occurs.
These values retain declared metadata; they do not prove that a dependency
implements a contract or that an environmental assumption is true. Transitive
admission and assumption composition remain future work.

The application supplies Root and Expected from its trusted configuration:

```shen
(vor.check-claim Root Expected Artifact ProofDepth)
```

The verifier validates the expected claim, checks its root against the trusted
root, and requires complete structural equality with the artifact's claim before
checking Evidence. Never select Expected or Root from the submitted artifact
as authority. Equality alone is not proof: the semantic checker rechecks the
payload, including when the claim matches. A submitted accepted/checked record
cannot bypass this path.

| Subject | Domain | Judgment | Kind | Payload checker |
| --- | --- | --- | --- | --- |
| `[model M]` | `boolean-states` | `[invariant]` | `finite-proof` | `vor.check-certificate M Evidence` |
| `[model M]` | `boolean-states` | `[trace-prefix T]` | `trace-check` | Exact equality with T, then `vor.trace` |
| `logic` | `intuitionistic-propositions` | `[derives G P]` | `concrete-derivation` | `vor.proof G P Evidence ProofDepth` |

Models, formulas, and contexts must already meet their existing closed grammar.
The R02 extension additionally accepts subject `[first-order Sig Vars]`, domain
`constructive-first-order`, judgment `[derives Gamma Target]`, and kind
`concrete-derivation`, checked by `vor.fol-check` with the supplied proof fuel.
The exact signature, free-variable scope, context, and conclusion are bound.
See LOGIC.md for its fixed rules and reserved induction premise.

Unsupported subjects, domains, kinds, and judgments are rejected, including
`generic-proof` and arbitrary Shen source definitions. Exact model identity
includes the invariant and every rule. The trace is part of its expected claim,
so replacing it with a shorter safe prefix changes the claim.

Success is `[checked ExactClaim OriginalAcceptance]`; rejection, violation, and
uncertainty remain distinct and are not wrapped as success. An invariant claim
is about all reachable states of this finite model, a trace claim is about one
prefix, and a propositional derivation is about its explicit context. None is
implementation refinement. Returned lists are data, not opaque capabilities;
consumers must recheck evidence rather than trusting a supplied success record.

`vor.typecheck-claim Root Expected Artifact` checks the indexed System S judgment
`[vor-bound-evidence Root Expected]`. Its datatype rule decodes literal cons
syntax without evaluation, then delegates to the same claim checker (proof depth
1000). This is not an independent proof kernel or a proof of rule soundness. The public
wrapper prechecks evidence and propagates unknown before inference, including
exhaustion of its fixed proof limit.

## Bounded inert byte-list grammar

`kernel/artifact.shen` defines VOR-DATA/0, a closed binary value encoding over a
proper list of byte integers. It does not use Shen's source reader, evaluator,
compiler, or loader. There is no byte-stream/stdin framing service, Rust codec,
handshake, authentication, concurrent-history mapping, or effect adapter yet;
those remain issue #3's separate work.

| Tag | Representation | Meaning |
| --- | --- | --- |
| 0 | one byte | empty list |
| 1 | one byte | false |
| 2 | one byte | true |
| 3 | tag + two bytes | unsigned integer, big endian, 0..65535 |
| 4 | tag + u16 length + bytes | nonempty printable ASCII symbol, bytes 33..126 |
| 5 | tag + u16 length + bytes | ASCII string, bytes 0..127, including empty |
| 6 | tag + u16 count + values | nonempty proper list |

The empty list has only tag 0. Symbols must round-trip through `intern`/`str`
and cannot alias Booleans. Numeric strings and actual integers remain different
value kinds when the host preserves that distinction. There is no signed,
floating-point, Unicode, or arbitrary-precision integer encoding in this version.
Integers above 65535 are explicitly rejected, not coerced or rounded. The wider
wire domains required by #3 need a versioned extension and their own evidence.

```shen
(vor.pack Value ByteLimit DepthLimit NodeLimit)
(vor.unpack Bytes ByteLimit DepthLimit NodeLimit)
(vor.check-artifact Root Expected Bytes ByteLimit DepthLimit NodeLimit ProofDepth)
```

Successful pack/unpack return `[ok Value]`. Decode must consume all bytes;
trailing data, unknown tags, malformed text, improper byte lists, unsupported
representations, and truncation cannot produce an accepted value. The caller
must supply a complete byte list; partial chunks are not separate requests.

Limits are positive naturals capped at 1,048,576 bytes, depth 256, and 65,536
value nodes. Depth and nodes count the root and every list element; list header
lengths do not authorize further work beyond these budgets. Exhausted depth or
node budgets produce explicit `unknown`, not acceptance or proof of invalidity.
Byte-list validation refuses oversized input. These are syntactic limits, not
proved bounds on CPU time, host stack, allocation, symbol-table growth, or the
cost of the subsequent semantic checker. Process isolation/resource limits and
long-running service lifecycle remain deployment obligations. The encoder takes
finite in-memory values; it is not an arbitrary-host-object sandbox.

`vor.check-artifact` decodes then rechecks the envelope against the separately
provided expected claim. No artifact text is loaded as executable Shen. Error
handlers return uncertainty instead of success; they cannot guarantee recovery
from process death or allocation failure.

## Tests and remaining theorem obligations

The corpus checks every proper prefix of a complete envelope, all 256 one-byte
tag inputs, independent exact byte vectors, boundary integers, precise budget
edges, model/dependency/assumption/judgment substitutions, forged acceptance,
System S binding, and executable-looking payloads with a mutation sentinel.
A transient-invariant violation remains visible even after a repair step; raw
partial observations retain their original documented uncertainty scope.

These tests are engineering evidence. They do not discharge:

- Identity binding, assumption retention, and report-composition theorems.
- Codec round-trip/canonicality and termination theorems.
- Public indexed-judgment correspondence and checker soundness.
- Generic program admission, dependency closure, or host preservation.
- Observation-map adequacy, fault semantics, or concrete refinement.

The fixed datatype rule and new executable side conditions enter the trusted
source inventory. No artifact may introduce rules to justify itself.


## R03 normalization and execution claims

Subject `[program P]`, domain `admitted-shen-0`, judgment
`[evaluates Name Args Outcome]`, kind `concrete-derivation` checks an exact
finite evaluation witness. Subject `[source Source]` with judgment
`[normalizes P]` checks the exact normalization certificate. The program binds
its original source and normalized definitions; code, inputs, and outcome may
not be substituted. Checker fuel uncertainty remains unknown through the typed
wrapper and process service. A checked modeled error is an evaluation fact,
not application-contract success. See PROGRAM.md for all limits.
