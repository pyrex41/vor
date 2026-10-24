# One-shot inert checker service (R01/#3, R13 transport prerequisite)

This increment adds a bounded, one-request process boundary for the existing
R01 claim families. It does not add generic admission, implementation
refinement, concurrent observation, or complete R13 transport semantics.

## Trust and authority

The launcher receives a trusted startup configuration containing the exact
root, expected claim, allowed pre-existing symbols, and independent limits.
Those values are selected before reading the request and are never replaced by
request fields. The fixed Shen checker remains the semantic authority; the OS
shim only enforces framing, launch, lifetime, and stdout discipline.

## Wire and lifetime

The service accepts exactly one bounded length-prefixed binary request followed
by EOF and emits exactly one bounded binary result. Fragmentation is ordinary
stream behavior; truncation, trailing bytes, unknown framing, and oversize
frames reject. Artifact bytes are inert data and are decoded by the fixed
restricted codec, never loaded, read as Shen source, evaluated, or used to
extend the kernel. A fresh one-shot process bounds untrusted symbol state;
the launcher enforces separate input and worker deadlines, and callers must
impose an overall wall-clock and OS resource timeout.

The initial domain remains VOR-DATA/0 (ASCII symbols and unsigned u16 values),
not FacilityGrid identifiers or a general-purpose service protocol.

## Compatibility boundary

The existing `vor.pack`/`vor.unpack` API remains an explicit trusted-host
compatibility path. The service uses a restricted known-symbol decoder that
rejects unknown symbol text before `intern`; this is not a claim that the
legacy in-process codec is safe for hostile long-lived input.

## Evidence and exit gate

The process corpus independently drives a reference frame encoder and checks
healthy, wrong-root/claim, forged acceptance, executable-looking payload,
unknown-symbol, fragmentation, truncation, trailing, oversize, depth/node,
and proof-budget cases. It captures raw stdout and proves that a failed
process emits no extra result. Full existing tests and demos remain required.

Open limits: semantic soundness, compiler/host preservation, process resource
isolation, authentication, retry/recovery, concurrent mapping, and all wider
wire domains remain future obligations.
