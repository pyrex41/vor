# Admitted fenced-job profile

`adapters/fenced-profile.shen` is the authoritative finite transition program.
Its 71 definitions use the existing R05 constructor, local-variable and earlier
call fragment. `fj.admit` checks exact source, construction and quantified type
contracts; the postconditions are `top`. This proves totality/type formation
relative to the construction root, not a generic fencing invariant theorem.
History checking evaluates this same admitted program; there is no Rust job
state machine.

The profile has two tenant slots for the same logical job key, two worker
identities, epochs 0/1, logical live/expired leases, two payload identities and
two stable completion operation identities. The external adapter policy must
bind concrete tenant/job/payload/operation identities to these constructors.
The profile has 33 slot constructors and 45 joint actions. Exhausting epoch 1
returns UNKNOWN; it never wraps or silently rejects a valid unbounded claim.
This is a qualification profile, not the application's storage integer range.

A claim can acquire a free or expired job. Completion must match owner, epoch,
live lease and payload; it atomically constructs completion, saved result and
outbox. A retry with the same operation and payload returns the retained result;
conflicting operation or payload is denied. Tenant actions preserve the other
slot. Delivery is separate, requires a durable outbox, and uses the logical
job/payload identity independently of attempt/epoch. A second identical delivery
has the same sink state; a conflicting payload is denied.

`fj.session-start` checks admission and caches the exact immutable program,
signature, contracts and result in trusted startup globals. `fj.next` accepts
only inert action/world values, checks their algebraic domains, evaluates that
frozen program and rechecks the concrete execution witness. It returns
`[next allow World]`, `[next deny World]`, or explicit unknown/rejected data.
The host must preserve the reviewed image and cache globals; artifacts cannot
supply code, cache contents or an alternate model.

Run `./scripts/shen -l tests/fenced-profile.shen` for admission, tenant-frame,
owner/epoch/lease controls, atomic completion/outbox, sink idempotency, retry
conflicts, bounded-epoch uncertainty and forged-admission rejection. These
engineering checks do not establish Erlang/PostgreSQL implementation refinement.
