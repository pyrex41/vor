# Request-to-effects protocol

`examples/effects-protocol.shen` is the authoritative executable VOR/0 model
for a small durable effects lifecycle:

```text
request commit -> response -> claim -> expire or apply effect -> finish
```

The model intentionally keeps response before worker completion possible. A
response requires the mutation to be durable; completion requires an effect and
an active lease. Expiry removes the lease, so a stale worker cannot apply an
effect. A retry is represented by another claim after expiry. The Boolean model
does not claim SQL atomicity, arbitrary worker identity, external-provider
idempotency, liveness, or refinement of the target application.

Run the focused checks with:

```sh
make test-effects-protocol
./scripts/export-effects-model --mode healthy --output .work/effects-model.json
```

`export-effects-model` invokes the trusted Shen definition and serializes its
inert model value to `vor-effects-model-v1`. It records source hashes for the
model and VOR kernel files. The `verification` field is informational metadata;
the consumer must run its own checker. `broken-commit` and `broken-finish`
exports are available for negative controls.

The finite certificate result establishes only that the exact Boolean model's
reachable states satisfy its invariant. It is not a proof that the application
implements the model. Implementation refinement, SQL isolation, crash
durability, provider behavior, general induction, and temporal progress remain
open obligations.
