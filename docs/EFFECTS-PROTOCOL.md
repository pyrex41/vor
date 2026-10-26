# Request-to-effects protocol

`examples/effects-protocol.shen` is the authoritative executable VOR/0 model
for a small durable effects lifecycle:

```text
request commit -> response -> claim -> expire or apply effect -> finish
```

The model intentionally keeps response before or after worker completion
possible. A response requires the mutation to be durable; completion requires
an effect, acknowledgement, and an active lease. Expiry and crashes remove the
lease. A lost acknowledgement can be followed by a retry, while a duplicate
sink application is an explicit unsafe mutant. The Boolean model does not yet
carry worker token/generation identity, so stale-worker fencing is an explicit
refinement obligation. It also does not claim SQL atomicity,
external-provider idempotency, liveness, or refinement of the target application.

Run the focused checks with:

```sh
make test-effects-protocol
./scripts/export-effects-model --mode healthy --output .work/effects-model.json
```

`export-effects-model` invokes the trusted Shen definition and serializes its
inert model value to `vor-effects-model-v1`. It refuses to overwrite an output,
uses bounded process/output limits, and records source hashes for the model,
kernel, launcher, toolchain, and PR117 overlay when present. The `verification` field is informational metadata;
the consumer must run its own checker. `broken-commit` and `broken-finish`
exports are available for negative controls.

The finite certificate result establishes only that the exact Boolean model's
reachable states satisfy its invariant. It is not a proof that the application
implements the model. Implementation refinement, SQL isolation, crash
durability, provider behavior, general induction, and temporal progress remain
open obligations.
