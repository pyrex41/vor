# Fenced-job finite-history checking

The fixed `service/fenced-job-config.shen` loads the admitted R05 joint-tenant
profile, a candidate producer, the captured observation mapper, and an independent
native Shen certificate checker. Start requests return inert candidate bytes with
UNKNOWN status. Observe requests independently validate those bytes. The producer
never grants acceptance.

Histories are `[fj-history 0 Operations EffectObservations FinalObservation]`.
Each `[fj-op Id Action Predecessors Effect Response]` has a canonical integer ID
0..31, a constructor of the admitted `fj-action` sort, causal predecessors,
`applied|not-applied|unknown`, and `allow|deny|unknown`. Independent observations
are `[fj-effect Id Effect]`; every operation must have a resolved independent
observation before a history can be checked. Missing final observations remain
UNKNOWN. Raw operation retries must retain stable logical identity; an adapter
must not invent post-dispatch certainty.

The producer memoizes `(World, RemainingIds, StickyBad)` and emits a bounded DAG.
The checker validates the initial state, exact remaining set, causal acyclicity,
every eligible operation and mapper outcome, all outgoing edges, each independently
computed target, unique metadata, and reachability. It invokes `fj.next` for model
steps; there is no second job transition function. The mapper carries operation
identity and the entire payload unchanged and expands unknown into both effects.
The source-captured Coq theorem proves that narrow mapping property.

A final `[fj-final World]` expresses model-state consistency only. The specimen
uses `[fj-final [fj-snapshot 0 World CountsA CountsB]]`, where each count triple
is `[durable-results durable-outbox physical-sink-effects]`. Counts are independently
observed after the campaign is sealed and all connections are closed. The current
profile-specific trusted projection expects 0/0/0 for free/running states, 1/1/0
for completed undelivered states, and 1/1/1 for completed delivered states. It is
explicitly source-bound to this finite profile. Physical count 2 is retained and
cannot be collapsed into a boolean delivered flag. These projection rules are
trusted adapter code, outside the captured effect-mapper theorem.

No compatible leaf is a definite observation violation; all compatible bad leaves
are a response violation; mixed outcomes or unresolved effect observations remain
UNKNOWN. Every compatible good leaf plus complete observations establishes bounded
finite-history consistency. It does not establish generic application safety,
compiler correctness, storage refinement, or the open R14 implementation refinement.

Bounds: 32 operations, 512 nodes, 100000 edges, 256KiB wire payload, depth 128 and
65536 inert values. Resource exhaustion is UNKNOWN. Native execution/deadline/
cleanup qualification is independent from semantic checking.

Run `./scripts/shen -l tests/history-checker.shen -l tests/fenced-job-config.shen`.
The controls include omitted/duplicate/wrong edges, root tampering, causal cycles,
missing predecessors, closed actions, duplicate observations, unknown effects,
sticky badness, tenant omission, same-owner stale epochs, duplicate physical sink
effects, early acknowledgement, and missing observations. These are semantic
fixtures; generated real database discovery/replay is a separate campaign gate.
