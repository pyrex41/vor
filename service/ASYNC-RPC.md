# Persistent local checker transport

`async_rpc.py` implements `async-wire/1` framing independently of the unchanged
one-shot service. The external caller supplies the trusted configuration,
source manifest digest, host executable digest, complete runtime bundle digest,
model and adapter identities. A request cannot select code or its own policy.
Configuration is executable trusted Shen: its reviewed dependency closure must
be part of the measured source image or pinned runtime/configuration package.
The OS and dynamically loaded system libraries remain trusted host assumptions.

The source identity is `source_identity(ROOT)` in the launcher: sorted tracked
paths, path length/path, file length and SHA-256, all with fixed big-endian
lengths. Runtime identity uses the same construction on relative regular-file
paths in the selected bundle and rejects symlinks. This binds the Chez boot
files as well as the executable. The operator must hold these files immutable
between measurement and execution; hashing is not a filesystem sandbox.

Start invokes fixed `vor.async.produce` and returns candidate bytes with UNKNOWN
status. Observe invokes fixed `vor.async.check` and alone supplies a semantic
verdict. Payloads are inert VOR-DATA byte sequences; no JSON, ETF,
artifact-selected function, or artifact-selected source is evaluated. The
example configuration checks the existing finite mutex claim, and is a
transport example rather than fenced-job qualification.

The protocol echoes session/run/request/source/model/adapter, nonzero nonce,
request-payload SHA-256 and exact resource limits. Accepted, invalid evidence,
UNKNOWN and definite violation have distinct tags. Duplicate request IDs,
changed session, malformed framing, missing data and oversized input fail
without a semantic reply. A new worker requires a fresh client nonce/session.
There is one in-flight request. The worker handles at most 256 requests.

A persistent Shen process loads trusted source once; each request supplies a
fresh history value. `--fresh` starts a new Shen process for each request.
Request input, worker execution and reply output each have bounded deadlines;
worker diagnostics have a cumulative 4096-byte cap. An independent guardian
kills the owned process group if its supervising launcher dies, including on
macOS. The guardian holds its process-group identity alive until cleanup, even when Shen
exits quickly. Cleanup kills the group before reaping the guardian, preventing
PID reuse from targeting an unrelated process group. This transport provides no
aggregate physical-memory or filesystem/network isolation. Operator policy
must apply the native resource controls appropriate for its qualification.

Run `python3 -m unittest discover -s tests -p test_async_rpc.py -v` after
bootstrap. Tests compare fresh/persistent results using real Shen evidence,
reject duplicates/malformed frames, enforce output/deadline limits, and kill a
worker after parent death. Tests are engineering evidence, not refinement.
