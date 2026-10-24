# One-shot checker transport

After `make bootstrap`, run `python3 service/checker-launch.py CONFIG`.
CONFIG is a trusted Shen source file, resolved relative to the caller's directory.
See `config-example.shen`. Loading it executes code with full host authority; it
must never be selected or supplied by an untrusted request.

Input is a big-endian unsigned 32-bit byte count followed by exactly that many
bytes and EOF. The count is 1..8192 inclusive. The first body byte is an opaque
request ID; remaining bytes are one canonical VOR-DATA/0 artifact. The launcher
passes those bytes as inert hexadecimal argv data to a fixed Shen program.
Shen decodes symbols by matching the configured pre-existing symbol table;
unknown names cannot intern new host symbols. ASCII/u16 is the existing narrow
codec domain, not a FacilityGrid wire domain.

Successful transport emits exactly four bytes: `0x56 0x01 REQUEST_ID STATUS`.
STATUS is 0 checked, 1 rejected or violation, 2 unknown. These are results for
this invocation's configured root and exact claim; the response is not a
transferable certificate, signed attestation, or generic verification flag.
Only Shen checks the artifact, root, claim, and proof. The launcher validates
framing and response identity, never theorem validity.

A nonzero exit means no semantic result. Never interpret absent, partial, extra,
wrong-ID, or failed-child output as checked. Worker stdout is capped at four
bytes and diagnostics at 4096 bytes; worker execution and exit share a five
second deadline. Failure kills and reaps the owned process group. The launcher
also has a separate five second input deadline covering header, body and EOF.
The caller must impose an overall deadline and OS memory/CPU
limits appropriate to its environment. This is not a resource sandbox.

The supervisor must trust the complete checker source tree and the host binary
selected by the platform host-path file, as well as the configuration. The
overlay checksum only identifies that overlay; it does not attest the host or
source tree. Deploy these together as an immutable reviewed artifact.

The config is loaded in a fresh process after kernel setup and before request
decoding. It can redefine trusted code, so its review is part of the trusted
base. Authentication, concurrent requests, retry/recovery, full claim-bearing
responses, and the ShenCheck/BEAM mapping remain open work. This service is an
R01/R13 prerequisite and does not discharge implementation refinement.

`make test-service` runs positive and hostile semantic cases plus framing,
worker-output, failed-exit, and deadline cases. No production Rust peer or
second semantic checker is required.


The semantic corpus also exercises R03 closed-program evaluation witnesses.
The exact program, input, and outcome remain selected by trusted startup policy;
requests do not choose executable source to load. A checked evaluation of a
modeled error is a successful evidence check, not proof that an application
contract succeeded. The wire alphabet and proper-list/u16/ASCII limits are
unchanged; broader library values need an explicitly extended codec.
