# Additive independent review: all 456 exact C input hashes

Reviewed source: `verify.py`, SHA256
`6782e2f9073d502bcd7b0247952ba29fb0ace2af2305e5f6d528800ffeddcaf9`.
Independent reviewer: `star_triangle_hand_review`. Producer:
`nonstar_cover_audit`. This extends the archived review of the preceding
version; archive checking, extraction, full verifier invocation and
single-case materialization are unchanged.

**Verdict: PASS for the new `verify-c-all` byte-reconstruction operation.**
The review was source-only, without executing the program.

The reviewer confirmed exact pins for manifest, acceptance and base; explicit
ordered 456 seed/acceptance IDs and unresolved rejection; separate adjusted
header hash states for each unit count; consumption of the exact headerless
base; original positive/negative unit order; copied hash states for every
suffix; matching of all 456 accepted formula hashes; and the logical-byte sum.
No formula file is generated, and the CLI keeps its receipt outside evidence.

The actual all-input execution passed in 0.239967 CPU seconds, representing
18,060,823,116 logical bytes without writing those bodies. Four additional
synthetic tests cover a shared-prefix success, a missing final seed, a wrong
R3_455 formula hash and an unresolved acceptance. All 23 verifier tests passed
in 0.029 seconds. These measurements are producer execution evidence, separate
from this independent source verdict. No solver, certificate or finite
mathematical computation was run.
