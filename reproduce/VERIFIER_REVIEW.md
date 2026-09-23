# Independent source review: portable archive verification and C reconstruction

Reviewed source: `verify.py`, SHA256
`6e9eb01764647e3fa3e721822bab722f29c10b599ef3aa158eab24bc977faba4`.
Independent reviewer: `star_triangle_hand_review`. Producer:
`nonstar_cover_audit`. This record preserves the reviewer's completed source
assessment; the reviewer did not execute the program or its tests.

Verdict: **GO for archive/custody verification and exact C-formula-byte
reconstruction. No material source defect found.**

The reviewer confirmed that the entrypoint authenticates the release archive
before extraction; rejects traversal, links, devices, sparse and duplicate
members; writes into a new destination; pins the archived verifier and index
before isolated `-I -B` execution; and requires the receipt outside the
snapshot. C reconstruction uses the original physical edge rank
`u*(121-u)/2 + v-u-1`, original signed-unit order, adjusted DIMACS header and
the exact accepted formula SHA256.

This verifies bytes and recorded custody, not UNSAT validity or unproved formal
bridges. The documentation preserves that boundary. The whole 455,901-file
check is a separate execution, not implied by this source verdict.

Author checks already completed when reviewed: 19 synthetic positive/negative
tests passed in 0.017 seconds; the released archive hash passed in 0.154056 CPU
seconds; and C/R3_000 was reconstructed and independently rehashed in 0.104349
CPU seconds. No solver, certificate or finite mathematical census ran. The
synthetic tests clean up only their own newly created temporary fixtures.
