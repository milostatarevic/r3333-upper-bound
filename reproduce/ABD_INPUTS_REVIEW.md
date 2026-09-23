# Independent source review: portable original A/B/D input reconstruction

Reviewer: `nonstar_cover_audit`; producer author: the parent agent. Reviewed
`abd_inputs.py` SHA256
`d5d42b3ce418a94a704978fda06fd3a07fdefa4877f99dc7a044c851577dca9b`.

Verdict: **GO for the stated exact-input-byte reconstruction scope.** This is
not acceptance of a new finite cover, native refutation, or formal proof.

The adapter pins each original manifest and case count; hashes the selected
shared prefixes; checks header/body/variable/clause dimensions; validates dense
units, suffix hashes and complete formula hashes; and keeps all source reads
within the supplied snapshot. For UUU/UUT, retained sparse bases and the exact
bijective dense maps recover the body. UUU additionally binds each historical
virtual formula hash to its pinned actual UNSAT native result. Reusing the UUT
manifest's pinned original-control metadata does not import UUT answers for
UUU; the separate original-base and result joins matter.

Output is create-only, outside the snapshot, with the 100 GiB disk floor and a
post-write hash check. Historical sources and original absolute paths are not
executed or opened. The receipt correctly denies mathematical-cover proof and
certificate checking.

Ten independent small tests in `test_abd_inputs.py` passed in 0.007 seconds:
good pinned bytes; bad digest; bad size; parent traversal; symlink source;
zero/out-of-range/repeated/conflicting/noninteger units; output inside snapshot;
wrong full-formula hash; wrong full-formula size; corrupted suffix hash. The
fixtures are synthetic and newly created; only those fixtures are cleaned up.

The producer's separately retained full check reports all 56,374 reconstructed
formula hashes passing in 3.738541 CPU seconds. I read its family counts and
ordered-digest receipt; I did not duplicate that full check. No solver, finite
mathematical census, original controller or certificate tool was executed in
this review.
