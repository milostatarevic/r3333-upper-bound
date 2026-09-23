# Review and execution of the portable finite G replay

The unchanged mathematical checker sources are pinned inside `g_check.py`:
the isomorphic-map checker has SHA256
`6944bd1ed614d7db9e31bce5cbed9520190ba96507ae106cec2bef0683986ac5`,
and the remaining-G checker has SHA256
`1ebf555cf5f0bb268b5412735747c361c6a43e2e36173a2d6f073b4f41347192`.

Separate AI-agent source review by `star_triangle_hand_review` approved the
adapter's authenticated copying, unchanged function entry points, complete
local-relation reconstruction and both exhaustive witness checks. Root also
inspected the adapter. The only change after the initial reviewed adapter
was renaming an output metadata field to `free_assignments_checked`; the
executed adapter SHA256 is
`bededef642ba40bd55fbb9f7d64a415c8f787d6e133ba745337a1d858f9793ef`.
No checker function or mathematical input was patched.

The actual run used the fresh authenticated public-verifier extraction and a
new output directory. It exited zero with PASS. It reconstructed rank 65,
nullity 15 and all 32,768 assignments of nonzero free coordinates over F3,
obtaining the 72-state relation byte-identical to the retained reference.
All 3,600 isomorphic-map and 10,368 remaining-G labels were rejected by
checked finite witnesses; the 11 and 19 checker controls passed.

Measured process CPU was 2.177987 seconds, wall time 2.208656 seconds and
peak RSS 40,386,560 bytes. The process CPU ceiling was 60 seconds, with no
wall deadline. The 100 GiB disk floor was preserved. RSS is checked between
bounded stages, not claimed as a continuously enforced macOS memory kill.

The exact execution and output pins are in
[REPLAY_RECEIPT.json](checks/G_REPLAY_001/REPLAY_RECEIPT.json), SHA256
`23ea573358654e2cca3f444aade091105aa469bfb4d8ff222fdf442d5abddf88`.
Fresh checker outputs are retained alongside it; unchanged parent inputs
remain in the evidence archive rather than being duplicated here.

This reproduces finite contradictions used by the guarded G lemma. It is
not a new SAT run, a new whole-C exclusion, external peer review, or a Lean
certificate for the Ramsey theorem.
