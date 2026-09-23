# Reproduce the common A/B/mixed-D input binding

This tool emits the exact Lean-defined A/B prefix bodies and the 737-pair
common family's signed suffixes, then compares **all 55,016 complete inputs**
with the retained original search manifests. It runs no SAT solver.

The finite boundary is A 360, B 5,096, D/UTU 6,576, D/UTT 6,576,
D/TTU 18,204 and D/TTT 18,204. The two special D/UUU and D/UUT families
and C's 456 inputs have separate reproduction tools.

## Dependencies

Use the pinned native-proof Lean environment and its complete compiled
mathematical closure. The only supplemental pure helper is
`PricingABD.CommonSuffixCache`, supplied unchanged under `lean/`. Include
that module in the package's normal source/build roots. Its imports are
already in the final theorem's mathematical closure. The helper proves
that caching leaves the exact ordered suffix unchanged.

`Emit.lean` uses a runtime `main(args)`; compiling it does not emit files.
It accepts one fresh output directory. The comparator needs Python 3
with assertions enabled and rejects `python -O`.

The common tool also reads the separately generated D prefix bodies,
named `UTU_four.body`, `UTU_five.body`, and similarly for UTT, TTU and TTT.
No emitted CNFs or compiled build products belong in this tool package.

## Run

Complete the mathematical build using [BUILD.md](../../BUILD.md), then set
`proof_lib` to that successful build's isolated `lib/` directory.
`archive_dir` may be the extracted archive root containing `evidence/`, or
the `evidence/` directory itself.

```sh
native_proof_dir="/path/to/native-proof"
proof_lib="/absolute/path/to/successful/.build/runs/RUN/lib"
common_tools="/path/to/reproduce/common"
archive_dir="/path/to/extracted-archive"
d_prefix_dir="/path/to/emitted-d-prefixes"
work_dir="$(mktemp -d)"

cd "$native_proof_dir"
in_proof_env() {
  lake env sh -c 'export LEAN_PATH="$1:$LEAN_PATH"; shift; exec "$@"' \
    sh "$proof_lib" "$@"
}
in_proof_env lean -j1 --run "$common_tools/Emit.lean" "$work_dir/common"

python3 -I -B "$common_tools/verify.py" \
  --package-root "$common_tools" \
  --archive-root "$archive_dir" \
  --emission-root "$work_dir/common" \
  --d-prefix-dir "$d_prefix_dir" \
  --output-dir "$work_dir/check"
```

Emission creates 20 A/B prefix bodies and `COMMON_SUFFIXES.tsv`. It retains
all output. The comparator writes `COMMON_NATIVE_CASE_MAP.tsv` and
`COMMON_NATIVE_ALL_INPUT_BINDING.json` into a fresh report directory.

`path_index.json` relocates historical paths into these explicit roots.
The four original receipts under `original_receipts/` are byte-identical
to their accepted originals. The path index checks their hashes and the
hashes of the original native sources, manifests and prefix files; it does
not rewrite the receipts.

The comparator preserves the complete original domain, word, literal-order,
prefix, header, full-formula hash, byte-count, variable-count and clause-count
checks. It clones a SHA-256 state after each prefix rather than writing
55,016 full CNFs. The resulting identity is the hash of the exact complete
DIMACS bytes, including the original header.

## Validation

The fresh portable emitter and comparator passed for every input. The
emitter used 111.35 CPU seconds and 3.18 GB peak polled RSS; comparison used
4.31 CPU seconds and 0.91 GB. These are incremental reproduction costs with
the mathematical dependencies already built. A corrupted copied suffix
was rejected, and optimized Python was rejected before comparison.
Original outputs and all control logs were preserved. The smoke test used
the previously validated D-prefix output directory; the independent D tool
provides the same required file interface.

Successful input binding identifies the formulas whose native UNSAT answers
are supplied separately. It produces no new UNSAT answer or certificate.
