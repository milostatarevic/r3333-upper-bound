# Reproduce exact native input identities

Build the package using [BUILD.md](../BUILD.md). Use the `lib/` directory of
a successful complete build, including the two supplemental binding helpers.
The commands below select that isolated output explicitly; plain `lake build`
is not the mathematical build entry point for this source package.

Extract this repository's evidence archive using
the [reproduction guide](../../publication/REPRODUCIBILITY.md) before running
these checks. The archive path may name its outer directory or the `evidence/`
directory inside it. Run the following commands from the repository root;
`cd formal` selects the Lean package.

```sh
cd formal
proof_lib="/absolute/path/to/successful/.build/runs/RUN/lib"
archive_dir="/absolute/path/to/extracted-archive"
work_dir="$(mktemp -d)"

in_proof_env() {
  lake env sh -c 'export LEAN_PATH="$1:$LEAN_PATH"; shift; exec "$@"' \
    sh "$proof_lib" "$@"
}

in_proof_env lean -j1 --run reproduce/d/Emit.lean "$work_dir/d"
python3 -I -B reproduce/d/verify.py \
  --archive-dir "$archive_dir" --d-prefix-dir "$work_dir/d" \
  --output-dir "$work_dir/d-check"

in_proof_env lean -j1 --run reproduce/common/Emit.lean "$work_dir/common"
python3 -I -B reproduce/common/verify.py \
  --package-root reproduce/common --archive-root "$archive_dir" \
  --emission-root "$work_dir/common" --d-prefix-dir "$work_dir/d" \
  --output-dir "$work_dir/common-check"

in_proof_env lean -j1 --run reproduce/uuq/EmitUUQ.lean "$work_dir/uuq"
python3 -I -B reproduce/uuq/compare.py \
  --archive-dir "$archive_dir" --emission-dir "$work_dir/uuq" \
  --d-prefix-dir "$work_dir/d" --output-dir "$work_dir/uuq-check"
```

The shared D emitter writes twelve prefix bodies. The common-family verifier
checks 55,016 complete inputs, and the UUU/UUT verifier checks 1,358. They
reuse prefix hash states to verify complete DIMACS identities without writing
every full CNF. The C tools cover the separate 456-case family and its common
base; their usage is described in [c/README.md](c/README.md).

All output directories must be fresh. The tools retain outputs and fail on
hash, census, literal-order, sign, variable-count or clause-count differences.
They launch no SAT solver. Original receipts and their path/hash indices are
preserved; supplied input bindings and native UNSAT results remain distinct
pieces of evidence.
