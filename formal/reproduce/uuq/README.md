# Reproduce the original UUU/UUT input binding

These tools reconstruct the exact inputs for both 679-case owners: 189 P15,
408 restricted D9, and 82 D10 cases each. They emit the small signed suffixes,
combine them in memory with supplied native D prefix bodies, and check all
1,358 complete sparse/native input hashes against the retained UNSAT records.
They do not run a SAT solver or replay certificates.

## Prerequisites

Use the final proof package's Lean 4.32.1 environment and pinned dependencies,
with `PricingG.UUQEmissionIdentity` and its dependency closure compiled.
`source_inventory.json` records the current 586-module source closure and pins
the [source manifest](../../SOURCE_MANIFEST.json). Its module hashes and byte
counts match the current package sources. This inventory is documentary;
the emitter and comparator do not read it.
`EmitUUQ.lean` is a runtime `main`, so importing/compiling it writes no files.
Python 3.9 or newer is sufficient for the comparator; `-O` and `-OO` are rejected.

Supply the extracted evidence archive, the four relevant native prefix bodies
(`UUU_four.body`, `UUU_five.body`, `UUT_four.body`, `UUT_five.body`), and two fresh
output directories. The shared D-prefix emitter can produce all twelve bodies;
this checker uses the four above. `--archive-dir` accepts either the outer
extraction directory containing `evidence/`, or that `evidence/` directory itself.

From the package root, select the successful isolated build described in
[BUILD.md](../../BUILD.md), adjusting the explicit input and output paths:

```sh
proof_lib="/absolute/path/to/successful/.build/runs/RUN/lib"
in_proof_env() {
  lake env sh -c 'export LEAN_PATH="$1:$LEAN_PATH"; shift; exec "$@"' \
    sh "$proof_lib" "$@"
}
in_proof_env lean -j1 --run reproduce/uuq/EmitUUQ.lean run/uuq_suffixes
python3 reproduce/uuq/compare.py \
  --archive-dir path/to/extracted_archive \
  --emission-dir run/uuq_suffixes \
  --d-prefix-dir run/native_d_prefixes \
  --output-dir run/uuq_binding
```

The emitter atomically claims a fresh final directory and writes twelve TSV
files: sparse and native suffixes for each of six families. A completed valid
comparison writes create-only, read-only `BINDING.json` and a separate
`PATH_HASH_INDEX.json`. A rejected input receives `REJECTED.json`; no passing
binding is written. Existing output directories are refused.

## Exact scope

`PricingG.UUQEmissionIdentity.emitted_eq` proves that the emitted sparse
representations are the formulas consumed by `PricingG.UUQExactNative`.
Native renaming uses the same proved `DNativeMaps` maps as the final theorem.
The checker verifies complete clause order and both literal signs, the original
case and Q-type indices, map inversion, complete formula hashes, and the input
hashes and terminal UNSAT status of each retained native result. The original
D10 census records complete formula hashes; P15 and D9 also record their unit
lists. Both formats are checked explicitly.

`reference_index.json` is the immutable, relative path/hash index for all
referenced archive records. It is derived from the already accepted 1,358-case
binding and terminal reconciliation; its provenance hashes are included.
The reproduction preserves the original trust boundary: the Lean mathematics
and exact input binding are checked, while the large search refutations are
supported by native solver results.

The [current complete input-binding result](../../checks/joined_bindings/RUN_RESULT.json)
records the package-wide verification. Existing validation receipts retain the
inventory and documentation hashes recorded for their earlier runs.
