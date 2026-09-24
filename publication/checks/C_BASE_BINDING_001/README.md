# Exact C-base identity check

The Lean-defined deterministic C base emits exactly the archived
`BROAD_BASE_001.cnf`: **439,723 variables, 1,880,888 clauses and 39,604,154
bytes**. The complete DIMACS header, clause order, literal signs and variable
numbers agree in all ten clause families.

SHA-256: `58478e3641d3ea52639566683daaea5f7a1d4112de5809f4af73ce1dfebf164f`.

[comparison.json](comparison.json) records the byte comparisons and each
family's hash. [receipt.json](receipt.json) records the emission and comparison
using the published source manifest and the complete portable build's library.
The [complete input-binding record](../../../formal/checks/joined_bindings/RUN_RESULT.json)
includes this base check and the subsequent checks of all 56,830 formulas.

This check connects the generator used by
`Ramsey61.CEncodingBase.broaderBase_satisfiable_of_normalized_host` to the
archived deterministic base. It is an executable emission and byte comparison;
the theorem's mathematical semantics are checked by Lean. Physical seed
coverage and the additional seed units have their own arguments in
[the proof](../../../proof.md). No SAT solver is run by this check.

## Reproduce

Complete the pinned Lean build described in [formal/README.md](../../../formal/README.md)
and extract the evidence archive following [the reproduction guide](../../REPRODUCIBILITY.md).
From the repository root, set `snapshot` to that extracted directory and choose
a fresh output directory. Set `proof_lib` to the successful build's isolated
`lib/` directory:

```sh
repo_dir="$PWD"
snapshot="/absolute/path/to/extracted-archive"
proof_lib="/absolute/path/to/successful/.build/runs/RUN/lib"
binding_work_dir="$(mktemp -d)"
cd "$repo_dir/formal"
lake env sh -c 'export LEAN_PATH="$1:$LEAN_PATH"; shift; exec "$@"' \
  sh "$proof_lib" lean -j1 --run \
  "$repo_dir/publication/checks/C_BASE_BINDING_001/EmitBase.lean" \
  "$binding_work_dir/BROAD_BASE_FROM_LEAN.cnf"
cd "$repo_dir"
python3 -B publication/checks/C_BASE_BINDING_001/compare_base.py \
  --archived "$snapshot/evidence/c_campaign/inputs/BROAD_BASE_001.cnf" \
  --emitted "$binding_work_dir/BROAD_BASE_FROM_LEAN.cnf" \
  --output "$binding_work_dir/comparison.json"
```

The comparator checks the fixed base hash and length before comparing every
clause. It refuses an existing output and requires Python assertions to be
enabled. The emitter also refuses an existing destination. The roughly 40 MB
emitted file is kept in the chosen output directory; it is not duplicated in
this package.

## Source and receipt identity

The source manifest is SHA-256
`15b6775769f3578acd5c6aa22c46506decb3c041bd98912a79d50dd6e55ea8ed`,
the same manifest recorded by the [complete mathematical build](../../../formal/BUILD_RESULT.json).
The compiled `CEncodingBase.lean` source has SHA-256
`9ba1a3051f64e785d422939ccbbff2ad8b2b83da82287c1dc96c5718f30a1186`.
The emission uses the build's isolated project library with its pinned
dependencies. The [execution records](../../../formal/checks/joined_bindings/records.tar.gz)
retain the source and imported-artifact checks, exact command, log, timing
and byte-comparison result. The emitter and comparator here are the portable
entry points; no source-text compatibility transformation is required.
