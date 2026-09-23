# Exact C-base identity check

The Lean-defined deterministic C base emits exactly the archived
`BROAD_BASE_001.cnf`: **439,723 variables, 1,880,888 clauses and 39,604,154
bytes**. The complete DIMACS header, clause order, literal signs and variable
numbers agree in all ten clause families.

SHA-256: `58478e3641d3ea52639566683daaea5f7a1d4112de5809f4af73ce1dfebf164f`.

[comparison.json](comparison.json) records the byte comparisons and each
family's hash. [receipt.json](receipt.json) records the emission, source and
compiled-import pins. Emission used 6.70 CPU seconds and comparison used
2.83 CPU seconds. The [portable comparator replay](PORTABLE_COMPARISON.json)
checked the same retained files in 2.92 CPU seconds.

This check connects the generator used by
`Ramsey61.CEncodingBase.broaderBase_satisfiable_of_normalized_host` to the
archived deterministic base. It is an executable emission and byte comparison;
the theorem's mathematical semantics are checked by Lean. Physical seed
coverage and the additional seed units have their own arguments in
[the proof](../../../proof.md). No SAT solver is run by this check.

## Reproduce

Use the pinned Lean environment described in [formal/README.md](../../../formal/README.md)
and extract the evidence archive following [the reproduction guide](../../REPRODUCIBILITY.md).
From the repository root, set `snapshot` to that extracted directory and choose
a fresh output directory:

```sh
repo_dir="$PWD"
snapshot="/absolute/path/to/extracted/evidence"
binding_work_dir="$(mktemp -d)"
cd "$repo_dir/formal"
lake build Ramsey61
lake env lean -j1 --run \
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

The emission receipt pins `CEncodingBase.lean` at
`70973cf905034f9294e793b3f1932bfa18ea5d12759c088a263d16e7183ccf86`.
The supplied module's SHA-256 is
`9ba1a3051f64e785d422939ccbbff2ad8b2b83da82287c1dc96c5718f30a1186`.
[SOURCE_COMPATIBILITY.json](SOURCE_COMPATIBILITY.json) verifies that removing
exactly five diagnostic `#print axioms` lines from the receipted source gives
the supplied file byte for byte. Its declarations and six other imported
sources are unchanged.

The [receipted source](historical/CEncodingBase.lean), original receipts, log
and emitter are preserved byte for byte. Original
machine-specific driver scripts are retained in `historical/` as provenance;
the commands above and the parameterized comparator are the portable entry
points.
