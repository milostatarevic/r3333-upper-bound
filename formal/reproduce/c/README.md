# Reproduce the 456 C input identities

`Emit.lean` emits the exact signed unit suffixes from `Ramsey61.CConcreteFamily.seedLiterals`. Complete the mathematical build using [BUILD.md](../../BUILD.md), then run the following commands from the repository root. Set `proof_lib` to that successful build's isolated `lib/` directory and `archive_dir` to the extracted archive root containing `evidence/`. The temporary workspace supplies the existing parent directory required by the emitter; both output directories must be fresh.

```sh
cd formal
proof_lib="/absolute/path/to/successful/.build/runs/RUN/lib"
archive_dir="/absolute/path/to/extracted-archive"
work_dir="$(mktemp -d)"

in_proof_env() {
  lake env sh -c 'export LEAN_PATH="$1:$LEAN_PATH"; shift; exec "$@"' \
    sh "$proof_lib" "$@"
}

in_proof_env lean -j1 --run reproduce/c/Emit.lean "$work_dir/c-suffixes"
python3 -I -B reproduce/c/verify.py \
  --archive-dir "$archive_dir" \
  --emission-dir "$work_dir/c-suffixes" \
  --base-file "$archive_dir/evidence/c_campaign/inputs/BROAD_BASE_001.cnf" \
  --output-dir "$work_dir/c-check"
```

`--archive-dir` accepts either the archive root containing `evidence/` or that `evidence/` directory itself. All other file arguments are explicit. The verifier rejects Python optimization (`-O`), missing or extra suffix files, modified pinned evidence, changed literal signs/order, and inconsistent complete formula hashes, byte counts or clause counts.

The common base is already byte-bound to the mathematical generator. `EmitBase.lean` is an unmodified copy of the accepted base emitter, with its original comparison receipt in `checks/original_base_comparison.json`. It may be used to regenerate one fresh base file if desired. The C suffix verifier accepts either that byte-identical emission or the pinned archived base. The base emitter accepts a fresh output **file**, not a directory; use it in an independently created empty workspace.

The verifier clones the common base hash state when assembling each case's complete hash; it never writes 456 full CNFs. It checks all 197,544 signed unit clauses and all 929 retained result records: each of the 456 cases has two native UNSAT records, and the 17 earlier capped attempts retain their UNKNOWN status. These are input-identity and evidence-custody checks. They do not rerun SAT solving or turn native solver answers into proof certificates.
