# Reproduce the 456 C input identities

`Emit.lean` emits the exact signed unit suffixes from `Ramsey61.CConcreteFamily.seedLiterals`. Use the pinned Lean environment and prepend the completed mathematical build's `lib/` directory to `LEAN_PATH`, as described in the package's build/reproduction instructions. The output directory's parent must exist; the emitter atomically creates the fresh output directory and refuses an existing one.

```sh
lean -j1 --run Emit.lean /absolute/path/to/fresh-c-suffixes
python3 verify.py \
  --archive-dir /absolute/path/to/extracted-evidence-archive \
  --emission-dir /absolute/path/to/fresh-c-suffixes \
  --base-file /absolute/path/to/extracted-evidence-archive/evidence/c_campaign/inputs/BROAD_BASE_001.cnf \
  --output-dir /absolute/path/to/fresh-c-verification
```

`--archive-dir` accepts either the archive root containing `evidence/` or that `evidence/` directory itself. All other file arguments are explicit. The verifier rejects Python optimization (`-O`), missing or extra suffix files, modified pinned evidence, changed literal signs/order, and inconsistent complete formula hashes, byte counts or clause counts.

The common base is already byte-bound to the mathematical generator. `EmitBase.lean` is an unmodified copy of the accepted base emitter, with its original comparison receipt in `checks/original_base_comparison.json`. It may be used to regenerate one fresh base file if desired. The C suffix verifier accepts either that byte-identical emission or the pinned archived base. The base emitter accepts a fresh output **file**, not a directory; use it in an independently created empty workspace.

The verifier clones the common base hash state when assembling each case's complete hash; it never writes 456 full CNFs. It checks all 197,544 signed unit clauses and all 929 retained result records: each of the 456 cases has two native UNSAT records, and the 17 earlier capped attempts retain their UNKNOWN status. These are input-identity and evidence-custody checks. They do not rerun SAT solving or turn native solver answers into proof certificates.
