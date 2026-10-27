# Bind the Lean formulas to native inputs

These tools compare the complete Lean-defined boundary with all **56,723 native formulas**. They check case coverage, signed literal order, dimensions, byte counts and full DIMACS SHA-256 identities. They do not run a SAT solver.

Complete the full [source build](../../BUILD.md) and generate the current input catalogue as described in [reproduce/README.md](../README.md). Run from `formal/`:

```sh
lake env python3 reproduce/uniform/run_binding.py \
  --build-dir /absolute/path/to/successful/.build/runs/RUN \
  --inputs /absolute/path/to/uniform-inputs \
  --output-dir /absolute/path/to/fresh-binding-run
```

The output directory must not exist. The driver checks the current source manifest, every module receipt and compiler log, the exact compiler and locked dependency runtime, and all accepted project artifacts. It constructs its library path from the selected build and pinned dependencies.

Before emission, `Audit.lean` checks the exact whole-proof theorem type with its sole indexed UNSAT premise and the 56,723-case count. Its two axiom reports may contain only `propext`, `Classical.choice` and `Quot.sound`.

| Family | Cases | Exporter and comparator |
|---|---:|---|
| A/B/D common catalogue | 55,016 | `EmitCommon.lean`, `check_common.py` |
| D/UUU and D/UUT | 1,358 | `EmitMarkedUU.lean`, `check_marked_uu.py` |
| Direct C entrances | 346 | `EmitCEntrance.lean`, `check_c_entrance.py` |
| Globally balanced hosts | 3 | `EmitBalanced.lean`, `check_balance.py` |

The C exporter also emits the shared 156,770-clause physical base. The common and marked-UU exporters emit complete ordered signed unit lists. Their comparators reconstruct each complete formula hash using the shared base. The balanced exporter writes all three 13,656-variable, 524,462-clause formulas in full.

`CommonUnitCache.cached_eq` and `BalancedEncoding.fastFormula_eq` prove that the evaluated cache representations equal the exact ordered formula definitions. The marked-UU and C exporters directly evaluate their physical-unit definitions.

The marked-UU comparator uses the flat physical case table at `reproduce/data/marked_uu.json` from the repository root; the driver selects that table by default and records its identity. An explicit `--case-table` argument selects the same data in another location.

`check_all.py` requires the four families to form the exact disjoint union, the Lean and native bases to agree, and every component to use the same catalogue. It also accepts separately emitted files through its command-line interface. That standalone comparison checks bytes and coverage; the driver additionally identifies the build and runtime that executed the emitters.

The driver retains `FINAL_THEOREM_AUDIT.json`, execution logs, emitted files, component comparison records and `RUN_RESULT.json`. It rechecks the input, source, log, compiler and artifact identities after execution. Failed checks retain their records and do not overwrite an earlier run.

The repository's `reproduce/uniform_release.py` joins a successful complete binding to the exact native result census. Its release verifier checks the retained package using the current repository's verification code. The serializer, execution and hash comparison are external checks; they are distinct from Lean's mathematical proof and from native UNSAT evidence.
