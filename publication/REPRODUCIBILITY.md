# Reproduce the proof computations

Run the following commands from the repository root unless stated otherwise.
The native input and evidence tools use Python 3.9 or later and its standard
library. The Lean build and binding driver require Python 3.10 or later and
the pinned toolchain described in [formal/BUILD.md](../formal/BUILD.md).

The proof has 56,723 mathematical cases and two native executions per case.
A second solver provides an independent execution of the same formula; it
does not increase the mathematical case count.

## Check the retained release

Fetch and authenticate the Git LFS payloads:

```sh
git lfs install --local
git lfs pull --include='archives/*.tar.gz'
shasum -a 256 -c archives/SHA256SUMS
```

`evidence-v1.tar.gz` supplies authenticated finite support and word data.
`evidence-v2.tar.gz` contains the current input catalog, all required native
results, and the mathematical build and exact-binding records. Archive names
are stable data locators. The current proof boundary is specified by the
current catalog and `RELEASE.json`.

Extract the authenticated release into a fresh directory and run the
current repository's verifier:

```sh
proof_work_dir=$(mktemp -d)
mkdir "$proof_work_dir/evidence-v2"
tar -xzf archives/evidence-v2.tar.gz -C "$proof_work_dir/evidence-v2"
python3 -B reproduce/uniform_release.py verify-package \
  --root "$proof_work_dir/evidence-v2" \
  --formal-root formal \
  --output "$proof_work_dir/release-verification.json"
```

This checks all 113,446 native outcomes and their exact formula identities,
raw logs, commands, solver binaries, exit codes and resource records. It
also checks the matching source manifest, complete build records, final
theorem audit, and exhaustive formula-binding result. The supplied proof
sources must match the package's mathematical manifest. No Lean compiler or
SAT solver is launched by this command, and archived scripts are not executed.
Write new reports outside the evidence directory; its exact file census is
part of the check.

The release preserves native execution records under `sources/abd/`,
`sources/c/` and `sources/balance/`, retaining their original local identifiers
and commands.
The verifier checks their complete mapping to the one current input catalog.
`math/build/` and `math/binding/` retain the mathematical verification records.
The [release checks](RELEASE_CHECKS.md) describe the scope of each result.

## Reconstruct every current formula

Generate a fresh complete catalog from the authenticated finite data:

```sh
python3 -B reproduce/uniform_k61.py prepare \
  --archive archives/evidence-v1.tar.gz \
  --output "$proof_work_dir/fresh-campaign/inputs"
```

The output directory must not exist. It contains a shared `base.clauses`,
`cases.jsonl.gz`, `MANIFEST.json`, and three complete balanced CNFs. Catalog
rows record stable indices, family and case IDs, ordered signed units or a
balanced-input path, dimensions, byte counts and complete formula hashes.
Preparation performs no SAT search. The generator also reads the checked-in
normalized tables under `reproduce/data/`, including `marked_uu.json`,
`c_entrances.json` and `balance_anchors.json`. Their identities are recorded
with the generated inputs.

Compare the freshly reconstructed catalog and base with the checked release:

```sh
cmp "$proof_work_dir/fresh-campaign/inputs/base.clauses" \
    "$proof_work_dir/evidence-v2/inputs/base.clauses"
python3 - "$proof_work_dir/fresh-campaign/inputs/cases.jsonl.gz" \
          "$proof_work_dir/evidence-v2/inputs/cases.jsonl.gz" <<'PY'
import gzip, itertools, json, sys
with gzip.open(sys.argv[1], 'rt') as first, gzip.open(sys.argv[2], 'rt') as second:
    for a, b in itertools.zip_longest(first, second):
        if a is None or b is None or json.loads(a) != json.loads(b):
            raise SystemExit('Catalog mismatch')
print('All catalog records match')
PY
for owner in UU UT TT; do
  cmp "$proof_work_dir/fresh-campaign/inputs/balanced/$owner.cnf" \
      "$proof_work_dir/evidence-v2/inputs/balanced/$owner.cnf"
done
```

The catalog comparison checks every ordered case record, including its
complete formula identity, without requiring identical gzip implementations.
The base and balanced formulas are compared byte for byte.

| Family | Cases |
| --- | ---: |
| `A` | 360 |
| `B` | 5,096 |
| `D_UUU` | 679 |
| `D_UUT` | 679 |
| `D_UTU` | 6,576 |
| `D_UTT` | 6,576 |
| `D_TTU` | 18,204 |
| `D_TTT` | 18,204 |
| `C` | 346 |
| `BALANCE` | 3 |
| **Total** | **56,723** |

Materialize an individual formula by its exact family and case ID:

```sh
python3 -B reproduce/uniform_k61.py materialize \
  --family C --case UU/455/pair_000/rep_000 \
  --output "$proof_work_dir/C-UU.cnf"
python3 -B reproduce/uniform_k61.py materialize \
  --family BALANCE --case UU \
  --output "$proof_work_dir/balance-UU.cnf"
```

The destination must be new. Marked formulas have 7,320 variables and the
156,770-clause common base followed by one unit clause per recorded literal.
The three balanced formulas have 13,656 variables and 524,462 clauses each.

For an edge with `u < v` and color `c`, its physical variable is

```text
4 * (u * (121 - u) // 2 + v - u - 1) + c + 1.
```

Pairs are listed lexicographically. The base emits the positive color
clause followed by six pairwise color exclusions for each edge, then the
four monochromatic-triangle exclusions for each lexicographically listed
triple. Case facts and auxiliary clauses have fixed orders as well, so the
comparison checks complete input identities rather than equisatisfiability.

## Run both solvers afresh

The supplied campaign driver uses native process accounting on macOS/Linux.
Its binary lookup is `/opt/homebrew/bin/kissat` and
`/opt/homebrew/bin/cadical`, with versions 4.0.4 and 3.0.1. This matches the
recorded macOS environment. On a different installation, adjust only that
lookup in the driver to the installed binaries; the driver retains its
own source and both binary identities in each new campaign. Verification
of the retained release does not need installed solvers.

After preparing `fresh-campaign/inputs`, start the complete search:

```sh
python3 -B reproduce/uniform_campaign.py \
  --root "$proof_work_dir/fresh-campaign" --workers 12
```

Choose a worker count supported by the machine. Both solvers use default
search options with no CPU or wall-clock limit for every case. The driver
copies and hashes the binaries, sources and finite data, and hashes each
input before and after its native execution. Marked inputs are retained
compactly as the shared base and signed units; the three balanced inputs
are retained in full.

A stop signal stops new admissions and lets submitted processes finish.
SAT, UNKNOWN or an error also stops further admissions. A 100 GiB free-disk
floor pauses new admissions without terminating a running solver. Incomplete
coverage cannot be reported as a successful complete campaign. Sleeping the
machine postpones completion without consuming a wall-clock timeout.

For an inventory during the search:

```sh
python3 -B reproduce/uniform_verify.py \
  --root "$proof_work_dir/fresh-campaign" --inventory
```

After it finishes, verify all results and independently rederive every input:

```sh
python3 -B reproduce/uniform_verify.py \
  --root "$proof_work_dir/fresh-campaign" \
  --rederive archives/evidence-v1.tar.gz \
  --output "$proof_work_dir/fresh-native-verification.json"
```

`uniform_verify.py` verifies a single native campaign. The supplied release
also contains mathematical verification records and is checked by
`uniform_release.py verify-package` as shown above. A native inventory is
not complete proof-package acceptance.

## Build and bind the mathematics

Build the complete proof from source:

```sh
(
  cd formal
  lake exe cache get
  lake env python3 build.py --validate-only
  lake env python3 build.py --jobs 1
)
```

Keep the supplied lock file. The full build includes the selected source closure and the
55 small classification CNF/LRAT checks, using a fresh project library.
It does not launch the native K61 searches. See
[the build guide](../formal/BUILD.md) and
[resource measurements](../formal/MEASUREMENTS.md) before increasing
compiler concurrency.

Use the successful full build's exact output directory for the binding:

```sh
(
  cd formal
  lake env python3 reproduce/uniform/run_binding.py \
    --build-dir /absolute/path/to/successful/.build/runs/RUN \
    --inputs "$proof_work_dir/fresh-campaign/inputs" \
    --output-dir "$proof_work_dir/fresh-binding"
)
```

The driver audits the exact final theorem type and count, executes the four
Lean emitters, then checks their complete disjoint union: 56,374 A/B/D
marked cases, 346 C entrances and three balanced inputs.
All 56,723 DIMACS identities must agree. Source, input, compiler, runtime,
log and artifact hashes are checked across the execution. The output
directory must be fresh; a failed attempt preserves its records.

## Routine repository checks

```sh
make test-ci
make lean-source-audit
make lean-ci
```

The source audit authenticates the full selected source/data package.
The small Lean CI target checks the physical encoding in five modules and
audits its two theorem dependencies. It does not substitute for the complete
mathematical build, all input bindings, or native SAT verification. The
[trust statement](TRUST_AND_CERTIFICATION.md) explains how these checks
combine to support the proof.
