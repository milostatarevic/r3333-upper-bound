# Reproduce the K60 argument

The boundary has **296,081 indexed formulas**: 231,168 E, 56,374 A/B/D, and
8,539 entrance and compatibility cases. Each has accepted native UNSAT
evidence from both Kissat 4.0.4 and CaDiCaL 3.0.1. Lean proves the mathematical reduction, exhaustive coverage and
encoding soundness in `UniformK60.ramsey60_of_exact_unsat`; its explicit premise
is `UniformK60.ExactInputs.AllUnsat`. The large native UNSAT results remain
external evidence, not refutations replayed by the Lean kernel.

## Check the retained evidence

Use Python 3.9+ and the standard library. Obtain the large archives through
Git LFS (`git lfs pull` in a Git checkout). Check the archive hashes against the
independently obtained [release index](publication/checks/K60_RELEASE.json), then
extract into two fresh directories. The native archive is stored in two
ordered parts, each below the hosting limit of 2 GiB per LFS object. The
release index pins each part and the original concatenated archive; splitting
does not alter its contents. The archives contain capsule members directly,
without a wrapping directory:

Run these commands in Bash from the repository root. The subshell stops on any failed
checksum, directory creation or extraction:

```sh
(
  set -euo pipefail
  (cd archives && shasum -a 256 -c SHA256SUMS)
  mkdir k60-formal-capsule k60-native-capsule
  tar -xzf archives/k60-formal-evidence.tar.gz -C k60-formal-capsule
  cat archives/k60-native-evidence.tar.gz.part01 \
      archives/k60-native-evidence.tar.gz.part02 | \
    tar -xz -C k60-native-capsule
)
```

Keep the two capsule workspaces separate. Replace the following paths with
your extraction paths, and set `K60_RELEASE_INDEX_SHA256` to the independently
obtained SHA256 of the release index:

```sh
K60_NATIVE=/absolute/path/to/native-capsule
K60_FORMAL=/absolute/path/to/formal-capsule
K60_NATIVE_SHA256=a781e5aecc1b91ae80419b3b396d3ac8439278ace527fc73859fdfaa2341537e
K60_RELEASE_INDEX_SHA256=...

python3 -B scripts/check_publication.py \
  --release-index-sha256 "$K60_RELEASE_INDEX_SHA256" \
  --formal-capsule "$K60_FORMAL" --native-capsule "$K60_NATIVE" --require-cadical
```

This command launches neither Lean nor a SAT solver and does not execute archived
generator code. Native verification reconstructs the full case/hash census and
checks every retained attempt, command, solver identity, raw log, exit status
and direct UNSAT coverage. The original CaDiCaL campaign covers 296,797
inputs; the selected package retains 296,077 of those formulas plus the four
direct C2 compatibility formulas. Omission records authenticate the 720
retired marked-balance inputs without counting them in the selected boundary.
Formal verification checks source/import closure, build and binding records,
and the retained complete formula emissions.
The same command independently recomputes the successful-run CPU report,
counting each selected formula's completed UNSAT execution once per solver and
reconciling unsuccessful-attempt overhead against the preserved all-attempt
totals. Checking these records is separate from rerunning Lean.

The retained formal build reuses 1,309 unchanged modules from the accepted
build and recompiles the five changed or dependent modules. The checks bind
their source and compiled artifact hashes. Retained Lean emissions are reused
only when the emitter, compiler and imported artifact bytes are unchanged;
their complete contents are compared again with the selected native inputs.
The source-build recipe below independently rebuilds all 1,314 selected modules.

Raw records retain their original paths. The manifest maps those paths to
archive members; the original machine and its installed solver are unnecessary.
Keep each capsule unchanged and write new outputs elsewhere. The external
manifest pin is essential; a hash supplied only by the same unchecked payload
is not an independent authentication source.

The [manual evidence workflow](.github/workflows/evidence.yml) runs these same passive
checks using an externally supplied release-index hash. By default it requires
complete CaDiCaL evidence, as does the local command above. The optional
`require_cadical=false` setting is only for reviewing historical incomplete
preparation packages. The workflow downloads only the K60 formal archive and
native archive parts, authenticates their concatenation, and
retains the verification logs. It neither publishes a release nor reruns Lean
or native solvers.

## Build the mathematical source package

The public `formal/` package contains the complete selected source closure and
its classification data. With Python 3.9+, Git and Elan installed, run from the
repository root:

```sh
(
  set -e
  cd formal
  lake exe cache get
  lake env python3 build.py --target UniformK60.Verification --validate-only
  lake env python3 build.py --target UniformK60.Verification --jobs 1
)
```

Keep `formal/lake-manifest.json` unchanged; do not run `lake update`. The builder
checks the pinned toolchain, clean dependency revisions, source hashes and
embedded data, and compiles into a fresh project library. A complete build
replays the 55 small classification certificates but does not rerun the large
native searches. [BUILD.md](formal/BUILD.md) describes the receipts, the small
encoding target and resource scope.

The [push/PR workflow](.github/workflows/verify.yml) audits the complete source
manifest and builds only the five-module `UniformK60.CoreCounts` target. It
does not replay the classification traces or compile the final theorem. The
[manual full-build workflow](.github/workflows/full-lean.yml) uses a provisioned
self-hosted runner for the complete source build and classification replay.
It does not perform exact-input binding or native searches. The corresponding
local targets are `make audit-sources`, `make test-ci`, `make lean-ci` and
`make lean-full`.

## Rebuild and bind the formal definitions

After the public source build above succeeds, use its printed
`BUILD_RESULT.json` for all four input comparisons. The checks run the
retained Lean emitters against that build and compare their output with the
native capsule's pinned inputs. Run from the repository root, choosing a new
output directory:

```sh
K60_BUILD_RESULT=/absolute/path/printed/by/the/build/BUILD_RESULT.json
K60_BINDINGS=/absolute/path/to/new-bindings

(
  set -e
  mkdir "$K60_BINDINGS"
  for PART in base marked counter balance; do
    python3 -B reproduce/publication_formal_evidence.py bind \
      --part "$PART" --formal formal --build-result "$K60_BUILD_RESULT" \
      --native-capsule "$K60_NATIVE" --output "$K60_BINDINGS/$PART"
  done
)
```

Stop if any stage fails. The checks bind the shared base, all marked/entrance
formula occurrences, counter clauses and seven complete balance formulas
to that same build. They check full input identities, including clause
order and repeated formula occurrences. Retain the receipts and logs.
These checks establish formal/input correspondence; they do not run the native
campaigns or discharge the external UNSAT premise.

To package the new build and comparisons for passive review, choose a new
destination:

```sh
K60_NEW_FORMAL=/absolute/path/to/new-formal-capsule

python3 -B reproduce/publication_formal_evidence.py prepare \
  --formal formal --build-result "$K60_BUILD_RESULT" \
  --bindings "$K60_BINDINGS" --native-capsule "$K60_NATIVE" \
  --output "$K60_NEW_FORMAL"
```

The capsule retains the selected sources, build receipts, four comparisons
and their complete emissions. The command verifies the resulting capsule
and prints its new manifest hash; this local rerun has its own identity,
separate from the published evidence.

## Export and rerun an individual formula

The selected-boundary tool
[`publication_native_evidence.py`](reproduce/publication_native_evidence.py)
lists case keys and exports exact formulas. Exporting a marked or entrance
formula imports the retained pinned catalogue code; exporting a compatibility
formula copies its retained full prefix. This active step is separate from
passive verification. It needs Python 3.9+ and the native capsule, with no
compiler, PySAT or original solver installation.

```sh
python3 -B reproduce/publication_native_evidence.py list \
  --root "$K60_NATIVE" --manifest-sha256 "$K60_NATIVE_SHA256" \
  --prefix balance/

python3 -B reproduce/publication_native_evidence.py export \
  --root "$K60_NATIVE" --manifest-sha256 "$K60_NATIVE_SHA256" \
  --case-key balance/C2_ROOT_UU --output /path/to/new-case.cnf

/path/to/your/kissat /path/to/new-case.cnf > /path/to/new-case-kissat.log
/path/to/your/cadical /path/to/new-case.cnf > /path/to/new-case-cadical.log
```

Case-key families are `e/`, `abd/`, `closure/` and `balance/`. Only the selected
296,081 cases are admitted; the retired marked-balance cases are excluded.
The destination must be new. The exporter verifies the complete declared CNF
SHA256 before and after writing.
Use your platform's own solvers for separate native reruns and retain each
binary/input hash, command, full log and exit status. Both solvers' accepted
UNSAT outcomes use exit status 20 and the exact line `s UNSATISFIABLE`; an
individual rerun does not establish coverage of the whole boundary.

All 296,081 indexed formulas have direct Kissat and CaDiCaL evidence under
the documented acceptance checks. Timeouts and interrupted attempts are
retained as history and never counted as refutations.

## Reproduce the completed CaDiCaL import

For maintainers, the completion importer accepts the stopped campaign only
after a fresh independent audit confirms every original case is UNSAT. It
preserves the raw attempt histories, selects the current boundary and computes
its all-attempt CaDiCaL timings in a new capsule. The input must be the
preserved pending capsule, not the completed capsule distributed above:

```sh
K60_PENDING_NATIVE=/absolute/path/to/preserved-pending-native-capsule
K60_PENDING_NATIVE_SHA256=af5f61c53abda49ef71cc8aa10493552670025baee5fb63c90d3247281818a1a

python3 -B reproduce/publication_native_evidence.py finalize-cadical \
  --root "$K60_PENDING_NATIVE" --manifest-sha256 "$K60_PENDING_NATIVE_SHA256" \
  --campaign /absolute/path/to/campaign-cadical-3.0.1 \
  --output /absolute/path/to/new-complete-native-capsule
```

The command refuses an incomplete campaign and neither modifies its records
nor runs a solver. Verify and archive the new capsule, then update the archive
checksums and release index to its new identity. The completed publication
capsule includes CaDiCaL results for every selected formula; the four direct
C2 results are included exactly once.
