# The project's K15 and K16 classification proofs

This package contains the project's own Lean derivation of the complete
critical three-color catalogues. It does not import a published Ramsey
classification theorem or use the answer to a previous published search as
an axiom.

`R4333Lean/CriticalCatalogues.lean` proves that every triangle-free
three-coloring of K16 is weakly isomorphic to one of the two explicit
templates, and every such K15 coloring is a deletion of one of those
templates. Weak isomorphism allows a vertex permutation and a single
permutation of the three colors.

The local proof proceeds through:

1. The elementary color-degree bounds.
2. Normalized, certificate-checked cases establishing the strongly regular
   parameters `(16,5,0,2)` for each color graph of a critical K16.
3. A constructive proof of uniqueness of the Clebsch graph with those
   parameters.
4. A certificate-checked exhaustive list of 72 two-color decompositions of
   its complement, and explicit maps into the two templates.
5. Certificate-checked K15 deficient-color constraints, which give a
   canonical K15-to-K16 extension, followed by restriction and vertex
   transitivity.

The payload consists of **32 Lean modules and 55 CNF/LRAT pairs**. The
110 data files total **5,081,743 bytes**. There are 30 pairs for the K15
extension, 24 for the K16 common-neighbor rule, and one for the Clebsch
complement. This is the exact dependency closure of the two catalogue
theorems.

`CheckedLRAT.lean` constructs a proof term from each LRAT trace and checks
that its type is the specified Lean CNF. The DIMACS formula must be
definitionally equal to that CNF. The result is checked by Lean's kernel;
the command does not declare an UNSAT axiom.

## Evidence and reproduction

The [32-module verification build](build_runs/20260922T072158Z_1790061718513440000/SUMMARY.json)
passed on 22 September 2026, using the packaged sources and all 55 included
CNF/LRAT pairs. Its import path contains only the build output and the
pinned Mathlib dependency cache; all project modules are compiled from source. The complete rebuild used **827.71 CPU seconds**, **725.37 seconds of
summed module elapsed time**, and at most **14,793,555,968 bytes (13.78 GiB)
RSS**. Modules were admitted serially, with four Lean threads per module.
The largest output was a 77,115,296-byte `.olean`.

The [actual-host adapter](adapter/README.md) is checked against this
classification closure. All seven inspected endpoints use only `propext`, `Classical.choice`
and `Quot.sound`; no catalogue-completeness premise remains at the K15/K16
physical-neighborhood endpoints. The adapter preserves both the physical
vertex map and the single palette permutation. It is checked separately
from the default `formal/` CI package.

[MANIFEST.json](MANIFEST.json) records exact files, hashes, import order and
source provenance. Build receipts preserve input manifests, commands, compiler
and source hashes, full logs and resource records. The
[complete portable build](../formal/BUILD_RESULT.json) also compiled all 32
classification modules and replayed all 55 pairs within the full mathematical
closure, using the [integrated source manifest](../formal/SOURCE_MANIFEST.json).

The package pins Lean 4.32.1 and Mathlib revision
`520045ab14e26149ee970e2e617ca04b09bde5d6`, matching the current formal package.
This standalone package has no checked-in Lake lock file. Its `lake update`
command resolves the revision fixed in `lakefile.toml` and creates its local
lock file. This differs from `formal/`, which supplies a complete lock file
that must be preserved. With Elan and Git installed, prepare the standalone
dependencies from this directory:

```sh
lake update
lake exe cache get
```

[build_serial.sh](build_serial.sh) lists all 32 source compilations in import
order, using four Lean threads per module. It writes new compiled output
under this package's `.lake/build/`. It invokes no SAT solver: the included
traces are replayed by the kernel.

```sh
sh build_serial.sh
```

On macOS, [build_local.py](build_local.py) instead uses an existing read-only
dependency cache, checks its Mathlib revision and all source/data hashes,
and writes separate output and receipts for every run:

```sh
python3 build_local.py --cache-root /path/to/pinned/.lake/packages \
  --lean /path/to/lean-4.32.1/bin/lean --jobs 4
```

Neither script imposes CPU, RSS or output-file kill limits. `build_local.py`
stops admitting new modules if the host reports acute memory or disk
pressure; it never signals existing jobs. The measured 13.78 GiB compiler
peak means the full rebuild should not be assumed to fit a small CI runner.

The present GitHub CI checks `formal/`, not this separate classification
package. Its verification scope is described in
[the provenance note](../publication/CLASSIFICATION_PROVENANCE.md).
