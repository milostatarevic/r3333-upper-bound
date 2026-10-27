# Reproduce the formula and evidence checks

Use the current repository's tools to check the released records, then [build the mathematics](../BUILD.md) and run a fresh [exact input binding](uniform/README.md). These checks do not execute a SAT solver.

## Check the retained release

After extracting the evidence package described in the [repository reproduction guide](../../publication/REPRODUCIBILITY.md), set `release_dir` to the directory containing `RELEASE.json`. Run from the repository root:

```sh
release_dir="/absolute/path/to/extracted-release"
python3 reproduce/uniform_release.py verify-package \
  --root "$release_dir" \
  --formal-root formal \
  --output /absolute/path/to/fresh-release-check.json
```

The output file must not exist. This verifies the complete native and mathematical record set, source and input identities, exact theorem audit, and all 113,446 required native results. It checks retained build records without recompiling Lean and checks native logs without rerunning the searches.

## Regenerate the complete input catalogue

From the repository root:

```sh
python3 reproduce/uniform_k61.py prepare \
  --archive archives/evidence-v1.tar.gz \
  --output /absolute/path/to/fresh-uniform-inputs
```

The output directory must not exist. The generator authenticates the finite support/word source data and the normalized case tables, constructs the shared K61 base and all 56,723 formula identities, and writes the three balanced CNFs. It reads data from the archive without executing archived programs.

## Bind a fresh Lean build

Complete the full source build in [BUILD.md](../BUILD.md), then run from `formal/`:

```sh
lake env python3 reproduce/uniform/run_binding.py \
  --build-dir /absolute/path/to/successful/.build/runs/RUN \
  --inputs /absolute/path/to/fresh-uniform-inputs \
  --output-dir /absolute/path/to/fresh-binding-run
```

The driver requires a successful complete current-source build and a complete input catalogue. It checks the final theorem, executes the four current Lean emitters, and joins the exact formula comparisons. See [uniform/README.md](uniform/README.md) for the covered families and retained records.

Native-search reproduction is a separate operation, documented in the [repository guide](../../publication/REPRODUCIBILITY.md).
