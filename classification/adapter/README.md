# Critical catalogues on the 61-vertex host

[ClassificationAdapter.lean](Ramsey61/ClassificationAdapter.lean) connects
the proved K15/K16 catalogues to the `Ramsey61.Host` type. Every
high monochromatic neighborhood is mapped completely onto a critical
template, preserving actual vertices and one consistent map of the three
remaining colors. It also exposes the K15 extension and the K16 strongly
regular color-graph theorem.

The [check receipt](../build_runs/ADAPTER_FRESH_20260922T073615Z/receipt.json)
and [axiom output](../build_runs/ADAPTER_FRESH_20260922T073615Z/lean.log) record
successful compilation against the 32-module classification closure:
2.30 CPU seconds, 2.89 elapsed seconds and 2,910,715,904 bytes peak RSS.
All seven inspected endpoints use only `propext`, `Classical.choice` and
`Quot.sound`. The source SHA-256 is
`ba4fc9343574e607478103599de47d45f176ba2dfef6cfcea9535f96ab165356`.

[RELOCATION.json](RELOCATION.json) binds the source path used in the check
receipt to this byte-identical packaged file. The default formal CI builds the
structural and encoding package; the adapter is checked using the command below.
Its endpoint provides catalogue and neighborhood maps, while the complete K61
case covers are presented in the written proof.

To repeat from the repository root after building `formal/` and the
classification package, provide the three existing dependency locations
and the pinned compiler. The classification location is the `output` field
in its successful `SUMMARY.json`; no historical project cache is required.

```sh
python3 - /path/to/lean-4.32.1/bin/lean \
  /path/to/pinned/.lake/packages \
  /path/to/fresh/classification/lib/lean <<'PY'
from pathlib import Path
import os, subprocess, sys
lean, cache, classification = sys.argv[1:]
root = Path.cwd().resolve()
output = root / 'classification/.lake/adapter/lib/lean/Ramsey61'
output.mkdir(parents=True, exist_ok=True)
paths = [root / 'formal/.lake/build/lib/lean', Path(classification)]
paths += [p / '.lake/build/lib/lean' for p in Path(cache).iterdir()
          if (p / '.lake/build/lib/lean').is_dir()]
env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, paths)))
subprocess.run([lean, '-j1', '-o', str(output / 'ClassificationAdapter.olean'),
                str(root / 'classification/adapter/Ramsey61/ClassificationAdapter.lean')],
               cwd=root / 'classification/adapter', env=env, check=True)
PY
```
