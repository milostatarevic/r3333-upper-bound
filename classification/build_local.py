"""Serial classification rebuild using a read-only pinned dependency cache.

There are no imposed CPU, memory, or output-file-size kill limits. Each
admission checks the actual host's memory-pressure state and available disk.
Already running processes are never signalled. Per-module receipts preserve
commands, hashes, CPU/RSS and the complete output, including failures.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parent
MATHLIB_REV = "520045ab14e26149ee970e2e617ca04b09bde5d6"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def revision(path):
    metadata = path / ".git"
    if metadata.is_file():
        metadata = (path / metadata.read_text().strip().removeprefix("gitdir: ")).resolve()
    head = (metadata / "HEAD").read_text().strip()
    if not head.startswith("ref: "):
        return head
    ref = head[5:]
    target = metadata / ref
    if target.is_file():
        return target.read_text().strip()
    for line in (metadata / "packed-refs").read_text().splitlines():
        if line.endswith(" " + ref):
            return line.split()[0]
    raise RuntimeError("Cannot resolve cached Mathlib revision")


def host_state():
    pressure = subprocess.run(["/usr/bin/memory_pressure", "-Q"],
                              text=True, capture_output=True, check=True)
    match = re.search(r"System-wide memory free percentage:\s*(\d+)%", pressure.stdout)
    if not match:
        raise RuntimeError("Cannot read host memory-pressure report")
    return {"memory_free_percent": int(match[1]),
            "disk_free_bytes": shutil.disk_usage(ROOT).free,
            "pressure_report": pressure.stdout.strip()}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--cache-root", type=Path, required=True)
    parser.add_argument("--lean", type=Path, required=True)
    parser.add_argument("--jobs", type=int, default=4)
    args = parser.parse_args()
    if args.jobs < 1:
        raise ValueError("jobs must be positive")
    cache = args.cache_root.resolve()
    if revision(cache / "mathlib") != MATHLIB_REV:
        raise RuntimeError("Mathlib revision differs from the package pin")
    if (cache / "mathlib/lean-toolchain").read_text() != (ROOT / "lean-toolchain").read_text():
        raise RuntimeError("Lean toolchain differs from the package pin")
    manifest_path = ROOT / "MANIFEST.json"
    manifest = json.loads(manifest_path.read_text())
    for record in manifest["files"]:
        if record["kind"] not in ("lean_source", "cnf", "lrat"):
            continue
        source = ROOT / record["path"]
        if source.stat().st_size != record["bytes"] or sha(source) != record["sha256"]:
            raise RuntimeError("Pinned input mismatch: " + record["path"])
    stamp = time.strftime("%Y%m%dT%H%M%SZ", time.gmtime()) + "_" + str(time.time_ns())
    run = ROOT / "build_runs" / stamp
    run.mkdir(parents=True)
    shutil.copyfile(Path(__file__), run / "build_local.py")
    shutil.copyfile(manifest_path, run / "input_manifest.json")
    out = ROOT / ".lake" / "classification_runs" / stamp / "lib" / "lean"
    out.mkdir(parents=True)
    cache_paths = [p / ".lake/build/lib/lean" for p in sorted(cache.iterdir()) if p.is_dir()]
    env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, [out] + cache_paths)))
    records = []
    print(json.dumps({"run": str(run), "output": str(out), "status": "STARTED"}), flush=True)
    for number, module in enumerate(manifest["topological_module_order"]):
        before = host_state()
        # These are host-pressure admission checks, not per-process limits.
        # Normal operation has tens of GiB available and >1 TiB free disk.
        if before["memory_free_percent"] <= 5 or before["disk_free_bytes"] < (1 << 30):
            (run / "ADMISSION_HOLD.json").write_text(json.dumps(before, indent=2) + "\n")
            raise RuntimeError("Host under memory/disk pressure; no new compiler admitted")
        source = ROOT / (module.replace(".", "/") + ".lean")
        dest = out / (module.replace(".", "/") + ".olean")
        dest.parent.mkdir(parents=True, exist_ok=True)
        command = [str(args.lean), "-j" + str(args.jobs), "-o", str(dest), str(source)]
        log_path = run / (f"{number:02d}_" + module + ".log")
        start = time.monotonic()
        with log_path.open("x") as log:
            result = subprocess.run(["/usr/bin/time", "-l"] + command,
                                    cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT)
        elapsed = time.monotonic() - start
        log_text = log_path.read_text()
        timing = re.search(r"([\d.]+) real\s+([\d.]+) user\s+([\d.]+) sys", log_text)
        rss = re.search(r"(\d+)\s+maximum resident set size", log_text)
        record = {"module": module, "status": "PASS" if result.returncode == 0 else "FAIL",
                  "command": command, "exit_code": result.returncode,
                  "elapsed_seconds": elapsed,
                  "user_CPU_seconds": float(timing[2]) if timing else None,
                  "system_CPU_seconds": float(timing[3]) if timing else None,
                  "peak_RSS_bytes_macos": int(rss[1]) if rss else None,
                  "source_sha256": sha(source), "log_sha256": sha(log_path),
                  "olean": str(dest), "olean_sha256": sha(dest) if dest.is_file() else None,
                  "olean_bytes": dest.stat().st_size if dest.is_file() else None,
                  "host_before": before, "host_after": host_state(),
                  "lean_binary_sha256": sha(args.lean), "mathlib_revision": MATHLIB_REV,
                  "input_manifest_sha256": sha(run / "input_manifest.json"),
                  "controller_sha256": sha(run / "build_local.py"),
                  "CPU_limit": None, "RSS_kill_limit": None, "file_size_limit": None,
                  "new_solver_calls": 0}
        (run / (f"{number:02d}_" + module + ".json")).write_text(json.dumps(record, indent=2) + "\n")
        records.append(record)
        print(json.dumps({k: record[k] for k in ("module", "status", "user_CPU_seconds",
              "system_CPU_seconds", "peak_RSS_bytes_macos", "olean_bytes")}), flush=True)
        if result.returncode:
            print(log_text, flush=True)
            raise SystemExit(result.returncode)
    summary = {"status": "PASS_COMPLETE_CLASSIFICATION_REBUILD", "run": str(run),
               "output": str(out), "module_count": len(records),
               "total_CPU_seconds": sum((r["user_CPU_seconds"] or 0) +
                                        (r["system_CPU_seconds"] or 0) for r in records),
               "sum_elapsed_seconds": sum(r["elapsed_seconds"] for r in records),
               "peak_RSS_bytes_macos": max(r["peak_RSS_bytes_macos"] or 0 for r in records),
               "records": [f"{i:02d}_" + r["module"] + ".json" for i, r in enumerate(records)]}
    (run / "SUMMARY.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary), flush=True)


if __name__ == "__main__":
    main()
