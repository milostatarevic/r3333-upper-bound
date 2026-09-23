#!/usr/bin/env python3
"""Replay the frozen independent finite G checkers, without a SAT solver.

Usage: python3 -B reproduce/g_check.py --snapshot /authenticated/extraction \
    --output /new/outside-directory

All inputs and both executed checker sources are authenticated by exact pins.
The sources are copied unchanged to the fresh output directory. Their original
function entry points run there, with no monkeypatch, changed source, changed
mathematical data, producer execution, or write into the evidence snapshot.
"""
import argparse
import contextlib
import hashlib
import json
import math
import os
from pathlib import Path
import resource
import shutil
import stat
import sys
import time

G_PATH = "evidence/G/retained"
FLOOR = 100 << 30
CPU_LIMIT = 60
RSS_LIMIT = 1 << 30
TREE_LIMIT = 64 << 20
FILE_LIMIT = 16 << 20
PINS = {
    "g_isomorphism": {
        "tools/checker.py": (35715, "6944bd1ed614d7db9e31bce5cbed9520190ba96507ae106cec2bef0683986ac5"),
        "tools/producer.py": (20946, "8157cf89b785834607a11c9211a8a5aab2b50c2c40a8bd34eca84b876eba8367"),
        "IMPLEMENTATION_CONTRACT.md": (6438, "bf1b82809714593fea2348dca0be74d386ac53492c5438935057867cc4ea1a0d"),
        "inputs/census.json": (290525, "f6f7e9e3c18969663ce0ad4fd94b584a340a70b9f929a433458aa3415d69f17a"),
        "inputs/source_matrices.json": (2258, "d278b344d4fbcaf892c41cd3c843b302844d54766d9489427e3a89fcd24f4d13"),
        "producer/SUMMARY.json": (647, "26be9a6941de4ec2bde5e40ff461bc223ae79058645a4034d4ea2a77c5c2f611"),
        "producer/results.json": (444528, "c04d8e4c878d1c68dc516f85570b7f90472805e50068546c3142755b90f70202"),
    },
    "g_remaining": {
        "tools/checker.py": (41424, "1ebf555cf5f0bb268b5412735747c361c6a43e2e36173a2d6f073b4f41347192"),
        "tools/producer.py": (26711, "cc6ece538e6ffe4ae70e1296d0bca94e746f0d9f45a0350a98cc1948ff832f83"),
        "IMPLEMENTATION_CONTRACT.md": (8168, "995342c0ba3939592ae4ef80843b70fccede5dc55499a2e95887d2cc7bf041af"),
        "inputs/census.json": (920722, "1f0fad0daf300ba33d3942f8ef7fee4fb6eb9504b1f3bddcca23f004d56a298e"),
        "inputs/source_matrices.json": (2258, "d278b344d4fbcaf892c41cd3c843b302844d54766d9489427e3a89fcd24f4d13"),
        "producer/SUMMARY.json": (1488, "4cb471489f76138bffd6e16cba33b03359879e5d3c66e81e55fb823166f2e984"),
        "producer/results.jsonl": (1149252, "9d472a88e328ab05ffc7567b8f06ab6d6b338c23decefb5bd982a769f27c0c3d"),
        "inputs/parent_census.json": (290525, "f6f7e9e3c18969663ce0ad4fd94b584a340a70b9f929a433458aa3415d69f17a"),
        "inputs/parent_local_reference.json": (117800, "2a7a1bf3f4128caaffefc0c8dbde13177e572e4f9b21ec8135f9ecd87b66f8b2"),
        "inputs/parent_LOCAL_SUMMARY.json": (1608, "f486dfe2bd11c626fdbe399ab0a348eedacce7e900fa100682b67131a41af6f7"),
        "inputs/PREPARE_RECEIPT.json": (973, "74c9b958f411b8b758b3f196578428b9631765b18c431921a426d2087028b973"),
    },
}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def identity(info):
    return (info.st_dev, info.st_ino, info.st_size,
            info.st_mtime_ns, info.st_ctime_ns)


def ordinary(path, directory=False):
    path = Path(os.path.abspath(path))
    for part in reversed((path,) + tuple(path.parents)):
        mode = part.lstat().st_mode
        expected = stat.S_ISDIR if part != path or directory else stat.S_ISREG
        need(expected(mode), "Nonordinary/symlink path component: " + str(part))
    return path


def stable_bytes(path, expected=None):
    path = ordinary(path)
    before = path.stat()
    need(before.st_size <= FILE_LIMIT, "Oversized finite input")
    with path.open("rb") as handle:
        need(identity(os.fstat(handle.fileno())) == identity(before), "File replaced at open")
        raw = handle.read(FILE_LIMIT + 1)
        need(identity(os.fstat(handle.fileno())) == identity(before), "File changed during read")
    need(identity(path.stat()) == identity(before), "File replaced after read")
    need(len(raw) == before.st_size, "Incomplete input read")
    result = (len(raw), hashlib.sha256(raw).hexdigest())
    if expected is not None:
        need(result == expected, "Frozen byte/hash mismatch: " + str(path))
    return raw


def bare_pin(path):
    raw = stable_bytes(path)
    return {"bytes": len(raw), "sha256": hashlib.sha256(raw).hexdigest()}


def parse(raw):
    def pairs(items):
        obj = {}
        for key, value in items:
            need(key not in obj, "Duplicate JSON key")
            obj[key] = value
        return obj

    def bad(value):
        raise ValueError("Nonfinite JSON value: " + value)

    def number(value):
        n = float(value)
        need(math.isfinite(n), "Overflowing JSON number")
        return n

    return json.loads(raw, object_pairs_hook=pairs, parse_constant=bad, parse_float=number)


def read_json(path):
    return parse(stable_bytes(path))


def write_new(path, raw):
    need(len(raw) <= FILE_LIMIT, "Oversized output")
    path.parent.mkdir(parents=True, exist_ok=True)
    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL |
                 getattr(os, "O_NOFOLLOW", 0), 0o600)
    with os.fdopen(fd, "wb") as handle:
        handle.write(raw)
        handle.flush()
        os.fsync(handle.fileno())
    need(stable_bytes(path) == raw, "Output readback differs")
    path.chmod(0o444)


def peak_rss():
    value = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    return int(value if sys.platform == "darwin" else value * 1024)


def guard(output):
    need(shutil.disk_usage(output).free >= FLOOR, "100 GiB free-space floor")
    need(peak_rss() <= RSS_LIMIT, "Observed process peak RSS exceeds 1 GiB")
    size = 0
    for base, dirs, files in os.walk(output, followlinks=False):
        for name in dirs:
            ordinary(Path(base) / name, directory=True)
        for name in files:
            path = ordinary(Path(base) / name)
            n = path.stat().st_size
            need(n <= FILE_LIMIT, "Output file cap exceeded")
            size += n
    need(size <= TREE_LIMIT, "64 MiB output-tree cap exceeded")
    return size


def limits():
    """Hard CPU/file caps; Linux address-space guard, plus stage RSS checks."""
    need(sys.flags.optimize == 0, "Run ordinary Python without -O")
    need(sys.version_info >= (3, 9), "Python 3.9+ required")
    for which, value in ((resource.RLIMIT_CPU, CPU_LIMIT),
                         (resource.RLIMIT_FSIZE, FILE_LIMIT)):
        soft, hard = resource.getrlimit(which)
        if hard != resource.RLIM_INFINITY:
            value = min(value, hard)
        if soft != resource.RLIM_INFINITY:
            value = min(value, soft)
        resource.setrlimit(which, (value, value))
    if sys.platform.startswith("linux"):
        soft, hard = resource.getrlimit(resource.RLIMIT_AS)
        value = 2 << 30
        for current in (soft, hard):
            if current != resource.RLIM_INFINITY:
                value = min(value, current)
        resource.setrlimit(resource.RLIMIT_AS, (value, value))
    # The frozen sources never spawn children or import project modules.
    sys.dont_write_bytecode = True


def stage(output, stages, kind, action, namespace):
    root = output / kind
    guard(output)
    t0, wall = time.process_time(), time.monotonic()
    stdout = output / "logs" / (kind + "_" + action + ".stdout.log")
    stderr = output / "logs" / (kind + "_" + action + ".stderr.log")
    stdout.parent.mkdir(exist_ok=True)
    with stdout.open("x") as out, stderr.open("x") as err:
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            namespace[action + "_action"](root)
    stdout.chmod(0o444)
    stderr.chmod(0o444)
    size = guard(output)
    stages.append({
        "kind": kind, "action": action, "status": "RETURNED_WITHOUT_ERROR",
        "CPU_seconds": time.process_time() - t0,
        "wall_seconds": time.monotonic() - wall,
        "peak_process_RSS_bytes": peak_rss(), "output_tree_bytes": size,
        "stdout": {"path": str(stdout), **bare_pin(stdout)},
        "stderr": {"path": str(stderr), **bare_pin(stderr)},
    })
    print(json.dumps({"stage": kind + "/" + action,
                      "CPU_seconds": stages[-1]["CPU_seconds"]}), flush=True)


def summary(root, name, schema):
    value = read_json(root / "checker" / name)
    need(value.get("schema") == schema and value.get("status") == "PASS",
         "Missing successful checker summary: " + name)
    return value


def replay(snapshot, output, started):
    copied = []
    modules = {}
    for kind, entries in PINS.items():
        target = output / kind
        for relative, pin in entries.items():
            source = snapshot / G_PATH / kind / relative
            raw = stable_bytes(source, pin)
            destination = target / relative
            write_new(destination, raw)
            copied.append({"snapshot_path": G_PATH + "/" + kind + "/" + relative,
                           "replay_path": str(destination),
                           "bytes": pin[0], "sha256": pin[1]})
        path = target / "tools/checker.py"
        raw = stable_bytes(path, entries["tools/checker.py"])
        namespace = {"__name__": "_ramsey61_frozen_" + kind,
                     "__file__": str(path), "__package__": None}
        # Exactly authenticated independent checker source, without its CLI.
        # No imported source/constant/function is changed after execution.
        exec(compile(raw, str(path), "exec"), namespace)
        need(namespace["ROOT"] == target, "Copied checker's physical root differs")
        modules[kind] = namespace

    stages = []
    iso = output / "g_isomorphism"
    rem = output / "g_remaining"
    stage(output, stages, "g_isomorphism", "local", modules["g_isomorphism"])
    local = summary(iso, "LOCAL_SUMMARY.json", "C61_CORE_LOCAL_CHECK_1")
    need((local["rank"], local["nullity"], local["free_assignments_checked"],
          local["independent_states"]) == (65, 15, 32768, 72), "Local exhaustive result")
    expected_ref = PINS["g_remaining"]["inputs/parent_local_reference.json"]
    fresh_reference = stable_bytes(iso / "checker/local_reference.json", expected_ref)
    need(fresh_reference == stable_bytes(rem / "inputs/parent_local_reference.json", expected_ref),
         "Fresh independent local relation differs from the remaining-G parent")

    stage(output, stages, "g_isomorphism", "controls", modules["g_isomorphism"])
    stage(output, stages, "g_isomorphism", "census", modules["g_isomorphism"])
    stage(output, stages, "g_remaining", "prepare", modules["g_remaining"])
    stage(output, stages, "g_remaining", "controls", modules["g_remaining"])
    stage(output, stages, "g_remaining", "census", modules["g_remaining"])
    ic = summary(iso, "CONTROLS.json", "C61_CORE_CHECKER_CONTROLS_1")
    rc = summary(rem, "CONTROLS.json", "C61_G_CHECKER_CONTROLS_1")
    first = summary(iso, "CENSUS_SUMMARY.json", "C61_CORE_CENSUS_CHECK_1")
    second = summary(rem, "CENSUS_SUMMARY.json", "C61_G_CHECKER_CENSUS_1")
    need(ic["control_count"] == 11 and rc["control_count"] == 19, "Control census")
    need(first["labels_checked"] == 3600 and first["label_counts"] == {"CORE_REJECTED": 3600},
         "Not every isomorphic label rejected")
    need(first["witness_counts"] == {"NO_LOCAL_COMPLETION": 3164, "SHARED_EDGE_CONFLICT": 436},
         "Isomorphic witness census differs")
    need(second["labels_checked"] == second["whole_label_rejected"] == 10368
         and second["branched_labels"] == second["branches_checked"] == second["local_cores"] == 0,
         "Remaining-G complete rejection not reproduced")
    need(second["by_witness"] == {"EMPTY_SCOPE": 10044, "FORCED_DIAGONAL_CONFLICT": 324},
         "Remaining-G witness census differs")
    # Re-authenticate both the immutable source snapshot and copied inputs.
    for kind, entries in PINS.items():
        for relative, pin in entries.items():
            stable_bytes(snapshot / G_PATH / kind / relative, pin)
            stable_bytes(output / kind / relative, pin)
    receipts = {}
    for kind in PINS:
        for p in sorted((output / kind / "checker").iterdir()):
            need(p.is_file(), "Unexpected checker output directory")
            receipts[str(p.relative_to(output))] = bare_pin(p)
    size = guard(output)
    return {
        "schema": "RAMSEY61_PUBLIC_FINITE_G_REPLAY_1", "status": "PASS",
        "scope": "Fresh execution of the frozen independent local72 and guarded-G finite checkers; no SAT solver or complete formal Ramsey proof.",
        "snapshot": str(snapshot), "output": str(output),
        "script_pin": bare_pin(Path(__file__).resolve()),
        "copied_exact_inputs": copied,
        "changed_checker_source_bytes": False, "patched_checker_functions": False,
        "local_relation_recomputed": True, "local_rank": 65, "local_nullity": 15,
        "free_assignments_checked": 32768, "complete_local_states": 72,
        "fresh_reference_matches_retained_parent_bytes": True,
        "isomorphic_labels_rejected": 3600, "remaining_labels_rejected": 10368,
        "independent_checker_controls": {"g_isomorphism": 11, "g_remaining": 19},
        "checker_output_pins": receipts, "stages": stages,
        "total_process_CPU_seconds": time.process_time(),
        "wall_seconds": time.monotonic() - started,
        "peak_process_RSS_bytes": peak_rss(), "output_tree_bytes_before_receipt": size,
        "limits": {"process_CPU_seconds": CPU_LIMIT, "output_file_bytes": FILE_LIMIT,
                   "output_tree_bytes": TREE_LIMIT, "minimum_free_disk_bytes": FLOOR,
                   "observed_stage_RSS_bytes": RSS_LIMIT,
                   "RSS_enforcement_note": "Peak checked between immutable bounded stages; Linux additionally has a 2 GiB address-space cap. macOS does not supply a reliable RLIMIT_AS equivalent here."},
        "solver_calls": 0, "producer_execution": False, "snapshot_writes": False,
        "new_formal_certificate": False,
    }


def main():
    limits()
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--snapshot", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    snapshot = ordinary(args.snapshot.resolve(strict=True), directory=True)
    requested = Path(os.path.abspath(args.output))
    parent = ordinary(requested.parent.resolve(strict=True), directory=True)
    output = parent / requested.name
    need(output != snapshot and snapshot not in output.parents, "Output must be outside snapshot")
    need(not os.path.lexists(output), "Output directory must not already exist")
    need(shutil.disk_usage(parent).free >= FLOOR + TREE_LIMIT, "100 GiB disk floor plus output reserve")
    output.mkdir(mode=0o700)
    started = time.monotonic()
    try:
        result = replay(snapshot, output, started)
    except Exception as exc:
        result = {
            "schema": "RAMSEY61_PUBLIC_FINITE_G_REPLAY_1", "status": "FAIL",
            "error_type": type(exc).__name__, "error": str(exc),
            "snapshot": str(snapshot), "output": str(output),
            "total_process_CPU_seconds": time.process_time(),
            "wall_seconds": time.monotonic() - started, "peak_process_RSS_bytes": peak_rss(),
            "partial_outputs_preserved": True, "no_rejection_is_proof": True,
        }
        write_new(output / "REPLAY_RECEIPT.json",
                  (json.dumps(result, indent=2, sort_keys=True) + "\n").encode())
        raise
    write_new(output / "REPLAY_RECEIPT.json",
              (json.dumps(result, indent=2, sort_keys=True) + "\n").encode())
    guard(output)
    print(json.dumps({"status": "PASS", "receipt": str(output / "REPLAY_RECEIPT.json"),
                      "CPU_seconds": result["total_process_CPU_seconds"],
                      "peak_RSS_bytes": result["peak_process_RSS_bytes"]}), flush=True)


if __name__ == "__main__":
    main()
