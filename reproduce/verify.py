#!/usr/bin/env python3
"""Offline archive verification and exact single-C-input reconstruction.

Only `full` executes archived code: the independently reviewed, SHA-pinned
stdlib preservation verifier. No command executes a solver or certificate tool.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import stat
import subprocess
import sys
import tarfile
import time

REPOSITORY = Path(__file__).resolve().parents[1]
ARCHIVE_PIN = (375104364, "2b85cac94df0317a532aa823cfea93ac83738093fc854805896943f90d468757")
VERIFIER_PIN = (12980, "102d11f98e3ceb369e45d110d264b79734615b3544d5cdebc13efe4ac237ce92")
INDEX_PIN = (5425, "0371c357740e6cce262a055d3f998637f8f218f1d492864be2fcff78e46b222e")
C = "evidence/c_campaign/"
C_PINS = {
    "inputs/SEEDS.json": (2244507, "848f9f9420944b804ba2c38ab48a40fdd2d71f1d1054e285d82ea6d06a7346ad"),
    "inputs/BROAD_BASE_001.cnf": (39604154, "58478e3641d3ea52639566683daaea5f7a1d4112de5809f4af73ce1dfebf164f"),
    "reviews/BROAD_SECOND_TAIL_RECONCILIATION_001.json":
        (378870, "c60248e17f5bb30cc7eb27d139f9317cd2ed1748c14f02f9642725afc1df6c09"),
}
EXPECTED_FILES = 455901
EXPECTED_BYTES = 2078952544
CHUNK = 1 << 20
DISK_FLOOR = 100 << 30
MAX_EXTRACTED_BYTES = 4 << 30
MAX_MEMBERS = 1000000


def require(condition, message):
    if not condition:
        raise ValueError(message)


def identity(info):
    return (info.st_dev, info.st_ino, info.st_size, info.st_mtime_ns, info.st_ctime_ns)


def ordinary_path(path, directory=False):
    """Reject links, including any existing parent component; do not resolve them."""
    path = Path(os.path.abspath(path))
    for component in reversed((path,) + tuple(path.parents)):
        mode = component.lstat().st_mode
        require(stat.S_ISDIR(mode) if component != path or directory else stat.S_ISREG(mode),
                "Nonordinary path component: " + str(component))
    return path


def new_path(path):
    path = Path(os.path.abspath(path))
    # Resolve the caller's existing parent (e.g. macOS /tmp -> /private/tmp).
    # Archive member paths never take this path and cannot introduce symlinks.
    path = ordinary_path(path.parent.resolve(strict=True), directory=True) / path.name
    require(not os.path.lexists(path), "Output must not already exist: " + str(path))
    return path


def outside(path, root):
    require(path != root and root not in path.parents, "Output must be outside the evidence snapshot")


def hash_stream(stream):
    stream.seek(0)
    digest, size = hashlib.sha256(), 0
    for block in iter(lambda: stream.read(CHUNK), b""):
        digest.update(block)
        size += len(block)
    stream.seek(0)
    return size, digest.hexdigest()


def fingerprint(path):
    path = ordinary_path(path)
    before = path.stat()
    with path.open("rb") as stream:
        require(identity(os.fstat(stream.fileno())) == identity(before), "Input replaced at open")
        result = hash_stream(stream)
        require(identity(os.fstat(stream.fileno())) == identity(before), "Input changed while reading")
    require(identity(path.stat()) == identity(before), "Input changed after reading")
    return result


def pinned_bytes(path, expected, maximum=8 << 20):
    path = ordinary_path(path)
    before = path.stat()
    require(before.st_size <= maximum, "Oversize metadata")
    with path.open("rb") as stream:
        require(identity(os.fstat(stream.fileno())) == identity(before), "Metadata replaced")
        data = stream.read(maximum + 1)
        require(identity(os.fstat(stream.fileno())) == identity(before), "Metadata changed")
    require(identity(path.stat()) == identity(before), "Metadata replaced after read")
    require((len(data), hashlib.sha256(data).hexdigest()) == expected, "Pinned metadata differs: " + str(path))
    return data


def archive_authenticate(stream, expected=ARCHIVE_PIN):
    stream.seek(0)
    start = stream.read(128)
    require(not start.startswith(b"version https://git-lfs.github.com/spec/v1"),
            "This is a Git LFS pointer; fetch the archive or supply --archive /offline/evidence-v1.tar.gz")
    actual = hash_stream(stream)
    require(actual == expected, "Archive SHA256 or byte size mismatch")
    return {"bytes": actual[0], "sha256": actual[1]}


def member_path(name):
    require(isinstance(name, str) and name and "\\" not in name and "\x00" not in name,
            "Unsafe archive path")
    p = PurePosixPath(name)
    require(not p.is_absolute() and bool(p.parts) and str(p) == name and
            all(part not in (".", "..") and ":" not in part for part in p.parts) and
            len(name) <= 2048 and len(p.parts) <= 80, "Unsafe archive path: " + name)
    return p


def disk_room(path, reserve=0):
    require(shutil.disk_usage(path).free >= DISK_FLOOR + reserve,
            "Insufficient free space to preserve the 100 GiB disk floor")


def extract_archive(stream, destination, disk_guard=disk_room,
                    max_bytes=MAX_EXTRACTED_BYTES, max_members=MAX_MEMBERS):
    """Never use extractall: accept ordinary files/directories, not links or devices.

    Ownership, modes, timestamps and archive xattrs are deliberately not restored.
    Failed partial outputs remain for inspection. The target must be new.
    """
    destination = new_path(destination)
    disk_guard(destination.parent, 2 * max_bytes)
    destination.mkdir(mode=0o700)
    seen, directories = set(), {PurePosixPath(".")}
    total, files, next_disk_check = 0, 0, 128 << 20
    stream.seek(0)
    with tarfile.open(fileobj=stream, mode="r|gz") as archive:
        for member in archive:
            path = member_path(member.name)
            require(member.name not in seen, "Duplicate archive member: " + member.name)
            seen.add(member.name)
            require(len(seen) <= max_members, "Archive member ceiling exceeded")
            require(member.isdir() or member.isreg(), "Archive links/devices/special members are forbidden")
            require(not member.issparse(), "Sparse archive members are forbidden")
            require(member.size >= 0 and (not member.isdir() or member.size == 0), "Invalid archive member size")
            require(member.size <= 1 << 30 and total + member.size <= max_bytes, "Archive payload ceiling exceeded")
            for parent in reversed(path.parents):
                if parent not in directories:
                    target = destination.joinpath(*parent.parts)
                    require(not os.path.lexists(target), "Archive file/directory collision")
                    target.mkdir(mode=0o700)
                    directories.add(parent)
            target = destination.joinpath(*path.parts)
            if member.isdir():
                if path not in directories:
                    require(not os.path.lexists(target), "Archive directory collision")
                    target.mkdir(mode=0o700)
                    directories.add(path)
            else:
                require(not os.path.lexists(target), "Archive file collision")
                source = archive.extractfile(member)
                require(source is not None, "Missing archive file body")
                remaining = member.size
                with source, target.open("xb") as out:
                    while remaining:
                        block = source.read(min(CHUNK, remaining))
                        require(bool(block), "Truncated archive member")
                        out.write(block)
                        remaining -= len(block)
                        total += len(block)
                        if total >= next_disk_check:
                            disk_guard(destination)
                            next_disk_check = total + (128 << 20)
                target.chmod(0o400)
                files += 1
            # No hardlinks are accepted, so tarfile's historical member cache is unnecessary.
            archive.members.clear()
    disk_guard(destination)
    return {"members": len(seen), "files": files, "uncompressed_bytes": total}


def check_verifier_result(result):
    require(result["status"] == "PASS_STAGING_BYTES_AND_CUSTODY" and
            result["total_files"] == EXPECTED_FILES and result["total_bytes"] == EXPECTED_BYTES and
            result["manifest_index_sha256"] == INDEX_PIN[1] and
            result["new_solver_calls"] == result["original_source_reads"] == 0,
            "Unexpected full verification result")
    custody = result["custody"]
    require(custody["status"] == "PASS_STAGED_C_AND_FINAL_CUSTODY" and
            custody["effective_dual_native_owners"] == 456 and custody["native_logs"] == 1843 and
            custody["result_counts"] == {"restricted": 914, "original_broad": 912, "first_tail": 13, "second_tail": 4} and
            custody["formal_certificate_verified"] is False, "Unexpected custody census")


def verify_extracted(snapshot):
    pinned_bytes(snapshot / "manifest/index.json", INDEX_PIN)
    script = snapshot / "tools/verify_staging.py"
    pinned_bytes(script, VERIFIER_PIN)
    # Isolated mode ignores PYTHONPATH and user site-packages; -B prevents evidence writes.
    run = subprocess.run([sys.executable, "-I", "-B", str(script)], cwd=snapshot,
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=False)
    require(run.returncode == 0, "Archived verifier failed:\n" + run.stderr[-8000:])
    result = json.loads(run.stdout)
    check_verifier_result(result)
    pinned_bytes(script, VERIFIER_PIN)
    pinned_bytes(snapshot / "manifest/index.json", INDEX_PIN)
    return result


def edge_var(u, v, color):
    require(all(type(n) is int for n in (u, v, color)) and 0 <= u < v < 61 and 0 <= color < 4,
            "Invalid physical seed edge")
    return 4 * (u * (121 - u) // 2 + v - u - 1) + color + 1


def materialize_c(snapshot, case, output):
    snapshot = ordinary_path(snapshot, directory=True)
    output = new_path(output)
    outside(output, snapshot)
    require(re.fullmatch(r"R3_[0-9]{3}", case) and int(case[3:]) < 456, "Choose R3_000 through R3_455")
    seeds = json.loads(pinned_bytes(snapshot / (C + "inputs/SEEDS.json"), C_PINS["inputs/SEEDS.json"]))
    accepted = json.loads(pinned_bytes(snapshot / (C + "reviews/BROAD_SECOND_TAIL_RECONCILIATION_001.json"),
                                     C_PINS["reviews/BROAD_SECOND_TAIL_RECONCILIATION_001.json"]))
    ids = ["R3_%03d" % i for i in range(456)]
    require(seeds["count"] == 456 and [s["id"] for s in seeds["seeds"]] == ids, "Seed census differs")
    rows = accepted["effective_acceptance_records"]
    require(accepted["status"] == "PASS_ALL456_BROADER_DUAL_NATIVE_UNSAT" and [r["id"] for r in rows] == ids,
            "Accepted C census differs")
    seed, row = seeds["seeds"][int(case[3:])], rows[int(case[3:])]
    units = [edge_var(*e) for e in seed["unit_colors"]] + [-edge_var(*e) for e in seed["non_color"]]
    tail = "".join("%d 0\n" % literal for literal in units).encode("ascii")
    base = ordinary_path(snapshot / (C + "inputs/BROAD_BASE_001.cnf"))
    before = base.stat()
    disk_room(output.parent, C_PINS["inputs/BROAD_BASE_001.cnf"][0] + (4 << 20))
    with base.open("rb") as stream:
        require(identity(os.fstat(stream.fileno())) == identity(before), "Base replaced")
        require(hash_stream(stream) == C_PINS["inputs/BROAD_BASE_001.cnf"], "Broader base differs")
        header = stream.readline(128)
        require(header == b"p cnf 439723 1880888\n", "Unexpected broader base header")
        digest, size = hashlib.sha256(), 0
        new_header = ("p cnf 439723 %d\n" % (1880888 + len(units))).encode("ascii")
        with output.open("xb") as out:
            for block in (new_header,):
                out.write(block); digest.update(block); size += len(block)
            for block in iter(lambda: stream.read(CHUNK), b""):
                out.write(block); digest.update(block); size += len(block)
            out.write(tail); digest.update(tail); size += len(tail)
        require(identity(os.fstat(stream.fileno())) == identity(before) and identity(base.stat()) == identity(before),
                "Base changed during reconstruction")
    require(digest.hexdigest() == row["formula_sha256"], "Reconstructed formula differs from accepted result")
    require(fingerprint(output) == (size, row["formula_sha256"]), "Output rehash differs")
    output.chmod(0o400)
    disk_room(output.parent)
    return {"status": "PASS_EXACT_ACCEPTED_C_FORMULA", "case": case, "output": str(output),
            "bytes": size, "sha256": row["formula_sha256"], "variables": 439723,
            "clauses": 1880888 + len(units), "seed_units": len(units), "source_pins": C_PINS,
            "scope": "Exact formula-byte reproduction only; no new solver answer or mathematical audit"}


def verify_c_all(snapshot):
    """Hash every original C input using shared prefix states; write no CNFs."""
    snapshot = ordinary_path(snapshot, directory=True)
    seeds = json.loads(pinned_bytes(snapshot / (C + "inputs/SEEDS.json"), C_PINS["inputs/SEEDS.json"]))
    accepted = json.loads(pinned_bytes(snapshot / (C + "reviews/BROAD_SECOND_TAIL_RECONCILIATION_001.json"),
                                     C_PINS["reviews/BROAD_SECOND_TAIL_RECONCILIATION_001.json"]))
    ids = ["R3_%03d" % i for i in range(456)]
    require(seeds["count"] == 456 and [s["id"] for s in seeds["seeds"]] == ids, "Seed census differs")
    rows = accepted["effective_acceptance_records"]
    require(accepted["status"] == "PASS_ALL456_BROADER_DUAL_NATIVE_UNSAT" and
            accepted["effective_dual_native_UNSAT"] == 456 and not accepted["unresolved"] and
            [r["id"] for r in rows] == ids, "Accepted C census differs")
    suffixes = []
    headers = {}
    for seed in seeds["seeds"]:
        units = [edge_var(*e) for e in seed["unit_colors"]] + [-edge_var(*e) for e in seed["non_color"]]
        suffixes.append((len(units), "".join("%d 0\n" % literal for literal in units).encode("ascii")))
        headers[len(units)] = ("p cnf 439723 %d\n" % (1880888 + len(units))).encode("ascii")
    states = {count: hashlib.sha256(header) for count, header in headers.items()}
    base = ordinary_path(snapshot / (C + "inputs/BROAD_BASE_001.cnf"))
    before = base.stat()
    with base.open("rb") as stream:
        require(identity(os.fstat(stream.fileno())) == identity(before), "Base replaced")
        require(hash_stream(stream) == C_PINS["inputs/BROAD_BASE_001.cnf"], "Broader base differs")
        old_header = stream.readline(128)
        require(old_header == b"p cnf 439723 1880888\n", "Unexpected broader base header")
        body_bytes = 0
        for block in iter(lambda: stream.read(CHUNK), b""):
            body_bytes += len(block)
            for state in states.values():
                state.update(block)
        require(identity(os.fstat(stream.fileno())) == identity(before) and identity(base.stat()) == identity(before),
                "Base changed during reconstruction")
    record_digest, logical_bytes = hashlib.sha256(), 0
    for case, row, (unit_count, suffix) in zip(ids, rows, suffixes):
        state = states[unit_count].copy()
        state.update(suffix)
        require(state.hexdigest() == row["formula_sha256"], "Reconstructed formula differs: " + case)
        size = len(headers[unit_count]) + body_bytes + len(suffix)
        record = {"case_id": case, "sha256": state.hexdigest(), "bytes": size,
                  "variables": 439723, "clauses": 1880888 + unit_count}
        record_digest.update((json.dumps(record, sort_keys=True, separators=(",", ":")) + "\n").encode())
        logical_bytes += size
    return {"status": "PASS_ALL456_EXACT_ACCEPTED_C_FORMULAS", "formulas": 456,
            "logical_formula_bytes": logical_bytes, "materialized_formula_files": 0,
            "ordered_formula_records_sha256": record_digest.hexdigest(), "source_pins": C_PINS,
            "scope": "All original broader C formula hashes reconstructed; no solver or mathematical cover replay"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    for name in ("check", "full"):
        cmd = commands.add_parser(name)
        cmd.add_argument("--archive", type=Path, default=REPOSITORY / "archives/evidence-v1.tar.gz")
        cmd.add_argument("--receipt", type=Path, required=name == "full")
        if name == "full":
            cmd.add_argument("--extract-to", type=Path, required=True)
    cmd = commands.add_parser("materialize-c")
    cmd.add_argument("--snapshot", type=Path, required=True)
    cmd.add_argument("--case", required=True)
    cmd.add_argument("--output", type=Path, required=True)
    cmd.add_argument("--receipt", type=Path, required=True)
    cmd = commands.add_parser("verify-c-all")
    cmd.add_argument("--snapshot", type=Path, required=True)
    cmd.add_argument("--receipt", type=Path, required=True)
    args = parser.parse_args()
    start = time.process_time()
    receipt = new_path(args.receipt) if args.receipt else None
    if args.command in ("materialize-c", "verify-c-all"):
        snapshot = args.snapshot.resolve(strict=True)
        outside(receipt, snapshot)
        if args.command == "materialize-c":
            output = new_path(args.output)
            require(receipt != output, "Receipt and CNF paths must differ")
            result = materialize_c(snapshot, args.case, output)
        else:
            result = verify_c_all(snapshot)
    else:
        archive = ordinary_path(args.archive)
        if receipt:
            require(receipt != archive, "Receipt must not overwrite archive")
        before = archive.stat()
        with archive.open("rb") as stream:
            require(identity(os.fstat(stream.fileno())) == identity(before), "Archive replaced at open")
            pin = archive_authenticate(stream)
            result = {"status": "PASS_ARCHIVE_SHA256_ONLY", "archive": str(archive), "archive_pin": pin,
                      "scope": "Authenticated release archive bytes; payload/custody not checked by this command"}
            if args.command == "full":
                destination = new_path(args.extract_to)
                outside(receipt, destination)
                extraction = extract_archive(stream, destination)
                require(identity(os.fstat(stream.fileno())) == identity(before), "Archive changed during extraction")
                verification = verify_extracted(destination)
                result = {"status": "PASS_PORTABLE_ARCHIVE_AND_CUSTODY", "archive": str(archive), "archive_pin": pin,
                          "snapshot": str(destination), "extraction": extraction, "verification": verification,
                          "scope": "Byte preservation and recorded C/final custody; no solver or certificate rerun"}
            require(identity(os.fstat(stream.fileno())) == identity(before) and identity(archive.stat()) == identity(before),
                    "Archive changed")
    result.update({"schema": "RAMSEY61_PORTABLE_REPRODUCTION_1", "new_solver_calls": 0,
                   "formal_certificate_verified": False, "original_source_reads": 0,
                   "driver_CPU_seconds": time.process_time() - start})
    # No receipt or bytecode is written inside the archived evidence.
    if receipt:
        with receipt.open("x", encoding="utf-8") as stream:
            json.dump(result, stream, indent=2, sort_keys=True); stream.write("\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, KeyError, TypeError, tarfile.TarError, subprocess.SubprocessError) as error:
        print("FAIL: " + str(error), file=sys.stderr)
        sys.exit(1)
