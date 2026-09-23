#!/usr/bin/env python3
"""Hash-checked, source-only Lean build. Python standard library; no prior project .oleans."""
from __future__ import annotations
import argparse
import concurrent.futures as cf
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
import uuid

TOOLCHAIN = "leanprover/lean4:v4.32.1"
MATHLIB_REV = "520045ab14e26149ee970e2e617ca04b09bde5d6"
MODULE = re.compile(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*\Z")
DIGEST = re.compile(r"[0-9a-f]{64}\Z")

class Invalid(RuntimeError):
    pass

def require(test, message):
    if not test:
        raise Invalid(message)

def utc():
    return dt.datetime.now(dt.timezone.utc).isoformat()

def sha(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as f:
        for block in iter(lambda: f.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()

def write_once(path, data):
    with Path(path).open("x", encoding="utf-8") as f:
        json.dump(data, f, indent=2, sort_keys=True)
        f.write("\n")

def inside(root, rel):
    require(isinstance(rel, str) and not Path(rel).is_absolute(), f"Not a relative path: {rel}")
    p = (root / rel).resolve()
    require(p.is_relative_to(root), f"Path escapes package: {rel}")
    return p

def uncomments(text):
    """Remove nested Lean comments, retaining quoted strings and line positions."""
    out = []; i = 0; depth = 0; quoted = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i): depth += 1; out.extend("  "); i += 2
            elif text.startswith("-/", i): depth -= 1; out.extend("  "); i += 2
            else: out.append("\n" if text[i] == "\n" else " "); i += 1
        elif quoted:
            out.append(text[i])
            if text[i] == "\\" and i + 1 < len(text):
                out.append(text[i+1]); i += 2; continue
            if text[i] == '"': quoted = False
            i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            if j < 0: j = len(text)
            out.extend(" " * (j-i)); i = j
        elif text.startswith("/-", i): depth = 1; out.extend("  "); i += 2
        else:
            quoted = text[i] == '"'; out.append(text[i]); i += 1
    require(depth == 0 and not quoted, "Unterminated Lean comment or string")
    return "".join(out)

def imports_of(text):
    code = uncomments(text)
    imports = []
    for line in code.splitlines():
        match = re.match(r"^\s*(?:public\s+)?import\s+(.*)$", line)
        if match:
            names = match.group(1).split()
            require(names and all(MODULE.fullmatch(x) for x in names), "Unsupported import syntax: " + line)
            imports.extend(names)
    return imports

def certificate_command(text):
    # Conservative: also reject a local command definition mentioning these names.
    return bool(re.search(r"\b(?:checked_lrat_proof|lrat_proof|lrat)\b", uncomments(text)))

def checked_pin(root, record):
    require(isinstance(record, dict) and DIGEST.fullmatch(record.get("sha256", "")), "Invalid hash record")
    p = inside(root, record["path"])
    require(p.is_file(), f"Missing file: {record['path']}")
    require(sha(p) == record["sha256"], f"Hash mismatch: {record['path']}")
    return p

def file_records(value):
    if isinstance(value, list): return value
    require(isinstance(value, dict), "files/data must be a list or a path map")
    return [dict(v, path=k) if isinstance(v, dict) else {"path": k, "sha256": v}
            for k, v in value.items()]

def static_check(root, manifest, targets, no_replay):
    require(manifest.get("toolchain") == TOOLCHAIN, "Unrecognized toolchain pin")
    require(manifest.get("mathlib_rev") == MATHLIB_REV, "Unrecognized Mathlib pin")
    require((root/"lean-toolchain").read_text().strip() == TOOLCHAIN, "lean-toolchain differs from manifest")
    files = file_records(manifest.get("files", []))
    required = {"lean-toolchain", "lakefile.toml", "lake-manifest.json", "build.py"}
    require(required <= {r["path"] for r in files}, "Manifest must pin all four build control files")
    for r in files: checked_pin(root, r)
    data = {r["path"]: r for r in file_records(manifest.get("data", []))}
    for r in data.values(): checked_pin(root, r)
    modules = manifest["modules"]
    require(isinstance(modules, dict) and modules, "Empty module map")
    for m, row in modules.items():
        require(MODULE.fullmatch(m), "Invalid module: " + m)
        require(row["path"] == "src/" + m.replace(".", "/") + ".lean", "Noncanonical module path: " + m)
        source = checked_pin(root, row)
        text = source.read_text(encoding="utf-8")
        require(imports_of(text) == row["imports"], "Import declaration mismatch: " + m)
        require(not re.search(r"^\s*#eval\b", uncomments(text), re.M), "Unapproved #eval in source: " + m)
        for raw in re.findall(r'\binclude_str\s+"([^"\n]+)"', uncomments(text)):
            p = (source.parent/raw).resolve()
            require(p.is_relative_to(root), "Embedded data escapes package: " + m)
            require(p.relative_to(root).as_posix() in data, "Unpinned embedded data: " + str(p))
    roots = targets or manifest.get("roots", [])
    require(roots and all(m in modules for m in roots), "Unknown or empty build target")
    selected = set(); stack = set()
    def visit(m):
        if m not in modules or m in selected: return
        require(m not in stack, "Import cycle at " + m)
        stack.add(m)
        for d in modules[m]["imports"]: visit(d)
        stack.remove(m); selected.add(m)
    for m in roots: visit(m)
    blocked = sorted(m for m in selected if certificate_command((root/modules[m]["path"]).read_text()))
    require(not no_replay or not blocked, "Certificate replay forbidden; selected closure contains: " + ", ".join(blocked))
    return modules, selected, data, blocked

def command_output(cmd, cwd):
    r = subprocess.run(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    require(r.returncode == 0, "Command failed: " + repr(cmd) + "\n" + r.stderr)
    return r.stdout.strip()

def runtime(root, manifest):
    require(os.environ.get("LEAN_PATH"), "Run this command through `lake env python3 build.py`")
    prefix = Path(command_output(["lean", "--print-prefix"], root)).resolve()
    binary = prefix/"bin"/("lean.exe" if os.name == "nt" else "lean")
    require(binary.is_file(), "Lean compiler not found beneath its prefix")
    version = command_output([str(binary), "--version"], root)
    require(re.search(r"\bLean \(version 4\.32\.1(?:,|\))", version), "Wrong compiler version: " + version)
    lake = json.loads((root/"lake-manifest.json").read_text())
    require(lake.get("packagesDir") == ".lake/packages", "Unexpected Lake package directory")
    packages = []; paths = []
    for p in lake["packages"]:
        require(p.get("type") == "git", "Only pinned Git dependencies are supported")
        name, revision = p["name"], p["rev"]
        require(re.fullmatch(r"[A-Za-z0-9_-]+", name), "Invalid package name")
        directory = root/".lake/packages"/name
        actual = command_output(["git", "-C", str(directory), "rev-parse", "HEAD"], root)
        require(actual == revision, "Dependency revision mismatch: " + name)
        dirty = command_output(["git", "-C", str(directory), "status", "--porcelain", "--untracked-files=no"], root)
        require(not dirty, "Tracked dependency files are modified: " + name)
        lib = directory/".lake/build/lib/lean"
        # A locked tool package need not have Lean artifacts unless this closure imports it.
        # Required imports are checked individually before their consumer compiles.
        if lib.is_dir(): paths.append(lib.resolve())
        packages.append({"name": name, "revision": actual, "library_available": lib.is_dir()})
    require(any(p["name"] == "mathlib" and p["revision"] == MATHLIB_REV for p in packages), "Mathlib revision missing")
    paths.append(prefix/"lib/lean")
    return binary, {"path": str(binary), "sha256": sha(binary), "version": version,
                    "toolchain": TOOLCHAIN, "packages": packages}, paths

def artifact_pins(path):
    # Lean may use executable code and private declarations alongside .olean.
    candidates = [path, Path(str(path)+".private"), Path(str(path)+".server"), path.with_suffix(".ir")]
    return [{"path": str(p), "sha256": sha(p), "bytes": p.stat().st_size} for p in candidates if p.is_file()]

def check_artifacts(pins):
    for p in pins:
        require(Path(p["path"]).is_file() and sha(p["path"]) == p["sha256"], "Imported artifact changed: " + p["path"])

def compile_one(m, root, row, data, output, run, binary, compiler, paths, project_modules):
    started = time.monotonic(); attempt = run/"modules"/m; attempt.mkdir(parents=True)
    receipt = {"module": m, "started_utc": utc(), "source": row, "status": "FAIL",
               "cpu_threads": 1, "resource_caps": None, "compiler_sha256": compiler["sha256"]}
    try:
        source = checked_pin(root, row)
        embedded = [data[((source.parent/raw).resolve()).relative_to(root).as_posix()]
                    for raw in re.findall(r'\binclude_str\s+"([^"\n]+)"', uncomments(source.read_text()))]
        for r in embedded: checked_pin(root, r)
        require(sha(binary) == compiler["sha256"], "Compiler changed during build")
        imports = []
        for d in row["imports"]:
            rel = Path(*d.split(".")).with_suffix(".olean")
            search = [output] if d in project_modules else paths
            found = next((p/rel for p in search if (p/rel).is_file()), None)
            require(found is not None, "Missing checked import " + d + " for " + m)
            imports.extend(artifact_pins(found))
        receipt["import_artifacts"] = imports; check_artifacts(imports)
        artifact = attempt/"output.olean"
        cmd = [str(binary), "-j1", "-o", str(artifact), str(source)]
        env = dict(os.environ)
        # Deliberately discard inherited project output paths.
        env["LEAN_PATH"] = os.pathsep.join(map(str, [output]+paths))
        receipt["command"] = cmd; receipt["LEAN_PATH"] = env["LEAN_PATH"]
        options = {"start_new_session": True} if os.name != "nt" else {"creationflags": subprocess.CREATE_NEW_PROCESS_GROUP}
        with (attempt/"lean.log").open("xb") as log:
            child = subprocess.Popen(cmd, cwd=root/"src", env=env, stdout=log, stderr=subprocess.STDOUT, **options)
            receipt["pid"] = child.pid
            if hasattr(os, "wait4"):
                _, status, usage = os.wait4(child.pid, 0)
                child.returncode = os.waitstatus_to_exitcode(status)
                receipt["CPU_seconds"] = usage.ru_utime + usage.ru_stime
                receipt["peak_RSS_bytes"] = usage.ru_maxrss * (1 if sys.platform == "darwin" else 1024)
            else:
                child.wait(); receipt["CPU_seconds"] = None; receipt["peak_RSS_bytes"] = None
        receipt["exit_code"] = child.returncode
        require(child.returncode == 0, "Lean failed; see immutable lean.log")
        checked_pin(root, row)
        for r in embedded: checked_pin(root, r)
        check_artifacts(imports)
        require(sha(binary) == compiler["sha256"], "Compiler changed during build")
        require(artifact.is_file(), "Successful compiler did not emit an artifact")
        destination = output/Path(*m.split(".")).with_suffix(".olean")
        destination.parent.mkdir(parents=True, exist_ok=True)
        require(not destination.exists(), "Refusing to overwrite accepted output")
        for a in artifact_pins(artifact):
            suffix = a["path"][len(str(artifact)):]
            target = Path(str(destination)+suffix) if not a["path"].endswith(".ir") else destination.with_suffix(".ir")
            shutil.copyfile(a["path"], target)
        receipt.update(status="PASS", artifact_sha256=sha(artifact), artifact_bytes=artifact.stat().st_size)
    except Exception as e:
        receipt["error"] = str(e)
    receipt["finished_utc"] = utc(); receipt["elapsed_seconds"] = time.monotonic()-started
    log = attempt/"lean.log"
    if log.exists(): receipt["log_sha256"] = sha(log)
    write_once(attempt/"receipt.json", receipt)
    return receipt

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--jobs", type=int, default=1, help="parallel compiler processes, 1 through 8 (each Lean uses -j1)")
    ap.add_argument("--target", action="append", default=[], help="build this module and its complete dependency closure")
    ap.add_argument("--no-certificate-replay", action="store_true", help="reject any selected closure with an LRAT command")
    ap.add_argument("--validate-only", action="store_true", help="check source/configuration hashes and graph; do not launch Lean")
    args = ap.parse_args(); require(1 <= args.jobs <= 8, "--jobs must be between 1 and 8")
    root = Path(__file__).resolve().parent
    run = root/".build/runs"/(dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ_")+uuid.uuid4().hex[:8])
    run.mkdir(parents=True); output = run/"lib"; output.mkdir()
    result = {"started_utc": utc(), "jobs": args.jobs, "status": "FAIL", "new_solver_calls": 0,
              "baseline_project_artifacts_reused": False, "run": str(run)}
    try:
        manifest_path = root/"SOURCE_MANIFEST.json"
        manifest = json.loads(manifest_path.read_text()); result["manifest_sha256"] = sha(manifest_path)
        modules, selected, data, cert = static_check(root, manifest, args.target, args.no_certificate_replay)
        result.update(targets=args.target or manifest["roots"], selected_modules=len(selected),
                      certificate_command_modules=cert,
                      classification_modules=sum(bool(modules[m].get("classification_source")) for m in selected))
        if args.validate_only:
            result["status"] = "PASS_STATIC_ONLY"
        else:
            binary, compiler, paths = runtime(root, manifest); result["compiler"] = compiler
            done = set(); pending = set(selected); active = {}; failures = {}; interrupted = False
            with cf.ThreadPoolExecutor(max_workers=args.jobs) as pool:
                while pending or active:
                    if not failures and not interrupted:
                        ready = sorted(m for m in pending if set(modules[m]["imports"]) & selected <= done)
                        for m in ready[:args.jobs-len(active)]:
                            pending.remove(m)
                            active[pool.submit(compile_one, m, root, modules[m], data, output, run, binary, compiler, paths, modules)] = m
                    require(active or failures or interrupted or not pending, "Dependency graph stalled")
                    if not active: break
                    try: finished, _ = cf.wait(active, return_when=cf.FIRST_COMPLETED)
                    except KeyboardInterrupt:
                        interrupted = True; print("Interrupted: finishing active compilers; no new admissions.", flush=True); continue
                    for future in finished:
                        m = active.pop(future); r = future.result()
                        if r["status"] == "PASS": done.add(m)
                        else: failures[m] = r.get("error", "Unknown failure")
                        print(f"{r['status']} {m} ({len(done)}/{len(selected)})", flush=True)
            require(sha(manifest_path) == result["manifest_sha256"], "Source manifest changed during build")
            for row in modules.values(): checked_pin(root, row)
            for row in data.values(): checked_pin(root, row)
            for row in file_records(manifest["files"]): checked_pin(root, row)
            result.update(completed=sorted(done), pending=sorted(pending), failures=failures, interrupted=interrupted)
            result["status"] = "PASS" if len(done) == len(selected) and not failures and not interrupted else "FAIL"
    except Exception as e:
        result["error"] = str(e)
    result["finished_utc"] = utc(); write_once(run/"BUILD_RESULT.json", result)
    print(json.dumps(result, indent=2)); return 0 if result["status"].startswith("PASS") else 1

if __name__ == "__main__":
    try: sys.exit(main())
    except Invalid as e: print(str(e), file=sys.stderr); sys.exit(2)
