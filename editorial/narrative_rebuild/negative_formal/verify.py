#!/usr/bin/env python3
"""Compile the isolated negative covariance supplement and audit its full closure."""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import os
import subprocess

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent / "negative_scaling.lean"
ROOT = HERE.parents[2]
PROJECT = ROOT / "bfgs_lean_stage1"

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--run-id", default=datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%SZ"))
args = parser.parse_args()
if not args.run_id or any(c not in "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_-" for c in args.run_id):
    raise SystemExit("run-id must use letters, digits, underscores or hyphens")
run = HERE / "runs" / args.run_id
run.mkdir(parents=True, exist_ok=False)
build = run / "build"
build.mkdir()
env = os.environ.copy()
elan = PROJECT / ".toolchain/elan"
if (elan / "bin/lake").is_file():
    env["ELAN_HOME"] = str(elan)
    env["PATH"] = str(elan / "bin") + os.pathsep + env["PATH"]
env["XDG_CACHE_HOME"] = str(PROJECT / ".cache")
env["MATHLIB_CACHE_DIR"] = str(PROJECT / ".cache/mathlib")
commands = []

def invoke(command, tag, runenv=env):
    start = datetime.datetime.now(datetime.timezone.utc).isoformat()
    result = subprocess.run(command, cwd=PROJECT, env=runenv, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log = run / (tag + ".log")
    log.write_text(result.stdout)
    commands.append({"command": command, "cwd": str(PROJECT), "started_utc": start,
                     "exit_code": result.returncode, "log": str(log.relative_to(ROOT))})
    (run / "commands.json").write_text(json.dumps(commands, indent=2) + "\n")
    if result.returncode:
        print(result.stdout)
        raise SystemExit(result.returncode)
    return result.stdout

baseline = json.loads((ROOT / "editorial/BASELINE.json").read_text())
inputs = [SOURCE, HERE / "DependencyAudit.lean", Path(__file__).resolve()]
for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json", "master_report/DECLARATION_INDEX.json"):
    path = PROJECT / name
    if digest(path) != baseline["files"][str(path.relative_to(ROOT))]:
        raise SystemExit("Pinned input differs from the recorded baseline: " + name)
    inputs.append(path)
version = invoke(["lake", "env", "lean", "--version"], "00_version").strip()
expected = (PROJECT / "lean-toolchain").read_text().strip().rsplit(":v", 1)[-1]
if not version.startswith("Lean (version " + expected + ","):
    raise SystemExit("Actual compiler differs from the pinned toolchain")
search = invoke(["lake", "env", "printenv", "LEAN_PATH"], "01_search_path").strip()
invoke(["lake", "env", "lean", "-R", str(SOURCE.parent), "-o",
        str(build / "negative_scaling.olean"), str(SOURCE)], "02_compile")
audit_env = env.copy()
audit_env["LEAN_PATH"] = str(build) + os.pathsep + search
audit_env["BFGS_NEGATIVE_AUDIT_OUT"] = str(run)
invoke(["lean", "-R", str(HERE), str(HERE / "DependencyAudit.lean")], "03_dependency_audit", audit_env)
summary = json.loads((run / "audit_summary.json").read_text())
if summary["status"] != "PASS":
    raise SystemExit("Dependency audit did not pass")
graph = json.loads((run / "dependency_graph.json").read_text())
for module in sorted({row["module"] for row in graph if row["module"].startswith("BfgsVerification")}):
    path = PROJECT / (module.replace(".", "/") + ".lean")
    if not path.is_file():
        raise SystemExit("Missing source for an imported project module: " + module)
    inputs.append(path)
summary.update({
    "lean_version": version,
    "sealed_baseline_commit": baseline["source_commit"],
    "source_commit_at_run": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
    "scope": "Mathematical covariance only. No orbit existence, local model, differentiability or all-query containment is inferred from this supplement.",
    "input_sha256": {str(path.relative_to(ROOT)): digest(path) for path in inputs},
    "output_sha256": {str(path.relative_to(ROOT)): digest(path) for path in sorted(run.iterdir()) if path.is_file()},
    "run_directory": str(run.relative_to(ROOT)),
})
(run / "SUMMARY.json").write_text(json.dumps(summary, indent=2) + "\n")
print(json.dumps(summary, indent=2))
