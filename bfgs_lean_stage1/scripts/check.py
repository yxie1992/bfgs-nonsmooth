#!/usr/bin/env python3
"""Fail-closed build/audit driver for the staged BFGS Lean project.

A static source scan is not a Lean verification. Missing executables, build
errors, missing axiom output, or unexpected axioms prevent a verified status.
Even a successful staged build does not establish the still-open matrix target.
"""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
AUDIT = ROOT / "audit"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED_LEAN = "4.19.0"


def lean_code_only(text: str) -> str:
    """Remove nested block comments, line comments and quoted strings."""
    out: list[str] = []
    i = depth = 0
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end == -1 else end
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            out.append(" ")
        else:
            out.append(text[i])
            i += 1
    if depth:
        raise ValueError("Unclosed Lean block comment")
    return "".join(out)


def record(status: dict) -> None:
    AUDIT.mkdir(exist_ok=True)
    (AUDIT / "STATUS.json").write_text(json.dumps(status, indent=2) + "\n")


def run(command: list[str], logfile: str, timeout: int) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True, timeout=timeout)
    (AUDIT / logfile).write_text(
        "$ " + " ".join(command) + "\n"
        + result.stdout + result.stderr + f"\nexit_code={result.returncode}\n"
    )
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--static-only", action="store_true")
    parser.add_argument("--timeout", type=int, default=600)
    args = parser.parse_args()
    AUDIT.mkdir(exist_ok=True)
    status: dict = {
        "timestamp_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
        "status": "NOT_CHECKED",
        "lean_typechecking_performed": False,
        "end_to_end_principal_minor_hierarchy_verified": False,
        "end_to_end_bfgs_reciprocal_growth_verified": False,
        "superquadratic_growth_verified": False,
        "verified_declarations": [],
        "warning": "A staged build is not a proof of the unimplemented matrix-to-hierarchy bridge.",
    }
    lean_files = [ROOT / "BfgsVerification.lean", ROOT / "Audit.lean"] + sorted(
        (ROOT / "BfgsVerification").glob("*.lean")
    )
    forbidden = re.compile(r"\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b")
    problems = []
    theorem_count = 0
    sources = []
    for path in lean_files:
        content = path.read_text()
        code = lean_code_only(content)
        theorem_count += len(re.findall(r"\b(?:theorem|lemma)\s+", code))
        problems += [f"{path.relative_to(ROOT)}: forbidden token {m.group(0)}" for m in forbidden.finditer(code)]
        sources.append({"path": str(path.relative_to(ROOT)), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()})
    status["sources"] = sources
    status["draft_theorem_declarations"] = theorem_count
    status["static_scan_passed"] = not problems
    status["static_scan_problems"] = problems
    if problems:
        status["status"] = "STATIC_SCAN_FAILED"
        record(status)
        print(json.dumps(status, indent=2))
        return 1
    if args.static_only:
        status["status"] = "STATIC_SCAN_ONLY_NOT_LEAN_VERIFIED"
        record(status)
        print(json.dumps(status, indent=2))
        return 0
    lake = shutil.which("lake")
    lean = shutil.which("lean")
    status["executables"] = {"lake": lake, "lean": lean}
    if lake is None or lean is None:
        status["status"] = "BLOCKED_NO_LEAN_TOOLCHAIN"
        record(status)
        print(json.dumps(status, indent=2))
        return 69
    try:
        version = run([lake, "env", "lean", "--version"], "lean_version.log", args.timeout)
        if version.returncode or f"version {EXPECTED_LEAN}" not in version.stdout:
            status["status"] = "TOOLCHAIN_VERSION_FAILED"
            record(status)
            return 1
        build = run([lake, "build"], "build.log", args.timeout)
        status["lean_typechecking_performed"] = True
        if build.returncode:
            status["status"] = "LEAN_BUILD_FAILED"
            record(status)
            return 1
        ax = run([lake, "env", "lean", "Audit.lean"], "axioms.log", args.timeout)
        if ax.returncode:
            status["status"] = "AXIOM_AUDIT_COMMAND_FAILED"
            record(status)
            return 1
        transcript = ax.stdout + ax.stderr
        expected = re.findall(r"^#print axioms (\S+)", (ROOT / "Audit.lean").read_text(), re.M)
        unexpected = []
        missing = []
        accepted = []
        for theorem in expected:
            # Lean versions differ in quote delimiters, but use this wording.
            match = re.search(re.escape(theorem) + r"['’]?\s+depends on axioms:\s*\[([^\]]*)\]", transcript)
            empty = re.search(re.escape(theorem) + r"['’]?\s+does not depend on any axioms", transcript)
            if not match and not empty:
                missing.append(theorem)
                continue
            axioms = set() if empty else {x.strip() for x in match.group(1).split(",") if x.strip()}
            excess = sorted(axioms - ALLOWED_AXIOMS)
            if excess:
                unexpected.append({"theorem": theorem, "unexpected": excess})
            else:
                accepted.append({"theorem": theorem, "axioms": sorted(axioms)})
        status["unexpected_axioms"] = unexpected
        status["missing_axiom_reports"] = missing
        if unexpected or missing:
            status["status"] = "AXIOM_AUDIT_FAILED"
            record(status)
            return 1
        status["status"] = "STAGED_LEMMAS_CHECKED_MATRIX_TARGET_STILL_OPEN"
        status["verified_declarations"] = accepted
        record(status)
        print(json.dumps(status, indent=2))
        return 0
    except subprocess.TimeoutExpired as exc:
        status["status"] = "COMMAND_TIMED_OUT"
        status["failed_command"] = exc.cmd
        record(status)
        return 124
    except OSError as exc:
        status["status"] = "EXECUTION_ERROR"
        status["error"] = str(exc)
        record(status)
        return 1


if __name__ == "__main__":
    sys.exit(main())
