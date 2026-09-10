#!/usr/bin/env python3
"""Fail-closed build/audit driver for the BFGS Lean project.

A static source scan is not a Lean verification. Missing executables, build
errors, missing axiom output, or unexpected axioms prevent a verified status.
A successful helper build alone is insufficient: exact target inhabitants and
compiled-environment axiom reports establish the matrix-run target status.
"""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
AUDIT = ROOT / "audit"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED_LEAN = "4.19.0"
EXPECTED_MATHLIB = "c44e0c8ee63ca166450922a373c7409c5d26b00b"
TARGETS = {
    "end_to_end_principal_minor_hierarchy_verified":
        ("BfgsVerification.principalMinorHierarchy", "BfgsVerification.PrincipalMinorHierarchyTarget"),
    "end_to_end_bfgs_reciprocal_growth_verified":
        ("BfgsVerification.reciprocalGrowth", "BfgsVerification.ReciprocalGrowthTarget"),
    "superquadratic_growth_verified":
        ("BfgsVerification.superquadraticReciprocalGrowth", "BfgsVerification.SuperquadraticReciprocalTarget"),
}


def theorem_names(code: str) -> list[str]:
    """Discover explicit declarations; compiled-environment enumeration audits
    these plus Lean-generated theorem declarations. Fail closed if one is absent.
    """
    scopes: list[tuple[str, str]] = []
    names: list[str] = []
    for line in code.splitlines():
        line = line.strip()
        namespace = re.match(r"namespace\s+(\S+)", line)
        section = re.match(r"(?:noncomputable\s+)?section(?:\s+(\S+))?$", line)
        ending = re.match(r"end(?:\s+(\S+))?$", line)
        if namespace:
            scopes.append(("namespace", namespace.group(1)))
        elif section:
            scopes.append(("section", section.group(1) or ""))
        elif ending and scopes:
            scopes.pop()
        theorem = re.search(r"\b(?:theorem|lemma)\s+([\w'.]+)", line)
        if theorem:
            name = theorem.group(1)
            prefix = ".".join(value for kind, value in scopes if kind == "namespace")
            names.append(name.removeprefix("_root_.") if name.startswith("_root_.")
                         else f"{prefix}.{name}" if prefix else name)
    return names


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
    local_elan = ROOT / ".toolchain" / "elan"
    if (local_elan / "bin" / "lake").is_file():
        os.environ["ELAN_HOME"] = str(local_elan)
        os.environ["PATH"] = str(local_elan / "bin") + os.pathsep + os.environ.get("PATH", "")
    os.environ["XDG_CACHE_HOME"] = str(ROOT / ".cache")
    os.environ["MATHLIB_CACHE_DIR"] = str(ROOT / ".cache" / "mathlib")
    AUDIT.mkdir(exist_ok=True)
    status: dict = {
        "timestamp_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
        "status": "NOT_CHECKED",
        "lean_typechecking_performed": False,
        "end_to_end_principal_minor_hierarchy_verified": False,
        "end_to_end_bfgs_reciprocal_growth_verified": False,
        "superquadratic_growth_verified": False,
        "verified_declarations": [],
        "warning": "Verification is pending for this invocation; success requires the complete build and axiom audit.",
    }
    lean_files = [ROOT / "BfgsVerification.lean", ROOT / "Audit.lean"] + sorted(
        (ROOT / "BfgsVerification").glob("*.lean")
    )
    forbidden = re.compile(r"\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b")
    problems = []
    theorem_count = 0
    declarations: dict[str, str] = {}
    sources = []
    for path in lean_files:
        content = path.read_text()
        code = lean_code_only(content)
        theorem_count += len(re.findall(r"\b(?:theorem|lemma)\s+", code))
        for name in theorem_names(code):
            declarations[name] = str(path.relative_to(ROOT))
        problems += [f"{path.relative_to(ROOT)}: forbidden token {m.group(0)}" for m in forbidden.finditer(code)]
        sources.append({"path": str(path.relative_to(ROOT)), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()})
    status["sources"] = sources
    status["explicit_theorem_declarations"] = theorem_count
    if len(declarations) != theorem_count:
        problems.append("Explicit theorem discovery mismatch; audit coverage cannot be certified")
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
        manifest = json.loads((ROOT / "lake-manifest.json").read_text())
        mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
        revision = run(["git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD"],
                       "mathlib_revision.log", args.timeout)
        if mathlib["rev"] != EXPECTED_MATHLIB or revision.stdout.strip() != EXPECTED_MATHLIB:
            status["status"] = "DEPENDENCY_REVISION_FAILED"
            record(status)
            return 1
        status["mathlib_revision"] = EXPECTED_MATHLIB
        version = run([lake, "env", "lean", "--version"], "lean_version.log", args.timeout)
        if version.returncode or not re.search(r"version " + re.escape(EXPECTED_LEAN) + r"(?:,|\s|\))", version.stdout):
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
        reports = [json.loads(line.removeprefix("BFGS_AUDIT "))
                   for line in transcript.splitlines() if line.startswith("BFGS_AUDIT ")]
        counts = re.findall(r"^BFGS_AUDIT_COUNT (\d+)$", transcript, re.M)
        if len(counts) != 1 or int(counts[0]) != len(reports) or not reports:
            status["status"] = "AXIOM_INVENTORY_FAILED"
            record(status)
            return 1
        inventory = {item["theorem"]: item for item in reports}
        if len(inventory) != len(reports):
            status["status"] = "DUPLICATE_AXIOM_REPORT"
            record(status)
            return 1
        unexpected = []
        missing = []
        accepted = []
        missing = sorted(set(declarations) - set(inventory))
        for theorem, item in sorted(inventory.items()):
            axioms = set(item["axioms"])
            excess = sorted(axioms - ALLOWED_AXIOMS)
            if excess:
                unexpected.append({"theorem": theorem, "unexpected": excess})
            else:
                if theorem in declarations:
                    accepted.append({**item, "axioms": sorted(axioms), "source": declarations[theorem]})
        status["audited_declaration_count"] = len(inventory)
        (AUDIT / "declarations.json").write_text(json.dumps(reports, indent=2) + "\n")
        status["unexpected_axioms"] = unexpected
        status["missing_axiom_reports"] = missing
        if unexpected or missing:
            status["status"] = "AXIOM_AUDIT_FAILED"
            record(status)
            return 1
        for flag, (name, signature) in TARGETS.items():
            status[flag] = name in inventory and inventory[name]["signature"] == signature
        status["conditional_results"] = [
            {"theorem": name, "verified": name in inventory, "condition": "NormalizedHierarchy"}
            for name in [
                "BfgsVerification.ReciprocalGrowth.hierarchy_reciprocal_growth",
                "BfgsVerification.QuantitativeGrowth.hierarchy_finite_horizon_rpow",
                "BfgsVerification.QuantitativeGrowth.hierarchy_superquadratic_growth",
            ]
        ]
        status["matrix_to_normalized_hierarchy_verified"] = "BfgsVerification.fullBFGS_normalizedHierarchy" in inventory
        status["finite_horizon_verified"] = "BfgsVerification.finiteHorizon" in inventory
        status["objective_level_model_formalized"] = False
        status["outside_verified_scope"] = [
            "Finite-convex-objective and differentiable-accepted-iterate model",
            "Objective-level Armijo-to-summability and compactness-to-gradient-bound deductions",
            "Other Module M statements and other research modules",
        ]
        status["remaining_target_obligations"] = [name for flag, (name, _) in TARGETS.items()
                                                  if not status[flag]]
        complete = all(status[flag] for flag in TARGETS)
        status["status"] = ("MODULE_M_MATRIX_AND_GROWTH_TARGETS_VERIFIED" if complete
                            else "STAGED_LEMMAS_CHECKED_MATRIX_TARGET_STILL_OPEN")
        status["warning"] = ("Claims concern the exact matrix-run targets printed in axioms.log; "
                             "other research modules and objective-level modeling are outside this audit.")
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
    except (ValueError, KeyError, StopIteration) as exc:
        status["status"] = "AUDIT_METADATA_ERROR"
        status["error"] = str(exc)
        record(status)
        return 1


if __name__ == "__main__":
    sys.exit(main())
