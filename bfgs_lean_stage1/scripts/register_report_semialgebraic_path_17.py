#!/usr/bin/env python3
"""Register milestone 17 only after its delivered scoped gate has passed.

This is a one-time release action, not the full audit. It changes central Lean
imports, Audit.lean and scripts/check.py, then freezes their resulting hashes.
Run scripts/check.py afterward; this script does not write STATUS.json or claim
that the new central audit has passed. All runtime inputs are delivered files.
"""
from __future__ import annotations

import ast
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

MANIFEST = "audit/semialgebraic_path_completion_declarations.json"
BLOCK = "REPORT_SEMIALGEBRAIC_PATH_TARGETS"
OLD_STATUS = "MODULE_M_AND_REPORT_TAME_GEOMETRY_TARGETS_VERIFIED"
NEW_STATUS = "MODULE_M_AND_REPORT_SEMIALGEBRAIC_PATH_TARGETS_VERIFIED"
MARKER = (
    "/- Seventeenth milestone: actual semialgebraic path graphs, finite path "
    "covers, scalar and objective composition regularity, and continuous "
    "semialgebraic path components. -/"
)
OLD_SCOPE_PREFIX = (
    "The literal A assertion that witnessing path graphs are semialgebraic "
    "remains under separate verification."
)
NEW_SCOPE_NOTE = (
    "The literal A geometric ingredients are now proved: actual semialgebraic "
    "witness paths, finite actual continuous-semialgebraic path components, "
    "and continuous objective composition smooth outside finitely many "
    "interior parameters. Historical E jobs/counts/timings/environment/archive "
    "identities remain unverified without the original inputs. R182–187's "
    "numerical attribution to an unidentified older four-piece objective "
    "remains a mathematical source-attribution obligation; the verified "
    "current D objective does not identify that older objective. See "
    "REPORT_STATUS.json"
)
LITERAL_TARGET_CHECK = (
    'status[flag] = name in inventory and inventory[name]["signature"] == signature'
)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def project_root() -> Path:
    for parent in Path(__file__).resolve().parents:
        if (parent / "lakefile.toml").is_file() and (parent / "scripts/check.py").is_file():
            return parent
    raise SystemExit("Cannot locate the delivered Lean project")


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def delivered_path(root: Path, value: str) -> Path:
    p = Path(value)
    require(not p.is_absolute() and ".." not in p.parts, f"Nonrelative input: {value}")
    require("scratch" not in p.parts and ".scratch" not in p.parts,
            f"Excluded runtime input: {value}")
    return root / p


def registry(code: str) -> dict[str, tuple[str, str]]:
    """Read literal target dictionaries and validate the actual ALL_TARGETS union."""
    dictionaries = {}
    union = None
    for node in ast.parse(code).body:
        if not isinstance(node, ast.Assign) or len(node.targets) != 1:
            continue
        name = node.targets[0]
        if not isinstance(name, ast.Name):
            continue
        if name.id == "ALL_TARGETS":
            require(union is None, "Duplicate ALL_TARGETS assignment")
            union = node.value
        elif name.id == "TARGETS" or name.id.endswith("_TARGETS"):
            require(isinstance(node.value, ast.Dict), f"Nonliteral target dictionary: {name.id}")
            require(name.id not in dictionaries, f"Duplicate target block: {name.id}")
            values = ast.literal_eval(node.value)
            require(len(values) == len(node.value.keys), f"Duplicate flags in {name.id}")
            dictionaries[name.id] = values
    merged = {}
    for values in dictionaries.values():
        require(not (merged.keys() & values.keys()), "Duplicate target flags across blocks")
        merged.update(values)
    seen = []

    def evaluate(node):
        if isinstance(node, ast.Name):
            require(node.id in dictionaries, f"Unknown union block: {node.id}")
            seen.append(node.id)
            return dictionaries[node.id]
        require(isinstance(node, ast.BinOp) and isinstance(node.op, ast.BitOr),
                "ALL_TARGETS is not a literal-dictionary union")
        return evaluate(node.left) | evaluate(node.right)

    require(union is not None, "Missing ALL_TARGETS")
    actual = evaluate(union)
    require(len(seen) == len(set(seen)) == len(dictionaries), "Omitted or repeated union block")
    require(actual == merged, "ALL_TARGETS does not contain every literal target")
    require(len(set(merged.values())) == len(merged), "Duplicate target pairs")
    return merged


def main() -> None:
    root = project_root()
    m = json.loads(delivered_path(root, MANIFEST).read_text())
    require(m.get("log_prefix") == "semialgebraic_path_completion", "Unexpected log prefix")
    require(len(m["scopes"]) == 7, "Expected seven reviewed scopes")
    sources = [s for scope in m["scopes"] for s in scope["sources"]]
    pairs = [tuple(pair) for pair in m["targets"]]
    require(len(sources) == len({s["path"] for s in sources}) == 33, "Expected 33 unique sources")
    require(len(m["declarations"]) == len(set(m["declarations"])) == 152,
            "Expected 152 unique scoped declaration reports")
    require(len(pairs) == len(set(pairs)) == 16, "Expected 16 unique exact target pairs")
    require(len({a for a, b in pairs}) == 16 and len({b for a, b in pairs}) == 16,
            "Repeated target theorem or target definition")
    for a, b in pairs:
        require(a in m["declarations"] and b in m["declarations"], f"Unaudited target pair: {a}")
        require(re.fullmatch(r"BfgsVerification\.[A-Za-z0-9_.]+", a) is not None and
                re.fullmatch(r"BfgsVerification\.[A-Za-z0-9_.]+", b) is not None,
                f"Unexpected target identifier: {a}, {b}")
    for source in sources:
        p = delivered_path(root, source["path"])
        require(p.parent == root / "BfgsVerification" and p.suffix == ".lean",
                f"Unexpected source path: {p}")
        require(source["module"] == "BfgsVerification." + p.stem, f"Module/path mismatch: {p}")
        require(digest(p) == source["sha256"], f"Delivered source changed: {p}")
    for scope in m["scopes"]:
        for evidence in scope["review_evidence"]:
            require(delivered_path(root, evidence).is_file(), f"Missing review evidence: {evidence}")
    delivered_path(root, m["audit_driver"])
    provenance_path = delivered_path(root, m["provenance_validator"])
    provenance = subprocess.run([sys.executable, str(provenance_path)], cwd=root,
                                text=True, capture_output=True, check=True)
    require(provenance.stdout.startswith("PASS:"), "Delivered provenance gate did not pass")
    gate = subprocess.run(
        [sys.executable, "scripts/verify_report_sign_query_scoped.py", "--validate-only",
         "--manifest", MANIFEST], cwd=root, text=True, capture_output=True, check=True)
    require("PASS: 33 delivered source hashes; 152 actual type/standard transitive axiom reports; "
            "16 strict exact targets; 7 independent peer reviews." in gate.stdout,
            "Delivered scoped gate did not report the expected PASS")
    log = (root / "audit/semialgebraic_path_completion_axioms_contracts.log").read_text()
    markers = re.findall(r"^EXACT_TARGET_OK (\S+)$", log, re.M)
    require(len(markers) == 16 and set(markers) == {a for a, _ in pairs},
            "Scoped exact-target markers do not match the manifest's actual theorem names")

    # Everything is computed and checked before the first central mutation.
    check_path = root / "scripts/check.py"
    old_code = check_path.read_text()
    require(BLOCK not in old_code, "Milestone 17 is already registered")
    old_targets = registry(old_code)
    require(len(old_targets) == 233, "Expected 233 existing exact targets")
    require(LITERAL_TARGET_CHECK in old_code, "Central actual-type literal equality safeguard changed")
    require(not ({a for a, _ in pairs} & {a for a, _ in old_targets.values()}),
            "A new theorem is already registered")
    block = BLOCK + " = {\n"
    for a, b in pairs:
        flag = a.removeprefix("BfgsVerification.").replace(".", "_") + "_verified"
        require(flag not in old_targets, f"Existing flag collision: {flag}")
        block += f'    "{flag}":\n        ("{a}", "{b}"),\n'
    block += "}\n"
    require(old_code.count("ALL_TARGETS = ") == 1, "Unexpected ALL_TARGETS layout")
    code = old_code.replace("ALL_TARGETS = ", block + "ALL_TARGETS = ", 1)
    anchor = "| REPORT_TAME_GEOMETRY_TARGETS\n"
    require(code.count(anchor) == 1, "Unexpected previous target union")
    code = code.replace(anchor, "| REPORT_TAME_GEOMETRY_TARGETS | " + BLOCK + "\n", 1)
    require(code.count(OLD_STATUS) == 1, "Unexpected previous success status")
    code = code.replace(OLD_STATUS, NEW_STATUS, 1)
    timeout_old = '    parser.add_argument("--timeout", type=int, default=600)'
    timeout_new = ('    parser.add_argument("--timeout", type=int, default=7200,\n'
                   '                        help="Timeout in seconds per command (default: 7200)")')
    require(code.count(timeout_old) == 1, "Expected the previous 600-second command timeout")
    code = code.replace(timeout_old, timeout_new, 1)
    scope_pattern = re.compile(r'^            "' + re.escape(OLD_SCOPE_PREFIX) + r'[^\n]*\n', re.M)
    require(len(scope_pattern.findall(code)) == 1, "Expected the single obsolete A scope note")
    code = scope_pattern.sub("            " + json.dumps(NEW_SCOPE_NOTE, ensure_ascii=False) + ",\n", code, count=1)
    new_targets = registry(code)
    require(len(new_targets) == 249, "Expected 249 resulting exact targets")
    require(all(new_targets[k] == v for k, v in old_targets.items()), "An existing target changed")
    require(set(new_targets.values()) - set(old_targets.values()) == set(pairs), "New target mismatch")
    require(LITERAL_TARGET_CHECK in code, "Literal actual-type safeguard was not preserved")
    for phrase in [
        '"Unconditional optimal-value convergence for arbitrary finite convex nonsmooth objectives"',
        '"Existence of admissible steps on every search ray"',
    ]:
        require(phrase in old_code and phrase in code, "An unclaimed general conclusion was removed")
    conditional_start = old_code.index('        status["conditional_results"] = [')
    conditional_end = old_code.index('        status["matrix_to_normalized_hierarchy_verified"]', conditional_start)
    require(old_code[conditional_start:conditional_end] in code, "Conditional bridge qualifications changed")

    prior = json.loads((root / "audit/report_tame_geometry_source_hashes.json").read_text())
    require(len(prior) == 693, "Expected milestone 16's 693-source freeze")
    for path, value in prior.items():
        require(digest(delivered_path(root, path)) == value, f"Previously frozen source changed: {path}")
    modules = sorted((root / "BfgsVerification").glob("*.lean"))
    files = modules + [root / "BfgsVerification.lean", root / "Audit.lean"]
    file_names = {str(p.relative_to(root)) for p in files}
    require(len(files) == 726, "Expected 726 resulting Lean sources")
    require(file_names - set(prior) == {s["path"] for s in sources}, "Unexpected new main source")
    root_path = root / "BfgsVerification.lean"
    old_root = root_path.read_text()
    require("/-!" in old_root, "Missing root documentation block")
    new_root = "".join("import BfgsVerification." + p.stem + "\n" for p in modules)
    new_root += "\n" + old_root[old_root.index("/-!"):]
    audit_path = root / "Audit.lean"
    old_audit = audit_path.read_text()
    require(MARKER not in old_audit, "Milestone 17 audit entries already exist")
    require('Meta.ppExpr info.type' in old_audit and 'collectAxioms name' in old_audit,
            "Actual compiled type/axiom audit has changed")
    new_audit = old_audit + "\n" + MARKER + "\n"
    for a, b in pairs:
        new_audit += f"#print {b}\nexample : {b} := {a}\n#print axioms {a}\n"
    content = {check_path: code, root_path: new_root, audit_path: new_audit}
    hashes = {
        str(p.relative_to(root)): hashlib.sha256(content[p].encode()).hexdigest()
        if p in content else digest(p)
        for p in sorted(files)
    }
    require(len(hashes) == 726, "Incorrect frozen source count")
    content[root / "audit/report_semialgebraic_path_targets.json"] = json.dumps(pairs, indent=2) + "\n"
    content[root / "audit/report_semialgebraic_path_source_hashes.json"] = json.dumps(hashes, indent=2) + "\n"
    for path in content:
        if path not in [check_path, root_path, audit_path]:
            require(not path.exists(), f"Refusing to overwrite an existing release manifest: {path}")
    for path, value in content.items():
        path.write_text(value)
    print(provenance.stdout, end="")
    print(gate.stdout, end="")
    print("Registered 16 new exact targets, 249 total; froze 726 Lean files. Full pinned central audit pending.")


if __name__ == "__main__":
    main()
