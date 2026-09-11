#!/usr/bin/env python3
"""Rebuild and audit the delivered six-scope sign-query milestone sources."""
import argparse
import datetime
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser()
parser.add_argument("--validate-only", action="store_true")
parser.add_argument("--manifest", default="audit/sign_query_declarations.json")
args = parser.parse_args()
m = json.loads((ROOT / args.manifest).read_text())
prefix = m.get("log_prefix", "sign_query")
audit_driver = m.get("audit_driver", "audit/SignQueryAudit.lean")
sources = [s for scope in m["scopes"] for s in scope["sources"]]
if not args.validate_only:
    modules = [s["module"] for s in sources]
    with (ROOT / f"audit/{prefix}_build.log").open("w") as log:
        subprocess.run(["lake", "build", *modules], cwd=ROOT, stdout=log,
                       stderr=subprocess.STDOUT, check=True)
    with (ROOT / f"audit/{prefix}_axioms_contracts.log").open("w") as log:
        subprocess.run(["lake", "env", "lean", audit_driver], cwd=ROOT,
                       stdout=log, stderr=subprocess.STDOUT, check=True)

for source in sources:
    p = ROOT / source["path"]
    assert hashlib.sha256(p.read_bytes()).hexdigest() == source["sha256"], p
    assert not re.search(r"\b(?:sorry|admit|axiom|native_decide|unsafe)\b", p.read_text()), p
for scope in m["scopes"]:
    assert scope["review_evidence"], scope["id"]
    for evidence in scope["review_evidence"]:
        assert (ROOT / evidence).is_file(), evidence
log = (ROOT / f"audit/{prefix}_axioms_contracts.log").read_text()
assert "error:" not in log
reports = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", log)
assert len(reports) == len(m["declarations"]) == len(set(m["declarations"]))
assert {n for n, _ in reports} == set(m["declarations"])
for n, axioms in reports:
    assert set(axioms.replace(",", " ").split()) <= {"propext", "Classical.choice", "Quot.sound"}, n
assert log.count("EXACT_TARGET_OK ") == len(m["targets"])
assert "error:" not in (ROOT / f"audit/{prefix}_build.log").read_text()
result = datetime.datetime.now(datetime.timezone.utc).isoformat() + "\n"
result += (f"PASS: {len(sources)} delivered source hashes; {len(reports)} actual type/standard "
           f"transitive axiom reports; {len(m['targets'])} strict exact targets; "
           f"{len(m['scopes'])} independent peer reviews.\n")
if not args.validate_only:
    (ROOT / f"audit/{prefix}_validation.log").write_text(result)
print(result, end="")
