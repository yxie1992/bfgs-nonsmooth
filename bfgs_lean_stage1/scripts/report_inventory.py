#!/usr/bin/env python3
"""Create/validate source coverage, without converting compilation into claim review."""
import hashlib
import json
import re
from pathlib import Path

PROJECT = Path(__file__).resolve().parents[1]
SOURCE = PROJECT.parent / "BFGS_MASTER_REPORT_LaTeX" / "report"
REGISTER = PROJECT / "audit" / "REPORT_STATUS.json"
MODULES = [
    ("I", "inventory", "synthesis_review_pending"),
    ("M", "foundation", "verified"),
    ("T", "T", "in_progress"),
    ("R", "R", "open"),
    ("F", "families", "open"),
    ("H", "H", "in_progress"),
    ("Q", "Q", "open"),
    ("G", "G", "in_progress"),
    ("A", "affine_geometry", "open"),
    ("C", "C", "open"),
    ("U", "U", "open"),
    ("D", "D", "open"),
    ("L", "L", "open"),
    ("E", "verification", "evidence_review_pending"),
]

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def initial_register():
    modules = []
    for tag, stem, status in MODULES:
        path = SOURCE / "chapters" / f"{stem}.tex"
        lines = path.read_text().splitlines()
        starts = [1] + [i for i, line in enumerate(lines, 1)
                        if i > 1 and re.match(r"\\(?:sub)*section\*?\{", line)]
        spans = []
        for j, start in enumerate(starts):
            end = starts[j + 1] - 1 if j + 1 < len(starts) else len(lines)
            spans.append({
                "id": f"{tag}.span.{j + 1}", "start_line": start, "end_line": end,
                "anchor": lines[start - 1],
                "labels": re.findall(r"\\label\{([^}]+)\}", "\n".join(lines[start-1:end])),
                "claim_review": "mapped_in_PROOF_OBLIGATIONS" if tag == "M" else "pending",
                "verified_exports": [],
            })
        modules.append({"module": tag, "source": str(path.relative_to(PROJECT.parent)),
                        "source_sha256": digest(path), "status": status,
                        "detailed_inventory": "PROOF_OBLIGATIONS.md" if tag == "M" else None,
                        "coverage_spans": spans})
    return {"schema_version": 1, "entire_report_verified": False,
            "scope": "Every retained mathematical assertion; explicit conjectures and historical evidence classified separately",
            "baseline_verified_commit": "6c29cff", "modules": modules,
            "source_files": {str(p.relative_to(PROJECT.parent)): digest(p)
                             for p in sorted(SOURCE.rglob("*.tex"))}}


def validate(data):
    for rel, expected in data["source_files"].items():
        assert digest(PROJECT.parent / rel) == expected, f"Source changed: {rel}"
    for module in data["modules"]:
        lines = (PROJECT.parent / module["source"]).read_text().splitlines()
        covered = [i for span in module["coverage_spans"]
                   for i in range(span["start_line"], span["end_line"] + 1)]
        assert covered == list(range(1, len(lines) + 1)), module["module"]
    print(f"PASS: preserved source hashes; exhaustive nonoverlapping spans for {len(data['modules'])} modules")
    print(f"Entire report verified: {data['entire_report_verified']}")

if __name__ == "__main__":
    if not REGISTER.exists():
        REGISTER.write_text(json.dumps(initial_register(), indent=2) + "\n")
    validate(json.loads(REGISTER.read_text()))
