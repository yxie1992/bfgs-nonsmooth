#!/usr/bin/env python3
"""Hash delivered source/configuration/documentation/audit files, excluding caches.

Run after the audit and after its output log has closed. MANIFEST.json itself
is excluded. The original draft manifest is preserved in audit/history/.
"""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
files = [p for p in ROOT.iterdir() if p.is_file() and p.name != "MANIFEST.json"]
for directory in ("BfgsVerification", "scripts", "reference", "audit"):
    files.extend(p for p in (ROOT / directory).rglob("*")
                 if p.is_file() and "__pycache__" not in p.parts)
manifest = {str(p.relative_to(ROOT)): {
    "bytes": p.stat().st_size,
    "sha256": hashlib.sha256(p.read_bytes()).hexdigest(),
} for p in sorted(files)}
(ROOT / "MANIFEST.json").write_text(json.dumps(manifest, indent=2) + "\n")
print(f"Wrote {len(manifest)} artifact hashes to MANIFEST.json")
