#!/usr/bin/env python3
"""Hash delivered source/configuration/documentation/audit files, excluding caches.

Run after the audit output log closes and intended delivery files are staged.
Hash the Git-index delivery inventory so untracked local notes do not make a
fresh checkout's manifest unreproducible. MANIFEST.json itself is excluded.
The original draft manifest is preserved in audit/history/.
"""
import hashlib
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
paths = subprocess.check_output(
    ["git", "ls-files", "--cached", "-z", "--", "."], cwd=ROOT
).decode().split("\0")
files = [ROOT / name for name in paths if name and name != "MANIFEST.json"
         and (ROOT / name).is_file() and "__pycache__" not in Path(name).parts]
manifest = {str(p.relative_to(ROOT)): {
    "bytes": p.stat().st_size,
    "sha256": hashlib.sha256(p.read_bytes()).hexdigest(),
} for p in sorted(files)}
(ROOT / "MANIFEST.json").write_text(json.dumps(manifest, indent=2) + "\n")
print(f"Wrote {len(manifest)} artifact hashes to MANIFEST.json")
