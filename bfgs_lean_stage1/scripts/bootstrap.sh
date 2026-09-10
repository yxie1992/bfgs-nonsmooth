#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
if ! command -v lake >/dev/null 2>&1; then
  echo 'A working Lean/Elan installation is required. No compilation has occurred.' >&2
  exit 69
fi
lake update
lake exe cache get
python3 scripts/check.py
