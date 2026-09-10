#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/env.sh
if ! command -v lake >/dev/null 2>&1; then
  echo 'A working Lean/Elan installation is required. No compilation has occurred.' >&2
  exit 69
fi
# Fetch the pinned manifest without invoking the native cache executable in the
# post-update hook. Lean 4.19's executable hits a dyld load error on newer macOS;
# running the same cache program through Lean's interpreter avoids that issue.
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
lake env lean --run .lake/packages/mathlib/Cache/Main.lean get
python3 scripts/check.py
