#!/usr/bin/env bash
# Source this from the project directory, or use bootstrap.sh/check.py directly.
BFGS_PROJECT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
if [ -x "$BFGS_PROJECT_ROOT/.toolchain/elan/bin/lake" ]; then
  export ELAN_HOME="$BFGS_PROJECT_ROOT/.toolchain/elan"
  export PATH="$ELAN_HOME/bin:$PATH"
fi
export XDG_CACHE_HOME="$BFGS_PROJECT_ROOT/.cache"
export MATHLIB_CACHE_DIR="$BFGS_PROJECT_ROOT/.cache/mathlib"
