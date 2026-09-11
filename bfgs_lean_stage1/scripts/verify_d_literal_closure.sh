#!/usr/bin/env bash
set -euo pipefail
BFGS_D_LITERAL_PROJECT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$BFGS_D_LITERAL_PROJECT"
source scripts/env.sh
unset LEAN_PATH
python3 scripts/verify_report_sign_query_scoped.py --manifest audit/d_literal_closure_declarations.json
python3 scripts/validate_d_literal_closure.py > audit/d_literal_closure_correspondence_validation.log 2>&1
cat audit/d_literal_closure_correspondence_validation.log
