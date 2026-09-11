#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/env.sh
python3 audit/validate_semialgebraic_path_completion_provenance.py > audit/semialgebraic_path_completion_provenance.log 2>&1
python3 scripts/verify_report_sign_query_scoped.py --manifest audit/semialgebraic_path_completion_declarations.json
