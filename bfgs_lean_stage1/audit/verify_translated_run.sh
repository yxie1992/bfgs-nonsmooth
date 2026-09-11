#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/env.sh
lake build BfgsVerification.TranslatedSearch > audit/translated_run_build.log 2>&1
lake env lean audit/TranslatedRunAudit.lean > audit/translated_run_axioms.log 2>&1
python3 audit/validate_translated_run.py > audit/translated_run_validation.log 2>&1
cat audit/translated_run_validation.log
