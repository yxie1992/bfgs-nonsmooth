#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/env.sh
lake build BfgsVerification.SemialgebraicSmoothComponents > audit/semialgebraic_smooth_components_build.log 2>&1
lake env lean audit/SemialgebraicSmoothComponentsAudit.lean > audit/semialgebraic_smooth_components_axioms_contracts.log 2>&1
python3 audit/validate_semialgebraic_smooth_components.py > audit/semialgebraic_smooth_components_validation.log 2>&1
