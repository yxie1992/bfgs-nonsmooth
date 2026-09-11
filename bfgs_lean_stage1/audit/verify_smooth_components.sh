#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/env.sh
lake build BfgsVerification.SmoothComponentTargets > audit/smooth_components_build.log 2>&1
lake env lean audit/SmoothComponentsAudit.lean > audit/smooth_components_axioms_contracts.log 2>&1
python3 audit/validate_smooth_components.py > audit/smooth_components_validation.log 2>&1
