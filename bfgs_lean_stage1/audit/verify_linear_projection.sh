#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/env.sh
lake build BfgsVerification.SemialgebraicAffineTargets > audit/a_linear_projection_build.log 2>&1
lake env lean audit/A_LINEAR_PROJECTION_AXIOMS.lean > audit/a_linear_projection_axioms.log 2>&1
lake env lean audit/A_LINEAR_PROJECTION_CONTRACTS.lean > audit/a_linear_projection_contracts.log 2>&1
python3 audit/validate_linear_projection.py > audit/a_linear_projection_validation.log 2>&1
cat audit/a_linear_projection_validation.log
