#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/env.sh
{
  lean --version
  lake build BfgsVerification.QuadraticProjectionTargets
} > audit/a_quadratic_projection_build.log 2>&1
lake env lean audit/A_QUADRATIC_PROJECTION_AXIOMS.lean > audit/a_quadratic_projection_axioms.log 2>&1
lake env lean audit/A_QUADRATIC_PROJECTION_CONTRACTS.lean > audit/a_quadratic_projection_contracts.log 2>&1
python3 audit/validate_a_quadratic_projection.py > audit/a_quadratic_projection_validation.log 2>&1
cat audit/a_quadratic_projection_validation.log
