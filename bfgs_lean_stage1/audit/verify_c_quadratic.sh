#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/env.sh
lake build BfgsVerification.PlanarQuadraticTargets > audit/c_quadratic_build.log 2>&1
lake env lean audit/C_QUADRATIC_AXIOMS.lean > audit/c_quadratic_axioms.log 2>&1
lake env lean audit/C_QUADRATIC_CONTRACTS.lean > audit/c_quadratic_contracts.log 2>&1
python3 audit/validate_c_quadratic.py > audit/c_quadratic_validation.log 2>&1
cat audit/c_quadratic_validation.log
