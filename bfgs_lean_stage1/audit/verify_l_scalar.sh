#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/env.sh
lake build BfgsVerification.LScalarTargets > audit/l_scalar_build.log 2>&1
lake env lean audit/L_SCALAR_AXIOMS.lean > audit/l_scalar_axioms.log 2>&1
lake env lean audit/L_SCALAR_CONTRACTS.lean > audit/l_scalar_contracts.log 2>&1
python3 audit/validate_l_scalar.py > audit/l_scalar_validation.log 2>&1
cat audit/l_scalar_validation.log
