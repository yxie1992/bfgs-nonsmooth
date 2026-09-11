#!/usr/bin/env bash
set -euo pipefail
BFGS_PRECISION_PROJECT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$BFGS_PRECISION_PROJECT"
source scripts/env.sh
python3 audit/generate_l_shape_fine_certificate.py --check > audit/l_shape_precision_generation_check.log 2>&1
lake build BfgsVerification.LShapePrecision > audit/l_shape_precision_build.log 2>&1
lake env lean audit/L_SHAPE_PRECISION_AXIOMS.lean > audit/l_shape_precision_axioms.log 2>&1
lake env lean audit/L_SHAPE_PRECISION_CONTRACTS.lean > audit/l_shape_precision_contracts.log 2>&1
python3 audit/validate_l_shape_precision.py > audit/l_shape_precision_validation.log 2>&1
cat audit/l_shape_precision_validation.log
