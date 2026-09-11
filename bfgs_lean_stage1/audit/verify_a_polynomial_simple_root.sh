#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/env.sh
{
  lean --version
  lake build BfgsVerification.PolynomialRootTargets
} > audit/a_polynomial_simple_root_build.log 2>&1
lake env lean audit/A_POLYNOMIAL_SIMPLE_ROOT_AXIOMS.lean > audit/a_polynomial_simple_root_axioms.log 2>&1
lake env lean audit/A_POLYNOMIAL_SIMPLE_ROOT_CONTRACTS.lean > audit/a_polynomial_simple_root_contracts.log 2>&1
python3 audit/validate_a_polynomial_simple_root.py > audit/a_polynomial_simple_root_validation.log 2>&1
cat audit/a_polynomial_simple_root_validation.log
