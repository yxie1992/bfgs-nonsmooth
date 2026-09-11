#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/env.sh
{
  lean --version
  lake build BfgsVerification.PseudoDivisionTargets
} > audit/a_polynomial_pseudodivision_build.log 2>&1
lake env lean audit/A_POLYNOMIAL_PSEUDODIVISION_AXIOMS.lean > audit/a_polynomial_pseudodivision_axioms.log 2>&1
lake env lean audit/A_POLYNOMIAL_PSEUDODIVISION_CONTRACTS.lean > audit/a_polynomial_pseudodivision_contracts.log 2>&1
python3 audit/validate_a_polynomial_pseudodivision.py > audit/a_polynomial_pseudodivision_validation.log 2>&1
cat audit/a_polynomial_pseudodivision_validation.log
