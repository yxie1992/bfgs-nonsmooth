#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/env.sh
{
  lean --version
  lake build BfgsVerification.PolynomialMultiplicityTargets
} > audit/a_polynomial_multiplicity_build.log 2>&1
lake env lean audit/A_POLYNOMIAL_MULTIPLICITY_AXIOMS.lean > audit/a_polynomial_multiplicity_axioms.log 2>&1
lake env lean audit/A_POLYNOMIAL_MULTIPLICITY_CONTRACTS.lean > audit/a_polynomial_multiplicity_contracts.log 2>&1
python3 audit/validate_a_polynomial_multiplicity.py > audit/a_polynomial_multiplicity_validation.log 2>&1
cat audit/a_polynomial_multiplicity_validation.log
