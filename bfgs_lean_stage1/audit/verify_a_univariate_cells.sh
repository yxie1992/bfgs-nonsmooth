#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/env.sh
{
  lean --version
  lake build BfgsVerification.UnivariateCellTargets
} > audit/a_univariate_cells_build.log 2>&1
lake env lean audit/A_UNIVARIATE_CELLS_AXIOMS.lean > audit/a_univariate_cells_axioms.log 2>&1
lake env lean audit/A_UNIVARIATE_CELLS_CONTRACTS.lean > audit/a_univariate_cells_contracts.log 2>&1
python3 audit/validate_a_univariate_cells.py > audit/a_univariate_cells_validation.log 2>&1
cat audit/a_univariate_cells_validation.log
