#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/env.sh
lake build BfgsVerification.AffineGapTargets BfgsVerification.PlanarFiniteMaxTargets > audit/affine_gap_finite_max_build.log 2>&1
lake env lean audit/A_AFFINE_GAP_AXIOMS.lean > audit/a_affine_gap_axioms.log 2>&1
lake env lean audit/A_AFFINE_GAP_CONTRACTS.lean > audit/a_affine_gap_contracts.log 2>&1
lake env lean audit/C_FINITE_MAX_AXIOMS.lean > audit/c_finite_max_axioms.log 2>&1
lake env lean audit/C_FINITE_MAX_CONTRACTS.lean > audit/c_finite_max_contracts.log 2>&1
python3 audit/validate_affine_gap_finite_max.py
