#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/env.sh
lake build BfgsVerification.AffineCriticalPathCover BfgsVerification.SemialgebraicSupportProjection BfgsVerification.SpatialQuadraticTargets BfgsVerification.FiniteMaxHessianTargets > audit/affine_spatial_hessian_build.log 2>&1
lake env lean audit/A_SUPPORT_PATH_AXIOMS.lean > audit/a_support_path_axioms.log 2>&1
lake env lean audit/A_SUPPORT_PATH_CONTRACTS.lean > audit/a_support_path_contracts.log 2>&1
lake env lean audit/A_SEMIALGEBRAIC_REDUCTION_AXIOMS.lean > audit/a_semialgebraic_reduction_axioms.log 2>&1
lake env lean audit/A_SEMIALGEBRAIC_REDUCTION_CONTRACTS.lean > audit/a_semialgebraic_reduction_contracts.log 2>&1
lake env lean audit/C_SPATIAL_WARNING_AXIOMS.lean > audit/c_spatial_warning_axioms.log 2>&1
lake env lean audit/C_SPATIAL_WARNING_CONTRACTS.lean > audit/c_spatial_warning_contracts.log 2>&1
lake env lean audit/FINITE_MAX_HESSIAN_AXIOMS.lean > audit/finite_max_hessian_axioms.log 2>&1
lake env lean audit/FINITE_MAX_HESSIAN_CONTRACTS.lean > audit/finite_max_hessian_contracts.log 2>&1
python3 audit/validate_affine_spatial_hessian.py
