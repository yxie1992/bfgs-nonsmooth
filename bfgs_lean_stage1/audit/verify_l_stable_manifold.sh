#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/env.sh
lake build BfgsVerification.LStableInvariantManifold > audit/l_stable_manifold_build.log 2>&1
lake env lean audit/L_STABLE_MANIFOLD_AXIOMS.lean > audit/l_stable_manifold_axioms.log 2>&1
lake env lean audit/L_STABLE_MANIFOLD_CONTRACTS.lean > audit/l_stable_manifold_contracts.log 2>&1
python3 audit/validate_l_stable_manifold.py > audit/l_stable_manifold_validation.log 2>&1
cat audit/l_stable_manifold_validation.log
