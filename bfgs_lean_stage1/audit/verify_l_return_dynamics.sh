#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/env.sh
python3 audit/generate_l_shape_certificate.py --check > audit/l_return_dynamics_regeneration.log 2>&1
lake build BfgsVerification.LGlobalVerification > audit/l_return_dynamics_build.log 2>&1
lake env lean audit/LReturnDynamicsAudit.lean > audit/l_return_dynamics_axioms.log 2>&1
python3 audit/validate_l_return_dynamics.py > audit/l_return_dynamics_validation.log 2>&1
