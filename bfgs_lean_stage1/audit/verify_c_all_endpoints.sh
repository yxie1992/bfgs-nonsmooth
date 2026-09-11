#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/env.sh
lake build BfgsVerification.PlanarAllEndpointTargets > audit/c_all_endpoints_build.log 2>&1
lake env lean audit/PlanarAllEndpointsAudit.lean > audit/c_all_endpoints_axioms.log 2>&1
python3 audit/validate_c_all_endpoints.py > audit/c_all_endpoints_validation.log 2>&1
