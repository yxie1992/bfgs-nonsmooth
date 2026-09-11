#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/env.sh
lake build BfgsVerification.StablePositiveDirection > audit/local_stable_orbit_build.log 2>&1
lake build BfgsVerification.StableOrbitTargets > audit/local_stable_orbit_targets_build.log 2>&1
lake env lean audit/LocalStableOrbitAudit.lean > audit/local_stable_orbit_axioms.log 2>&1
lake env lean audit/LOCAL_STABLE_ORBIT_PEER_CONTRACTS.lean > audit/local_stable_orbit_peer_contracts.log 2>&1
python3 audit/validate_local_stable_orbit.py > audit/local_stable_orbit_validation.log 2>&1
cat audit/local_stable_orbit_validation.log
