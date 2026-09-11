#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/env.sh
lake build BfgsVerification.LGlobalTargets > audit/l_global_targets_build.log 2>&1
lake env lean audit/LGlobalTargetsAudit.lean > audit/l_global_targets_axioms.log 2>&1
python3 audit/validate_l_global_targets.py > audit/l_global_targets_validation.log 2>&1
