#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/env.sh
lake build BfgsVerification.LScalarStepTargets > audit/l_step_build.log 2>&1
lake env lean audit/L_STEP_AXIOMS.lean > audit/l_step_axioms.log 2>&1
lake env lean audit/L_STEP_CONTRACTS.lean > audit/l_step_contracts.log 2>&1
python3 audit/validate_l_step.py > audit/l_step_validation.log 2>&1
cat audit/l_step_validation.log
