#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../../.."
source scripts/env.sh
BFGS_VALUE_SCOPE="$PWD/audit/scratch/objective_value_scale19"
export LEAN_PATH="$BFGS_VALUE_SCOPE:${LEAN_PATH:-}"
lake env lean -o "$BFGS_VALUE_SCOPE/ObjectiveValueScaling.olean" "$BFGS_VALUE_SCOPE/ObjectiveValueScaling.lean" > "$BFGS_VALUE_SCOPE/build.log" 2>&1
lake env lean -o "$BFGS_VALUE_SCOPE/ObjectiveValueScalingTargets.olean" "$BFGS_VALUE_SCOPE/ObjectiveValueScalingTargets.lean" > "$BFGS_VALUE_SCOPE/targets_build.log" 2>&1
lake env lean "$BFGS_VALUE_SCOPE/Audit.lean" > "$BFGS_VALUE_SCOPE/axioms_contracts.log" 2>&1
python3 "$BFGS_VALUE_SCOPE/validate.py"
