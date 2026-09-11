#!/usr/bin/env bash
set -euo pipefail
BFGS_E_SCOPE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BFGS_E_PROJECT="$(cd "$BFGS_E_SCOPE/../../.." && pwd)"
cd "$BFGS_E_PROJECT"
source scripts/env.sh
lake build BfgsVerification.PlanarQuadraticConvergence BfgsVerification.NormalSpikeObjective BfgsVerification.HessianUpdate > "$BFGS_E_SCOPE/design/facts_dependencies_build.log" 2>&1
lake env lean -o "$BFGS_E_SCOPE/lean/EReconstructionFacts.olean" "$BFGS_E_SCOPE/lean/EReconstructionFacts.lean" > "$BFGS_E_SCOPE/design/facts_build.log" 2>&1
export LEAN_PATH="$BFGS_E_SCOPE/lean:${LEAN_PATH:-}"
lake env lean "$BFGS_E_SCOPE/lean/FactsAudit.lean" > "$BFGS_E_SCOPE/design/facts_axioms_contracts.log" 2>&1
python3 "$BFGS_E_SCOPE/design/validate_facts.py" | tee "$BFGS_E_SCOPE/design/facts_validation.log"
