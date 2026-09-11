#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/env.sh
lake build BfgsVerification.LStepEmbeddingTargets > audit/l_step_embedding_build.log 2>&1
lake env lean audit/L_STEP_EMBEDDING_AXIOMS.lean > audit/l_step_embedding_axioms.log 2>&1
lake env lean audit/L_STEP_EMBEDDING_CONTRACTS.lean > audit/l_step_embedding_contracts.log 2>&1
python3 audit/validate_l_step_embedding.py > audit/l_step_embedding_validation.log 2>&1
cat audit/l_step_embedding_validation.log
