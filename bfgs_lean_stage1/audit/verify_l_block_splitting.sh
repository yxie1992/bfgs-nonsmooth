#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/env.sh
lake build BfgsVerification.LBlockStableOrbit > audit/l_block_splitting_build.log 2>&1
lake env lean audit/LBlockSplittingAudit.lean > audit/l_block_splitting_axioms.log 2>&1
python3 audit/validate_l_block_splitting.py > audit/l_block_splitting_validation.log 2>&1
cat audit/l_block_splitting_validation.log
