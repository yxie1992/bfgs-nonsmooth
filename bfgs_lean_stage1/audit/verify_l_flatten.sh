#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/env.sh
lake build BfgsVerification.LFlattenNeighborhood > audit/l_flatten_build.log 2>&1
lake env lean audit/LFlattenAudit.lean > audit/l_flatten_axioms.log 2>&1
python3 audit/validate_l_flatten.py > audit/l_flatten_validation.log 2>&1
cat audit/l_flatten_validation.log
