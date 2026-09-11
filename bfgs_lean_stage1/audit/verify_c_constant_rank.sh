#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/env.sh
lake build BfgsVerification.ConstantRankTargets > audit/c_constant_rank_build.log 2>&1
lake env lean audit/ConstantRankAudit.lean > audit/c_constant_rank_axioms.log 2>&1
python3 audit/validate_c_constant_rank.py > audit/c_constant_rank_validation.log 2>&1
