#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/env.sh
lake build BfgsVerification.LIdentityGeometry BfgsVerification.AffineRankLossTargets > audit/l_identity_build.log 2>&1
lake env lean audit/LIdentityAudit.lean > audit/l_identity_axioms.log 2>&1
python3 audit/validate_l_identity.py > audit/l_identity_validation.log 2>&1
cat audit/l_identity_validation.log
