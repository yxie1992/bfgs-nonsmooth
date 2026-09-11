#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/env.sh
lake build BfgsVerification.LActualCopyTargets > audit/l_actual_copies_build.log 2>&1
lake env lean audit/LActualCopiesAudit.lean > audit/l_actual_copies_axioms.log 2>&1
lake env lean audit/LActualCopiesContracts.lean > audit/l_actual_copies_contracts.log 2>&1
python3 audit/validate_l_actual_copies.py > audit/l_actual_copies_validation.log 2>&1
cat audit/l_actual_copies_validation.log
