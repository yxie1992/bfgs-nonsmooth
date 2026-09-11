#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/env.sh
lake build BfgsVerification.ComparisonEnergyWarning BfgsVerification.AffineImageRanges > audit/tf_source_details_build.log 2>&1
lake env lean audit/TFSourceDetailsAudit.lean > audit/tf_source_details_axioms.log 2>&1
python3 audit/validate_tf_source_details.py > audit/tf_source_details_validation.log 2>&1
cat audit/tf_source_details_validation.log
