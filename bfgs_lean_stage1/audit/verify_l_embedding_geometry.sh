#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/env.sh
lake build BfgsVerification.LEmbeddingGeometryTargets > audit/l_embedding_geometry_build.log 2>&1
lake env lean audit/LEmbeddingGeometryAudit.lean > audit/l_embedding_geometry_axioms.log 2>&1
lake env lean audit/LEmbeddingGeometryContracts.lean > audit/l_embedding_geometry_contracts.log 2>&1
python3 audit/validate_l_embedding_geometry.py > audit/l_embedding_geometry_validation.log 2>&1
cat audit/l_embedding_geometry_validation.log
