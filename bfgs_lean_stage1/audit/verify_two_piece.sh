#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/env.sh
lake build BfgsVerification.TwoPieceTargets > audit/two_piece_build.log 2>&1
lake env lean audit/TwoPieceAudit.lean > audit/two_piece_axioms.log 2>&1
python3 audit/validate_two_piece.py > audit/two_piece_validation.log 2>&1
