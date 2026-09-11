#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/env.sh
lake build BfgsVerification.RectangularNuclearTargets > audit/rectangular_nuclear_build.log 2>&1
lake env lean audit/RECTANGULAR_NUCLEAR_AXIOMS.lean > audit/rectangular_nuclear_axioms.log 2>&1
lake env lean audit/RECTANGULAR_NUCLEAR_CONTRACTS.lean > audit/rectangular_nuclear_contracts.log 2>&1
python3 audit/validate_rectangular_nuclear.py > audit/rectangular_nuclear_validation.log 2>&1
cat audit/rectangular_nuclear_validation.log
