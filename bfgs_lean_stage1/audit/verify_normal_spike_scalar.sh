#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/env.sh
python3 audit/validate_normal_spike_scalar.py --prepare
lake build BfgsVerification.NormalSpikeTargets 2>&1 | tee audit/normal_spike_scalar_build.log
lake env lean audit/NORMAL_SPIKE_SCALAR_AXIOMS.lean > audit/normal_spike_scalar_axioms.log 2>&1
lake env lean audit/NORMAL_SPIKE_SCALAR_CONTRACTS.lean > audit/normal_spike_scalar_contracts.log 2>&1
python3 audit/validate_normal_spike_scalar.py | tee audit/normal_spike_scalar_validation.log
