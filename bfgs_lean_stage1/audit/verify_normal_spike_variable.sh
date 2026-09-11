#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/env.sh
python3 audit/validate_normal_spike_variable.py --prepare
lake build BfgsVerification.NormalSpikeVariableTargets 2>&1 | tee audit/normal_spike_variable_build.log
lake env lean audit/NORMAL_SPIKE_VARIABLE_AXIOMS.lean > audit/normal_spike_variable_axioms.log 2>&1
lake env lean audit/NORMAL_SPIKE_VARIABLE_CONTRACTS.lean > audit/normal_spike_variable_contracts.log 2>&1
python3 audit/validate_normal_spike_variable.py | tee audit/normal_spike_variable_validation.log
