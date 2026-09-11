#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/env.sh
python3 audit/validate_normal_spike_examples.py --prepare
lake build BfgsVerification.NormalSpikeExampleTargets BfgsVerification.NormalSpikeRational 2>&1 | tee audit/normal_spike_examples_build.log
lake env lean audit/NORMAL_SPIKE_EXAMPLE_AXIOMS.lean > audit/normal_spike_example_axioms.log 2>&1
lake env lean audit/NORMAL_SPIKE_EXAMPLE_CONTRACTS.lean > audit/normal_spike_example_contracts.log 2>&1
lake env lean audit/NORMAL_SPIKE_RATIONAL_AXIOMS.lean > audit/normal_spike_rational_axioms.log 2>&1
lake env lean audit/NORMAL_SPIKE_RATIONAL_CONTRACTS.lean > audit/normal_spike_rational_contracts.log 2>&1
python3 audit/validate_normal_spike_examples.py | tee audit/normal_spike_examples_validation.log
