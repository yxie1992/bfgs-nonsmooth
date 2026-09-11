#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../../.."
source scripts/env.sh
python3 audit/scratch/r_reconstruction19/verify.py
