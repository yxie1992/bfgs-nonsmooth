#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/env.sh
BFGS_CACHE_EVIDENCE="$PWD/audit/cached_axiom_evidence"
export LEAN_PATH="$BFGS_CACHE_EVIDENCE:${LEAN_PATH:-}"
python3 scripts/validate_cached_axiom_audit.py --baseline-only
python3 - <<'PY'
from pathlib import Path
import json
base=Path('audit/cached_axiom_evidence')
names=[]
for manifest in ['audit/semialgebraic_path_completion_declarations.json','audit/module_m_literal_completion_declarations.json']:
 for name in json.loads(Path(manifest).read_text())['declarations']:
  if name not in names:names.append(name)
assert len(names)==170
(base/'CurrentRequestedNames.lean').write_text('import Lean\nnamespace ExperimentalAxiomAudit\ndef currentRequestedNames : Array Lean.Name := #[\n'+',\n'.join('  `'+name for name in names)+']\nend ExperimentalAxiomAudit\n')
PY
lake env lean -o "$BFGS_CACHE_EVIDENCE/CachedAxiomGraph.olean" "$BFGS_CACHE_EVIDENCE/CachedAxiomGraph.lean" > "$BFGS_CACHE_EVIDENCE/current_helper_build.log" 2>&1
lake env lean -o "$BFGS_CACHE_EVIDENCE/CurrentRequestedNames.olean" "$BFGS_CACHE_EVIDENCE/CurrentRequestedNames.lean" > "$BFGS_CACHE_EVIDENCE/current_names_build.log" 2>&1
lake env lean "$BFGS_CACHE_EVIDENCE/CycleChecks.lean" > "$BFGS_CACHE_EVIDENCE/current_cycle_checks.log" 2>&1
lake env lean "$BFGS_CACHE_EVIDENCE/CachedCurrentAudit.lean" > "$BFGS_CACHE_EVIDENCE/current_cached_audit.log" 2>&1
printf '%s\n' 'PASS:fresh cached current environment snapshot extracted;run validate_cached_axiom_audit.py after the central gate closes.'
