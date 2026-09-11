# Cached axiom audit evidence

The shared graph collector has been compared exhaustively against the closed ordinary milestone17 audit: all 7,684 actual theorem types and axiom sets match. The earlier 7,486 theorem comparison and all 152 independently collected scoped sets also match. The helper reproduces each pinned Lean4.19 checked-environment dependency case and computes reverse reachability from every discovered axiom. Seven cycle cases and an independent source review are included.

These files are audit tooling and evidence, not mathematical proof premises. No custom axiom or assumption is introduced into the project proofs. The pinned compiler and full project build remain required.

Public commands, from the project directory:

1. `python3 scripts/validate_cached_axiom_audit.py --baseline-only` validates the frozen ordinary/cached17 comparison and evidence hashes.
2. After root adopts the three Module M proof files and registers both targets, `python3 scripts/prepare_cached_axiom_adoption.py` captures the entire current ordinary Audit, checks that its old tail is preserved and the new target commands exist, and writes `ProposedCurrentAudit.lean` plus exact prefix/tail provenance. It does not change main Audit. Root reviews and adopts that candidate separately.
3. `bash scripts/run_cached_axiom_snapshot.sh` extracts every current actual theorem type and axiom set, including all 170 scoped declarations across milestones17/18. It builds only the audit helper and uses the already compiled main library; it does not replace the project's build step.
4. After the full current central gate has closed, `python3 scripts/validate_cached_axiom_audit.py` checks every current theorem type/set against the fresh snapshot, the entire unchanged old inventory, all 18 new ordinary-scoped axiom sets, three proof-source hashes, all 251 registered target signatures, and exact adopted prefix/current-tail preservation.

Optional ordinary-collector reproduction remains available. Source `scripts/env.sh`, then run `python3 scripts/reproduce_standard_axiom_audit.py --run`. It combines the original ordinary enumeration prefix with the complete current tail, invokes Lean's standard collector on every current theorem, and compares every result against the cached snapshot. It never edits Audit or check.py and may take substantially longer.

`evidence_manifest.json` freezes all static public files. Historical paths inside copied reviews/manifests are provenance labels only; validators do not read them. Current snapshot/adoption/output files are intentionally separate from immutable reviewed evidence. The baseline comparison is already complete. Current18 comparisons require the new main files, actual ordinary scoped logs, prefix adoption, fresh snapshot, and completed current central gate; their success is not asserted in advance.
