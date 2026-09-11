# Reconstruction delivery evidence

These are the actual authoring and independent fixture-review records. Paths
inside historical commands and manifests identify their original authoring
locations; they are provenance labels, not runtime dependencies. The delivered
proofs are checked using `scripts/verify_report_sign_query_scoped.py --manifest
audit/reconstruction_completion_declarations.json`; delivered-only provenance is
checked by `audit/validate_reconstruction_completion_provenance.py`. The central
registration and freeze scripts are in `scripts/`. The complete current release
gate is `scripts/validate_report_reconstruction_19.py`.
