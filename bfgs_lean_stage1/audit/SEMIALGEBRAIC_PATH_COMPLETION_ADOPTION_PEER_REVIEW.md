# Milestone 17 adopted-source correspondence

Independent adoption check: **PASS**. This check concerns the correspondence and delivered audit setup. The new compiler/axiom/contract gate runs separately and is not inferred from this result.

For all 33 adopted Lean files, an independent comparison against the frozen reviewed source checked both SHA-256 hashes, equal line counts, and every changed line. Each changed line is exactly an import with `BfgsVerification.` prepended. Every non-import byte is unchanged. Recorded `import_normalizations` identify exactly those changed lines.

The delivered driver contains exactly the aggregate manifest's 152 declaration checks and 152 transitive-axiom requests, including the generated structure constructors and fields. Its 16 strict wrapper-target pairs match the manifest exactly. The seven original scope reviews and successful owner/peer evidence are preserved verbatim under `audit/semialgebraic_path_completion_reviews/`.

The delivered provenance validator was independently rerun successfully. Its source never reads a scratch path or the historical `reviewed_source` field: it reconstructs original bytes using the recorded import lines, compares `reviewed_original_sha256`, and checks public evidence and main-dependency hashes. Thus fresh reproduction requires delivered sources, public audit files, the existing main dependencies and the pinned toolchain. The optional historical scratch labels do not form a build dependency.

Evidence: `audit/semialgebraic_path_completion_adoption_peer_validation.log`. Compiler, axiom and exact-contract evidence is generated independently by `bash audit/verify_semialgebraic_path_completion.sh`.
