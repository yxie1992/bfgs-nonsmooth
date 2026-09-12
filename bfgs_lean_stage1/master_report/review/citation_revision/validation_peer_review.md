# Citation revision validation peer review

Reviewed on 2026-09-12. Scope: read-only review of `scripts/apply_report_attributions.py`, `scripts/verify_report_attributions.py`, the build/release-validator diffs, and the literature readers using `literature_audit/scripts/baseline_io.py`. This review did not rerun the full release gates or a fresh Lean build.

**Disposition: no blocking finding in the current revision.** The patch adds a preservation check to the public release gate without removing its prior compiler-evidence, independent source/index, corruption-rejection, browser, PDF or manifest checks.

## Confirmed properties

- **Historical baseline:** `baseline_bytes` accepts only a path listed in the unchanged literature `BASELINE.json`. A current file must have the recorded SHA-256; otherwise the reader uses the explicitly recorded 40-character Git commit and checks the historical object's SHA-256. Missing history fails with a recovery instruction. The readers no longer mistake current revised line numbers for historical audit locations. Their output reports the actual read location. This is an authorized change of where the historical bytes are read, not substitution of a new baseline.
- **Mathematical preservation:** the revision verifier checks all 22 recorded prior-file hashes directly against Git. It reverses the 41 exact note texts and five explicitly enumerated novelty-wording replacements, then compares each of the 14 chapters against the preceding edition. The five replacements remove novelty wording only. The 172 old/new claim records must retain IDs, modules, original source identity/ranges/hashes, classification, export lists and inherited review fields. The declaration index is compared as raw bytes; tracked Lean and toolchain changes are rejected.
- **Placement and editorial status:** every note is checked outside theorem, lemma, proposition, corollary and proof environments. Inspection of the actual 41 note records confirmed paired boundary markers and no macro redefinitions or input/include directives. Generated claims carry a distinct bibliographic-note status, the index displays an editorial notice, the dedicated register identifies its scope, and STATUS explicitly says external comparisons are not Lean-verified. These checks preserve scope rather than converting publication-history assertions into formal theorems.
- **Determinism and guards:** the application script computes the complete in-memory edit ledger, reverses its changes and compares every chapter before writing it. Existing unique-anchor, line-location, nonoverlap, original-source and proof-export guards remain. The builder includes note inputs in its hash inventory and checks that every note is mapped. The final verifier adds the attribution check alongside the previous gates. The literature-register rebuild consumes the same historical claim bytes after revision.
- **Evidence inspected:** `preservation_check.json` records PASS for 14 recovered chapters, 172 unchanged export lists and no tracked Lean/toolchain changes. `negative_guards.json` records rejection of all seven pre-existing corruption cases. These are inspected existing logs, not newly executed tests in this peer review.

## Nonblocking hardening observations sent to the parent task

1. In the initially reviewed `baseline_io.py`, the current-checkout fast path reads a file once for its hash and again for its return value. Reading once into a byte string and returning that same checked string would remove the narrow concurrent-edit race. There is no evidence of such a race in this revision.
2. The new baseline helper uses assertions but initially had no local `__debug__` guard. The validator rejects Python `-O`, whereas the register rebuilder does not. Rejecting optimized execution in the helper would ensure that the historical-byte checks cannot be disabled by importing it from that caller. The documented commands use ordinary Python and are unaffected.

These are implementation hardening recommendations, not evidence of a changed report theorem or a false current hash. The parent task was notified before this review was recorded.

## Limits

The verifier is not a LaTeX semantics engine or an external-source correctness oracle; the inserted prose still requires scholarly review. Its tracked-source Git comparison is supplemented by the existing compiler/source-inventory audit rather than being a standalone audit of every untracked scratch file. The historical commit must remain available in a clone, as the updated README states. Current chapter files contain LF line endings; the preserved-text comparison uses decoded text before its final byte comparison. No new mathematical assumptions, proof terms or relaxed axiom allowlist were introduced by the reviewed diffs.

## Resolution after final read-only recheck

Both hardening observations are **resolved** in the final reviewed helper. A module-level `if not __debug__` rejection now runs before baseline loading or register work. The current-checkout path reads once into `current_bytes`, hashes that value and returns the same checked bytes. The historical Git-object SHA-256 check remains in place.

Final reviewed `literature_audit/scripts/baseline_io.py` SHA-256: `4a8824bd8ebb0149047d97c2e0d352b4d96b08b79e9e64e660a9c0e1e472490e`.

This reviewer independently ran both `rebuild_register.py` and `validate.py` with `python3 -B -O`. Both returned exit 1 with the expected baseline-assertion guard message, before register writes; no additional files were written by those checks. The refreshed existing `literature_audit/review/validation.log` was also inspected and records PASS for all 18 baseline inputs and the supplement manifest. The parent reports that this log came from `validate.py --write-manifest`; the full gate was not rerun here.

Final disposition remains **PASS; no unresolved actionable findings in this review**.
