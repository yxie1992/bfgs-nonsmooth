# Final targeted M42 infrastructure acceptance

**Verdict: ACCEPTED for the documented source-tooling grammar.**
**I1, I3, F1, F2 and D1 are resolved. Remaining blocker: none.**

Reviewed R at `dde6824c13e56a43b7b711132a8b09d24f8b5292` on 16 October 2026.
This acceptance is limited to the remaining fixes and their evidence binding.
The earlier mathematical and metadata semantic reviews were not reopened.

## Independently checked

- Regenerated the actual four-file runtime diff against the previous reviewed
  snapshot. It is **byte-identical** to my validated
  `production_fix_review/REMAINING_FIX_PROPOSAL.diff` and the implementer's
  `integration/final_small/APPLIED_RUNTIME.diff`. Only the two intended helpers
  changed; assembler and October checker bytes are unchanged.
- Matched all nine current delivered-file hashes to the focused evidence and
  matched current runtime bytes to both implementer test clones. Inspected the
  focused script and its **43 matched checks plus 3 baseline commands**, reusing
  the earlier validated prototype/matrices.
- Verified both supplied reviewed-metadata hashes and their exact bytes in the
  production evidence. Compared the saved output files and hashes independently:
  ledger, HTML and all three component reviews are byte-identical before/after;
  the receipt differs **only** in the two intended helper hashes.
- In a fresh scratch clone of `dde6824` with current tooling and the supplied
  reviewed metadata, matched **71 receipt-bound inputs** to current bytes, ran
  `refresh_correspondence.py --check`, and regenerated the ledger/HTML with the
  assembler. All six output hashes exactly match the focused production evidence.
- Ran **11 small independent F1/F2/D1 probes**: bare CR rejects before masking;
  LF/CRLF remain accepted; ordinary/raw-string, character, proposition and
  structure-final-literal bodies remain complete; strings cannot create
  declarations; balanced type subterms are retained while depth-zero token
  restrictions remain enforced. All passed.
- Read the revised wording in `INTEGRATION.md:113-148` and the October
  `README.md:203-211`; it accurately states the newline profile, separate trimming
  mask and delimiter-depth-zero restriction. Verified the archived
  `verification/INTEGRATION_FIX_REVIEW.md` preserves my original review bytes
  and hash with separate dispositions.

**29/29 recorded acceptance checks passed.** Artifacts are under
`final_acceptance/`: `ACCEPTANCE_CHECKS.json`, `ACTUAL_RUNTIME.diff`,
`INDEPENDENT_OUTPUT_DIFF.json`, and the two independent command logs.

## Resolution

| Finding | Accepted resolution |
|---|---|
| **I1 / F1** | Canonical-input guard now rejects bare CR before comment masking; the frozen resolver is untouched. |
| **I3 / F2** | Declaration recognition retains its literal-masked view; body trimming uses the comment-only view, preserving complete trailing literals. |
| **D1** | Documentation precisely limits the term-token refusals to delimiter depth zero and describes balanced subterms as lexical, not semantic, evidence. |

The approved metadata used only in scratch was byte-exact:

- `ADDITIONS.reviewed.json`: `10a582f0888c35830c4cfb5717b73bd280ff47869f46bde81d55081f4482499a`
- `CHANGES.reviewed.json`: `fe941216c6cf87a918d5a75eb1e6178243101468140ea1e4319b8f77dec5d283`

## Current runtime hashes

| Path | SHA-256 |
|---|---|
| `editorial/assemble_claim_ledger.py` | `36e7fa7c82de410d6f5ddbc2d2bafcab4ac10034be823d2429985561aafd00dc` |
| `editorial/coverage_additions.py` | `9cf6c3c41e00da7311ec8eae5e7c657fd2452c67940c6fdbc2eb7c15288e6157` |
| `editorial/lean_source.py` | `823795a178ee5dc80a286ebf1e6ce0cb6c3c070a001bce259b6207432fbe9413` |
| `editorial/release_20261015/refresh_correspondence.py` | `7dadc6d7d48869b7d2538ce37c18800451f38a3de834aca59f46ce82d5b67376` |

Full nine-file start/end records: `final_acceptance/SOURCE_HASHES_START.json` and
`SOURCE_HASHES_END.json`, observed from `2026-10-16T20:44:09.316870+00:00` to
`2026-10-16T20:48:26.113615+00:00`; all hashes and HEAD were unchanged.

R remained read-only, its real manifest remains empty, and the reviewed metadata
remains external for coordinator installation. No Lean/lake or broad-suite rerun
occurred; H/HOST was untouched. This is source-tooling acceptance, not additional
Lean semantic or kernel evidence.
