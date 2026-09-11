# Original-claim review and additional Lean proofs

This package supplements the existing whole-report verification with a direct
review of critical original claims, expanded contracts, and new proofs. Read
[the claim review](../../CLAIM_REVIEW.md) for the precise mathematical scope,
[claim dispositions](CLAIM_DISPOSITIONS.json) for the distinctions between
errors, qualifications and unsupported history, and [status](STATUS.json) for
the release result. It does not certify every original sentence as true.

| Driver | Content |
|---|---|
| [M](sources/ExpandedContracts.lean) | Actual principal determinants and matrix hierarchy, raw full-BFGS growth hypotheses, original constants, exact Gram sum and sharp potential. |
| [A/C](sources/GeometryContracts.lean) | Actual supporting sets, semialgebraic graph and path hypotheses, affine-critical cluster and conditional convergence statements. |
| [D/L](sources/NegativeClaims.lean) | Literal negative-example contracts, actual construction bridges and parameter independence. |
| [Search](sources/SearchFuel.lean) | Successful exact search returns the same complete result and history with any additional fuel. |
| [R/U](sources/OriginalClaimInterpretation.lean) | Homogeneous intercept at arbitrary reference; positive degree and unique optimizer derived in R's compact context; actual zero-coupling split in U. |
| [R/U peer](sources/PeerContracts.lean) | Exact copy of the R/U source followed by nine independently restated contracts. The repeated seventeen declarations are counted as repeated checks. |

The package has 70 distinct owned declarations: 41 theorems and 29 definitions.
The peer driver repeats 17 of those declarations. The full audit emits 182
ordinary axiom-report occurrences concerning 141 distinct declarations,
including selected existing library declarations. Its 35 exact markers comprise
28 literal comparisons, five raw-interface checks and two completion markers.
Neither repeated reports nor definitions are counted as new mathematical
theorems. The unchanged main library's counts are reported separately.

All six sources are byte-identical to their reviewed standalone versions. The
peer driver must begin with the exact R/U source bytes. The
[job manifest](jobs.json) freezes source hashes, ordered ordinary reports,
expected axiom sets, literal markers and review metadata. Only `propext`,
`Classical.choice` and `Quot.sound` are permitted. The baseline binds all 737
main Lean sources, pinned configuration and relevant unchanged original
chapters. The prior full-report validator separately checks all 22 original
research artifacts and the complete earlier reconciliation.

From `bfgs_lean_stage1`:

```sh
python3 scripts/validate_report_reconstruction_19.py
python3 scripts/verify_report_claim_review_20.py --run
python3 scripts/verify_report_claim_review_20.py
```

The run performs an incremental `lake build BfgsVerification`, then invokes the
pinned compiler on each actual source. It uses existing build artifacts and is
not a new clean build. It clears inherited `LEAN_PATH`, records actual commands,
working directories, UTC times, durations and exit codes, and hashes sources
and outputs. All nine dependency revisions and clean states are recorded before
and after execution. Input changes, missing reports, changed types or axioms,
failed compilers and incorrect markers fail the gate.

The first public execution lives in [fresh/SUMMARY.json](fresh/SUMMARY.json).
Later `--run` calls preserve it and automatically select a new UTC-named folder
under `runs/`; the runner prints the exact command for validating that run.
Without `--run`, the command validates the delivered `fresh/` evidence. An
explicit `--run-dir` selects another run within this package. Every artifact
stays in the repository. Reproduction reads no scratch directory or missing
source input.

The files under `reviewed_logs/` are the completed authoring-stage audits for
this new review, not the report's unsupported older execution history. The
files under `fresh/` are the subsequent public-path executions. The reviews
under `reviews/` state which original proofs and hypotheses were examined;
they are independent agent reviews, not human referee reports. The final
delivery review and supplemental status also bind the new mathematical
interpretations and the unchanged earlier whole-report evidence.
