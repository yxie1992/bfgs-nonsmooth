# Milestone19 import-only reconstruction delivery

This directory prepares a new reconstruction tranche without modifying main
proofs, the central checker or release status. The corrected report and the new
nineteen-job execution register are owned separately by root; these scripts do
not assert historical run identity or promote a whole-report flag.

Expected source scopes are ObjectiveValueScaling (2 files/25 reports/1 target),
the explicit R reconstruction (5/53/2), and EReconstructionFacts (1/7/1).
The combined public scope has8 sources,85 actual reports and4 exact targets.
Only owned import lines are rewritten to their `BfgsVerification` main names;
all other proof bytes are preserved, and reversal reconstructs every reviewed
original hash. Owner and independent peer evidence are copied publicly.

The scoped manifest is `audit/reconstruction_completion_declarations.json`;
the driver is `audit/ReconstructionCompletionAudit.lean`. Its ordinary build,
type/axiom and exact-contract logs use `reconstruction_completion_*`, separately
from the later full `report_reconstruction_check.log`.

Root's sequence after independent tooling review:

1. `python3 audit/scratch/reconstruction_delivery19/prepare_delivery.py --apply`
   requires the exact committed/pushed release18 baseline19c7691 and its closed
   successful status. It installs only8 new library sources and public evidence
   and tooling. The default invocation writes scratch `preview/` only.
2. Source `scripts/env.sh` and run
   `python3 scripts/verify_report_sign_query_scoped.py --manifest audit/reconstruction_completion_declarations.json`.
3. After the actual ordinary scoped PASS, run
   `python3 scripts/register_report_reconstruction_19.py`.
   It preserves all251 old target pairs and the whole previous `Audit.lean`,
   including its cached prefix, and appends4 target print/inhabitant/axiom checks.
4. `python3 scripts/freeze_report_reconstruction_19.py` verifies all727 old
   library sources, all8 new sources, current registered checker/root and the
   exact full Audit before freezing737 source files.
5. Run the full pinned255-target central gate and close
   `audit/report_reconstruction_check.log` before root updates the corrected
   report status, new execution register, release documentation or manifest.

The new target block is `REPORT_RECONSTRUCTION_TARGETS`, the central success
label is `MODULE_M_AND_REPORT_RECONSTRUCTION_TARGETS_VERIFIED`, and the target
and freeze files are `audit/report_reconstruction_targets.json` and
`audit/report_reconstruction_source_hashes.json`. The public provenance validator
reads only delivered files; historical scratch labels are never runtime inputs.
No audit-prefix optimization or change to mathematical criteria occurs here.

Preview compilation and private registration/freeze fixtures must pass before
root invokes `--apply`. The three unrelated duplicate documents in the main
working directory are outside this delivery and are not touched.
