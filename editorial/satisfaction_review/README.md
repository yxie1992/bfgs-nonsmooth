# Skeptical refinement of the author-review paper

This directory records the additional review requested after the narrative release. Start with REVIEW_LOG.md and the four *_critique.md records. JSON companions retain candidate hashes, exact contract locations, review limits and independently executed rational diagnostics.

`python3 editorial/satisfaction_review/integrate.py` refreshes reviewed correspondence, verifies all31 paper statement blocks against the preceding Git baseline, and registers the new full structural geometry audit without overwriting the earlier one. It must run before `bash editorial/build.sh` after any further prose revision.

`python3 editorial/satisfaction_review/formal/verify.py --run-id local_review` freshly compiles the unchanged ArticleGeometry and ConvexBalance modules and audits their complete checked structural closure. Use a new run id; original pinned library objects are reused. The actual first run is geometry_structural_01. Original corrected sources and all prior closed audit evidence remain unchanged.

The release integrity checker authenticates the current full evidence, and archive validation recompiles all three article supplements in fresh extraction-local output directories against explicitly checked pinned dependency caches. These are substantive proof, prose and execution checks; they do not certify publication priority, foundational consistency or human approval.
