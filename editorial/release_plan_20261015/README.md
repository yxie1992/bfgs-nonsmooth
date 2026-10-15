# Release-run plan, 15 October 2026

A read-only study, by an AI agent (Claude in OpenCode), of how to make the next
release run. It was made while step 2 (the manuscript corrections) was in
progress, on a scratch copy of commit `1abfe07`, and it changed nothing in the
repository. Its scratch directory is copied here so that the plan and its
evidence survive.

- `PLAN.md`: the plan. The scripts and how the 13 September release ran; the
  checks C1–C18 that fail or need updating, with their fixes; the Lean runs; what
  to preserve; the decisions D1–D8; a step-by-step sequence; failure modes;
  snippets.
- `PROGRESS.md`: the agent's working notes.
- `tools/`: its helper scripts.
- `*.json`, `*.err`, `dry_*.log`, `cov_*.txt`: the evidence of its dry runs
  (PLAN.md, Appendix B).

In the plan, `S` is the agent's scratch directory (any directory outside the
repository will do), and `H` is the September checkout on the MacBook, which holds
the sealed Lean host cache and the earlier editions' archives and must stay
untouched. The open items are tracked in `TODO_LEAN_REVIEW.md` ("Release receipts
are now stale").

After an independent review of the release tooling (15 October,
`editorial/release_20261015/TOOLING_REVIEW.md`), two parts of the plan changed:

- the order of Phase 2: the Lean evidence (axiom audit and kernel replay) comes
  after every change to the claim ledger, the coverage registers and the counts
  printed in `companion/current_verification.tex`, since the release-input check
  binds the evidence to them (section "Run order" of
  `editorial/release_20261015/README.md`);
- the Lean host (D2, D3): an APFS copy (`cp -cR`) of H's `bfgs_lean_stage1/.lake`
  and `.toolchain`, outside the temporary directories, instead of H itself. The
  copy passes the cache-binding check, and a full scratch validation against it
  left H unchanged, while linking H itself writes to it (elan's `known-projects`
  file, git index locks in its dependency checkouts).
