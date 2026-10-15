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
