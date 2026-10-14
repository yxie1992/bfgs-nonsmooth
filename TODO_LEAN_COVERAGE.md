# TODO: Lean coverage of every claim

Started 14 October 2026, at the author's request: "We want lean to have 100%
coverage for all proofs and claims on both main manuscript and companion."
Reviewer: AI assistant (Claude). Method, statuses and rules:
`editorial/lean_coverage/README.md`.

Agreed scope:
- Every definition, named result, result stated in prose, and displayed formula
  asserted as true (also inside proofs), plus the claims of the abstract,
  introduction, remarks, tables and captions, gets a Lean theorem with the same
  statement. Each proof is covered by the Lean proof of its result; undisplayed
  connecting steps are left to the line-by-line reading of the proofs, which
  follows this work.
- Open questions are stated in Lean without proof and marked open. Literature
  results that the documents use are proved in Lean. History, motivation,
  descriptions of software or runs, and literature only mentioned are
  classified as non-claims with a reason.

Progress (`python3 editorial/lean_coverage/check_coverage.py`):

| Document | Mechanical items | Status |
|---|---|---|
| Article (`paper/`, 15 files) | 274 | in progress |
| Companion (`companion/`, 18 files) | 520 | not started |

## Open items

- [ ] Article: classify every item and write the coverage modules
      `bfgs_lean_article/BfgsArticle/Coverage/Article/*.lean`.
- [ ] Companion: the same, `.../Coverage/Companion/*.lean`.
- [ ] Integrate: import the coverage modules in `BfgsArticle.lean`, add the
      register names to the axiom audit, rerun the audit and the kernel replay.
- [ ] Discrepancies found on the way go to `TODO_MANUSCRIPT_REVIEW.md`.
- [ ] Non-vacuity follow-up: no admissible run is exhibited on the three-branch
      objective of Theorem `art:nonradial-example` (its objective-level hypotheses
      are shown satisfiable; runs are exhibited on |x|, max(x,−2x), u²+|v| and a
      quadratic). A general existence theorem for Armijo–weak Wolfe steps at
      differentiable points of finite convex maxima would settle it.
