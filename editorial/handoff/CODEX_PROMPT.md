# Execute the BFGS paper-and-companion authoring project

You are continuing this work in my existing Git repository. Produce a coherent, polished optimization journal paper and a reorganized complete companion report from the current corrected mathematical and Lean record. Aim at the standards of Mathematical Programming or SIAM Journal on Optimization. This is an implementation/authoring task, not a request for another plan.

## Goal and persistence

Keep working through source inspection, mathematical selection, drafting, proof reconstruction, attribution, figure production, builds, visual inspection, formal correspondence, and revision until the completion gates below are satisfied. Do not stop after writing an outline, scaffolding LaTeX, obtaining one successful build, or making one editorial pass. Make routine editorial decisions yourself and document consequential ones. Do not ask for repeated approval of section order or filenames.

The deliverable is an **author-review-ready research article**, not a claim that a journal will accept it or that human review has already occurred. If a genuine external blocker prevents completion, finish everything unblocked, record the exact blocker and evidence, and report the remaining action honestly. If execution/context must end, leave a precise checkpoint and next command, commit/push the checkpoint as appropriate, and do not claim completion. Do not promise unattended work after execution has stopped.

## 1. Establish the authoritative baseline

First inspect repository instructions, `git status`, the current branch/remotes, recent history, and the actual file tree. Preserve existing user changes. Read the latest corrected manuscript, not just the original 76-page report. Locate the operative inventory, corrections ledger, Lean project, pinned dependencies, proof index, claim/source maps, audit outputs, and literature audit.

Likely names include `MASTER_RESULTS.md`, `VERIFICATION_REPORT.md`, `master_report/PROOF_INDEX.html`, `CLAIMS.json`, `SOURCE_MAP.json`, `literature_audit/`, and LaTeX `chapters/` and `coverage/` directories; discover actual paths rather than assuming them. The attached editorial package inspected the 11 September corrected edition in `latex.zip`, but your repository may be newer. Do not restart from the old uncompiled stage-one Lean draft.

Write a baseline record with the Git commit, operative paths, current proof/audit status, source versions, and any conflicts. Exact formal theorem contracts determine formal scope; the corrected prose and human correspondence review explain that scope. If they conflict, investigate and log the discrepancy rather than silently favoring a convenient version. Historical reports and this editorial brief do not override corrected mathematics.

Read the handoff documents, especially `RESULTS_SELECTION.md`, `PAPER_BLUEPRINT.md`, and `JOURNAL_POLICY.md`. They prescribe editorial organization, not unproved stronger theorems.

## 2. Preserve the exact mathematical scope

The algorithm is unmodified **full BFGS** with Armijo–weak-Wolfe and actual gradients at differentiable accepted iterates. Keep all quantified hypotheses visible: finite-valued convex objective, dimension, local structural neighborhood/compact sublevel, initialization, and the distinction between an infinite admissible run and a particular deterministic line search.

Do not substitute L-BFGS, damping, restarts, proximal methods, strong Wolfe, or nonlinear coordinate invariance. Do not assume iterate convergence, a favorable matrix limit, or a spectral bound in a theorem meant to derive convergence. Distinguish objective convergence, distance to the solution set, whole-iterate convergence, and finite termination of a line search.

Preserve the actual local-counterexample quantifiers: one fixed objective and fixed implementation/parameters/initial matrix; arbitrarily close bad starting points; nonstationary limits; and all-trial containment where proved. This does not mean every close start fails, a positive-measure failure basin, floating-point robustness, or failure of every unit-first routine.

Keep the two local negative results separate: the globally C^{2,1} convex-branch construction lacks a uniform positive lower curvature assumption; the uniformly strongly convex finite-branch construction is C^{1,1} and loses second differentiability at the accumulation point. Do not combine them into a finite uniformly strongly convex C^2 local counterexample. The quadratic strongly convex example is global failure, not local failure near its own true minimizer.

The full matrix principal-minor theorem and its bridge to scalar reciprocal growth must remain actual BFGS results, not assumed recurrences. Preserve the weaker-assumption and finite-horizon versions when they are not logically subsumed by the strongest summable-budget result.

Treat geometry such as “preserved descent” as interpretation unless an exact theorem establishes it. In particular, affine criticality and accessible-jump geometry are not a necessary-and-sufficient classification. Do not identify all active jumps with accessible jumps without the needed hypothesis. Use the corrected planar determinant orientation and one-sided derivative proof; C^2 branches do not produce an arbitrarily smooth field. Preserve corrections to radial intercepts and coupling/eligibility qualifications.

## 3. Build one unified story

Suggested title: **BFGS on Convex Nonsmooth Functions: Local Convergence and Failure**. Refine it only for clarity or verified scope.

Core thesis: regularity inside smooth branches alone does not guarantee local convergence; identifiable compatibility between gradient jumps and remaining descent does support convergence through a comparison-energy framework, without presumed matrix behavior.

Lead with the sharp contrast: finite polyhedral local geometry with smooth cell extensions admits local convergence, whereas finitely many globally very smooth convex branch formulas can encode deterministic local failure. Explain that finitely many formulas do not imply finitely controlled local switching geometry. Introduce the lower-curvature result as an independent strengthening along another regularity axis.

Use `u^2 + |v|` as the running intuitive example: vertical gradient jumps and surviving horizontal descent. Contrast it with the specific certified nonstationary corner, not an arbitrary corner claimed to fail. At an optimizer, contraction may be appropriate; at a wrong vertex the constructed algorithm can contract without eliminating the objective gap. Present this as an explanation of the proved examples, not universal matrix asymptotics.

Explain the reference-energy identity before the principal-minor machinery: it has a decrease term measuring missed progress and a positive secant correction. The reciprocal-growth theorem gives the budget that the objective geometry must defeat. Then motivate the certificate's visibility, secant, and transport requirements in words before displaying matrix inequalities. Move from a fixed radial comparison direction to moving geometry, then to controlled residuals in smooth directions.

## 4. Author the journal article

Default to a Mathematical Programming-style regular article unless the repository already establishes a target. Aim for roughly 30–35 normal journal-style pages including essential appendices and references, as an editorial budget, not a publisher limit or guarantee. If scope makes this unrealistic, reduce the article's advertised theorem set and retain the additional results in the companion; never hide indispensable arguments or compress typography. Document significant length exceptions. Assess SIOPT separately against its actual policy rather than calling the same long manuscript compliant with both journals.

Use this structure, adapting boundaries for clarity:

1. **Introduction and main results.** The question, prior context, positive/negative contrast, precise scope and contribution statements. State the main negative results early, even if their proofs come later. Readers should know the main conclusion within two pages.
2. **Geometry of progress and stagnation.** The mixed ridge and the actual bad corner; first-order model agreement; affine versus convex balance; local versus global failure. Integrate the first figure. Avoid an abstract catalogue.
3. **A common BFGS energy principle.** Update/line search, reference energy, actual principal-minor hierarchy, reciprocal growth, and the sufficient certificate. Include the complete essential proof chain, with technical algebra in article appendices if needed.
4. **Geometries guaranteeing local convergence.** Centered homogeneous/sublinear geometry, smooth perturbations, inward radial smoothness, and finite local partitions. Give a few meaningful examples rather than many nearly identical corollaries. Explain each assumption's role.
5. **Beyond radial geometry.** Present selected strongest geometric extensions with complete proofs: preferably the planar affine-critical result and its nondegenerate smooth-max corollary. Include the fixed-normal multidimensional theorem if its full argument fits the article's claim budget; otherwise keep it as a clearly identified companion result, not an unproved article headline. Keep the planar, fixed-normal, and flat-contour parabolic cases distinct.
6. **Deterministic local failure despite regularity.** Explain the seed, its exact cycle and actual trial tree, then the shrinking smooth embedding. Treat the positive-curvature/stable-manifold extension separately. Give a mathematical proof of the computer-assisted claim: objects, sound certificate, strict bounds, and infinite induction—not “the script passes.”
7. **Verification and the remaining boundary.** Concise formal-verification scope and reproducibility, limitations, and a focused conclusion. No claim that the area is finished or that all convex nonsmooth cases are classified.

The article must stand mathematically on its own for its main results. Complete proofs may appear in appendices within the same article. The companion is not a substitute for an essential lemma or theorem proof. Do not rely on journal-published supplementary proofs: check `JOURNAL_POLICY.md` and the live journal pages.

A short summary of additional companion results is acceptable only if explicitly marked as such, precisely referenced, and excluded from the article's independently established main contribution claims. Favor a smaller complete article over a large incomplete theorem catalogue. Keep both positive and negative results central; do not silently turn this into a negative-only paper or split it into multiple journal submissions.

## 5. Produce the companion, not an archive dump

Create a coherent complete companion report from the corrected edition. Preserve every strongest nonredundant positive, negative, geometric, and quantitative result. Use shared notation and prove shared foundations once. Retain full noncompact homogeneous theory, lifting, rates, certificate nonnecessity, auxiliary families, exact construction details, and extended verification there.

Maintain a supersession ledger: an omitted theorem needs a precise stronger implication and retained location. Incomparable hypotheses or conclusions require separate entries. In particular, preserve the two local counterexamples, simple global corollaries, noncompact homogeneous clauses, fixed-normal versus planar geometry, flat-contour parabolic family, and scalar baseline. The earlier two-branch scalar-ridge theorem may be presented as the already-justified planar corollary; retain the independent proof as provenance when present.

Keep original source snapshots and prior correction ledgers unchanged. Give every theorem in either new document a mapping to its corrected source, all needed Lean exports and exact type/hypothesis correspondence, and proof location. One sample export in a coverage table is not automatically the whole proof. Record definitions, hypotheses, conjectures, and historical process statements separately from theorems. Preserve the current axiom policy and existing formal audits; do not weaken checks to obtain a green build.

## 6. Attribute previous work accurately and conventionally

Use the existing literature audit as a starting point. Verify the primary sources for each load-bearing comparison, with author list, title, version, publication status, theorem locator, exact hypotheses/conclusion, and access level. Record search dates and limits. Metadata or an abstract is not a full-proof inspection. Never copy audit claims into “we read” statements unless supported by an actual record.

Organize related work by mathematical role: classical smooth-BFGS analysis and matrix potentials; unmodified nonsmooth-BFGS positive results; failures with different algorithms/line searches/objective assumptions; and VU/partial-smoothness/stratification ingredients. Consult the keys identified in `ATTRIBUTION_GUIDE.md`, including Guo–Lewis, Xie–Wächter, Lewis–Overton, Powell, Byrd–Nocedal, Gebken, the geometric antecedents, and the relevant earlier negative examples. L-BFGS may be compared bibliographically but is not our algorithm.

Clearly separate a known special case, a standard proof tool, a consequence of existing machinery, a refinement/generalization, and a potentially new complete theorem. Do not claim Euclidean-norm convergence or finite two-piece escape as newly discovered. Do not overstate the novelty of basic Gram/Schur algebra, cocoercivity, or affine-critical-value geometry. Preserve exact-version numbering and updated author lists. Keep unresolved attribution unresolved.

Write an integrated scholarly related-work section and point-of-use citations, not repeated provenance blocks before every lemma. Replace internal report labels with article cross-references; the paper's bibliography is not a list of chat-generated reports. Do not assert “first,” “complete,” “sharp,” or “optimal” without evidence. Human authors must review cited sources and novelty claims before submission.

## 7. Figures, numerical evidence, and verification

Produce up to three purposeful vector figures from reproducible mathematics/code: (i) gradient-jump geometry and remaining descent, (ii) the certified three-step cycle and rejected trials, and (iii) isolated versus accumulating bad configurations. Use the canonical corrected seed and label exact-data renderings versus schematics. Make all figures legible in grayscale and at final size. Do not use an arbitrary numerical trajectory as proof of stable-manifold membership or floating-point robustness.

Include a small table separating the local counterexamples' regularity assumptions, and one compact positive/negative scope map if space permits. Every figure/table must answer a question in the text. Do not pad the article with a large empirical benchmark suite; this is a mathematical paper.

Explain Lean briefly in the article, with exact theorem-level coverage in the companion. Review the current main theorem contracts and actual transitive audit evidence. Reproduce available builds/audits in the pinned environment; if costly or blocked, record precisely what ran and what did not. Do not restore withdrawn historical execution counts. Formal verification does not certify novelty, natural-language translation, or practical floating-point behavior.

Draft truthful AI-use and reproducibility disclosures from the actual research record and current journal guidance. Do not describe theorem development/formalization assistance as grammar checking only. Do not invent author consent, authorship, affiliations, grants, ORCIDs, repository DOIs, or human independent review. Mark human-supplied metadata/actions separately for author approval. Do not submit to a journal, create a public archival deposit, or email anyone.

## 8. Required outputs and persistent work record

Adapt paths to the repository, but deliver:

- `paper/`: modular LaTeX, bibliography, figure sources, build entry point, and compiled article PDF.
- `companion/`: reorganized complete report source, compiled PDF, proof appendix/correspondence and reproducibility material.
- `editorial/`: baseline, narrative/selection decisions, claim ledger, supersession ledger, attribution ledger, policy check, notation map, review log, worklog and actionable next-state file.
- `release/`: author-review PDFs and source archive/manifest (or the repository's existing release layout).
- A concise final status stating actual files, page counts, build/audit results, verified scope, commit hashes and push outcomes, plus genuine remaining author actions.

Share stable definitions/notation/bibliographic data where useful without forcing both documents into the same structure. Avoid duplicate hand-edited canonical theorem statements. The article should not inherit module-letter numbering, a report-style table of contents, correction history, or code-audit blocks in its main narrative.

## 9. Commit and push major milestones

This is a Git repository, and I explicitly want major milestones **committed and pushed**. Follow repository instructions and existing branch conventions. Inspect changes before staging; commit only task-related files, never unrelated user edits, secrets, downloaded copyrighted papers, large dependency caches, or unnecessary build debris. Use the existing authorized remote; do not invent a remote, change visibility, force-push, rewrite shared history, or discard work.

Suggested milestones:
A. Baseline, authoritative claim map, selection plan and policy decision.
B. Complete article v1 with main proofs and figures.
C. Complete companion and cross-document/formal/attribution mapping.
D. Revised, built, visually inspected, audited author-review release.

At each milestone update the worklog, run the relevant checks, inspect the diff, commit meaningfully, and push the working branch to its configured remote. Verify push success and record the commit. If authentication/network/branch protection blocks pushing, preserve local commits, record the exact error, continue unblocked work, and report the unresolved push; never claim it succeeded. Do not auto-merge into a protected branch.

## 10. Definition of done: revise until these gates pass

Conduct and document at least three distinct author-side review passes: mathematical scope/proof completeness; narrative/novelty/readability; and build/visual/reproducibility integrity. These are your self-review passes, not independent human peer review. Fix every substantive issue they reveal and repeat as needed.

The job is complete only when:

1. The title, abstract, first two pages, theorem set, proof structure and conclusion tell the same precise story.
2. Both positive and negative results are central, with no false necessary-and-sufficient boundary or mixed counterexample assumptions.
3. All article main claims have complete arguments in the article and its own appendices; no essential result is outsourced to a companion citation, a script, or Lean alone.
4. Every retained claim has a completed source/formal/attribution mapping, and all omitted results have a justified disposition.
5. The strongest incomparable results are preserved in the companion, with corrected proofs and no resurrected withdrawn claims.
6. Both documents compile from documented commands, references resolve, figures are reproducible, and every page has been rendered and visually inspected. No substantive placeholder or authoring TODO remains.
7. Current verification status is evidenced, not inferred from old counts; exact, interval, symbolic, numerical and formal evidence are distinguished.
8. Journal-policy constraints, page count, companion status, and honest AI/reproducibility disclosures are documented. Human metadata/consent/public-deposit decisions are explicitly reserved for the author.
9. Three review passes are logged, major milestones are committed/pushed, and the final release is traceable to a Git commit; any external failure is clearly marked rather than silently waived.

Now inspect the repository and begin executing. Use the editorial handoff as a guide, but let the corrected proof contracts and current journal guidance constrain every substantive claim.
