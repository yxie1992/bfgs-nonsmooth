# Completion gates, review loop, and Git milestones

## A finite, substantive completion target

Work until the article and companion are author-review-ready under the gates below, not until an impossible self-certified promise of journal acceptance or novelty. Continue past the first draft and first build. Do not require the author to approve every ordinary editorial choice.

A genuine external dependency may remain (author affiliation/consent, inaccessible source, unavailable remote authentication). Record it explicitly; it cannot be turned into a passed gate by omitting the evidence. Complete all independent work. A mathematical gap or failed audit is a substantive blocker and must not be described as cosmetic author input.

## Required review passes

Run at least three distinct author-side self-review passes and revise after each. They are not external peer review.

### Pass 1 — Contract and proof review

For every main theorem, read the exact statement, all hypotheses, proof and mapped Lean contracts. Check dimensions, constants, quantifier order, finite versus infinite runs, actual BFGS versus abstract recurrence, weak versus strong Wolfe, and what compactness/uniqueness actually supplies. Verify the proof uses only established lemmas in the stated domains.

Check the negative constructions separately: object regularity, fixed objective, initial matrix, exact line-search outputs, differentiability of all claimed queries, secant positivity, closure, scaling, all-trial containment and nonstationarity. Check stable-manifold existence is not represented as a numerically exhibited initial state.

Check corrected determinant signs, actual right-derivative arguments, accessible-jump qualifications, regularity of constructed fields, normal/tangent restrictions, and interception/translation terms. No silent hypothesis strengthening or conclusion weakening.

### Pass 2 — Narrative and scholarship review

Read the article without the companion open. Can a reader state the problem and main positive/negative contrast after two pages? Are new conditions motivated before their notation? Does each section answer a question? Do proof sketches explain the actual mechanism rather than announce “by a calculation” at the key step?

Read the abstract and conclusion against the claim ledger. Remove hype and scope inflation. Make known special cases and standard ingredients explicit. Inspect every novelty comparison and its primary source/version/access evidence. Keep the report's internal history out of the article's plot.

### Pass 3 — Production and reproducibility review

Build both documents from the documented commands; run the available current formal and source audits without weakening them. Record exact commands, commit and exit status. Check cross-references, bibliography, theorem numbering, symbols, compilation warnings and source portability.

Render and inspect every page. Fix clipping, tiny text, dense tables, badly broken equations, duplicate labels, blank pages and unreferenced figures. Compile again after changes. Recheck the theorem/notation map whenever statements change.

Write a closure entry identifying all issues found, how they were resolved, and the evidence for each resolution. A checklist with every box ticked but no performed checks is not a review record.

## Release gates

- [ ] Coherent narrative: introduction, theorem set, section structure and conclusion agree.
- [ ] Article main claims have complete proofs within the article and its own appendices.
- [ ] Strongest incomparable results remain in the companion; omissions have a justified ledger entry.
- [ ] Every claim has a corrected source/formal-contract/attribution mapping.
- [ ] No unresolved mathematical TODO, placeholder proof or invented computation remains.
- [ ] Formal coverage statement is consistent with actual current audits; no reliance on declaration counts alone.
- [ ] No altered proof-checking rules, hidden axioms, unsafe proof dependence or redefinition to make the claim trivial.
- [ ] Exact, interval, symbolic, high-precision, schematic, and historical evidence are distinguished.
- [ ] Both PDFs build cleanly and every page is visually inspected.
- [ ] Figures and supporting computations reproduce from source.
- [ ] Journal fit, page count, proof placement and companion status are documented.
- [ ] AI-use and reproducibility disclosures are factual; author approval and missing personal metadata are separately listed.
- [ ] Worklog, review log, manuscript/companion maps, hashes and release commands are current.
- [ ] Major milestones are committed and pushed, or a push failure is honestly recorded with local commit intact.

## Git workflow

The user explicitly requests commits and pushes at major milestones. Inspect and follow repository instructions and existing branch conventions first. Do not overwrite uncommitted user changes, reset history, force-push, change repository visibility, or silently merge into protected branches.

Recommended milestones:

| Milestone | Concrete deliverable | Check before commit/push |
|---|---|---|
| A — Baseline and scope | Corrected source inventory, operative formal contracts, selection and journal-fit plan | Sources resolve; user work preserved; planned theorem set is coherent |
| B — Complete article v1 | Full text, main proofs, first figures and bibliography | Build succeeds; no missing central proof; claim IDs mapped |
| C — Complete companion | All retained results, proof/citation/source maps and reproducibility structure | No incomparable result lost; formal/current-source scope reconciled |
| D — Author-review release | Revised PDFs, source archive and completed review evidence | All release gates checked; renders inspected; actual audits recorded |

Use concise descriptive commits. Run `git diff --check`, inspect the diff and staged files, and commit only relevant changes. Use the configured authorized remote and working branch. If the branch has no upstream, use the existing project remote according to its convention; never invent a remote URL. Verify the push outcome. Authentication/network/protection failure is not permission to bypass safeguards; record it and continue local unblocked work.

Do not commit secrets, credentials, personal information unrelated to authorship, downloaded copyrighted full-text literature without permission, toolchain caches, `.lake` build trees or giant transient render directories. Respect the repository's policy on tracked release PDFs. Preserve source snapshots and audit evidence, with hashes for regenerated artifacts as appropriate.

A reproducible verification record should identify the audited source commit. If generating the record itself creates a later commit, state both relationships rather than making an impossible self-containing hash claim.

## Persistent state

Maintain concise, factual files such as:

    editorial/WORKLOG.md
    editorial/NEXT_ACTION.md
    editorial/CLAIMS.csv
    editorial/SUPERSESSION.md
    editorial/ATTRIBUTION.csv
    editorial/REVIEW_LOG.md
    editorial/JOURNAL_FIT.md
    editorial/AUTHOR_ACTIONS.md

Write observed results and decisions, not private internal reasoning. At a context interruption, include the current branch/commit, completed gates, unresolved issues and exact next command. Do not claim that work continues unattended after the session ends.

## Final response

Report the produced paths, paper/companion page counts, build and audit outcomes, exact claimed formal coverage, milestone commits and push results, and genuine author actions. Identify any remaining blocker plainly. Do not say “submission-ready” when consent, proof correctness, required citations or mandatory declarations remain unresolved; “author-review-ready” is the intended deliverable.
