# Minimal correspondence refresh for this exposition revision

Read-only review, 13 September 2026, against the current review registers from
`91d30dadcfd0980472c3896be0c9fd83fc7d4db1`. Other agents were still editing
TeX during inspection, so final locations must be calculated after integration.
No mapping, checker or audited evidence was changed by this review.

## Use the current registers as the starting point

Do **not** rerun `editorial/satisfaction_review/integrate.py`. Its baseline is
`dbe14e9`, and its byte-equal theorem-block assertion cannot accept the newly
reviewed notation aliases. More seriously, it runs the old narrative
rebuilders: `negative_record.py` reconstructs from `c84763f`, and
`integrate_reviews.py` reconstructs component/root data from older snapshots.
That is not a safe incremental refresh of the current branch-regularity and
cache registrations. The final companion branch record is also appended
without an idempotent ID check. Preserve these historical scripts and their
receipts; do not change their old baselines to make them pass.

Use the three current `editorial/*_contract_review.json` files as immutable
input snapshots for a small revision-local refresh. Retain these payloads
exactly, comparing the old/new JSON subtrees before accepting the refresh:

- Positive: `source_sha256`, `full_source_span_register`,
  `supplemental_formal_evidence`, `formal_project_dependency_closure` and
  `formal_dependency_audit`, except a genuinely required **additive** source
  union that is separately justified for a new deduction.
- Negative: `canonical_contracts`, canonical declaration-index/claims hashes,
  source-span/export/dependency and axiom data, `supplemental_formal_audit`,
  `supplemental_branch_regularity_audit`, and `companion_only_disposition`.
- Root: `supplemental_audit`, `supplemental_declarations`,
  `supplemental_audit_artifacts`, `supplemental_structural_audit`,
  `supplemental_branch_regularity_audit`, `supplemental_cache_binding`, legacy
  closures/axioms, canonical statement reviews and mathematical corrections.
  Keep the earlier `satisfaction_review` as history; add this revision's
  provenance rather than relabeling an old compiler run as current.

Also preserve the existing narrative supplement register and actual run
artifacts. Exposition and notation changes do not warrant different theorem
names, axiom closures, source exports or cache hashes.

## Refresh the fields that actually describe the new article

Resolve `editorial/active_tex_sources.py`'s input graph, not every archived TeX
file. Match each old named statement by its existing label; verify the same
theorem/lemma/proposition/corollary/definition label set and kinds. Store a
revision-level alias table with mathematical role, file/scope, old spelling,
new spelling and unchanged Lean definition. Compare statement bodies after
only these reviewed token substitutions and benign whitespace changes;
retain both raw hashes. Any remaining change requires explicit review.
Never normalize all occurrences of `c`, `d`, `n`, `p` or `M` globally: the
collision is precisely that these tokens have different mathematical roles.
The PSD Hessian remainder, seed inverse matrices, Wolfe margin, seed slope
coordinates and embedding index need distinct scoped entries. The coordinate
notation clarification near the cycle lemma also needs an explicit entry.

Refresh:

1. Positive `article_files`/`article_sha256`; each statement's
   `article_statement`, `article_location` and `proof_location`; equation
   `article_location`; unnumbered deduction `anchor`/`article_location`.
2. Negative `article_file_sha256`; label `article_file`/`line`; every
   `proof_locations` start/end and anchor. A canonical statement input is not
   its proof. Keep split proofs and appendix references explicit.
3. Root `article_file_sha256`; each active record's `anchor` and
   `article_location`, and its `scope_review` where exposition changed.

Require every active text anchor to occur exactly once in its specified file.
Require proof starts and ends in order and within bounds; count explicit
environments rather than choosing the first later proof regardless of label.
Update end anchors when inserting a new subsection between old segments.

Already observed stale anchors are:

- `root.introduction.mechanism`: old “We prove a hierarchy linking adjacent
  degrees”; current N1 text says “We prove an inequality linking”.
- `root.energy.nonnecessity`: old “The certificate is a sufficient
  convergence mechanism.” is currently absent.
- Positive residual-norm deduction: old “For example, a locally
  $C^{1,1}$ convex loss…” now begins “A locally $C^{1,1}$ convex loss…”.

If a redundant passage is intentionally removed, retain its old complete row
in revision dispositions/history and remove it from the active rows. Do not
attach its detailed old assertion to a vaguer surviving sentence merely to
obtain an anchor match.

## Record the newly explicit deductions without inventing Lean endpoints

The existing root-record shape already suffices: unique `id`, exact
`article_location` and `anchor`, `source_span_ids`, complete
`all_source_span_exports`, selected `primary_declarations`, and a concrete
`scope_review`. State the complete elementary derivation and whether there is
a literal Lean endpoint or a reviewed deduction from checked ingredients.
The latter must not be described as a newly compiled theorem.

- **N1 norm illustration / N4 norm examples:** link to
  `art:homogeneous-examples`, `H.span.9` and the existing homogeneous endpoints.
  Distinguish the elementary nonsmooth-locus observation from a publication
  priority assertion. N1 literature comparisons belong in `N1_review`, not
  among claims supposedly proved by Lean.
- **N4 smooth loss plus L1:** add the new
  `art:local-l1-decomposition` to positive `equation_mappings`, governed by
  `art:local-centered`, with a deduction for the fixed-sign neighborhood and
  zero-coordinate centered penalty. `R.span.8`/`R.span.11` and
  `BfgsVerification.AffineKinks.local_matrix_l1_basin` are existing relevant
  support. Keep uniqueness as an assumption and the conclusion local.
- **N3 field overview:** map the level-velocity, normal-angle joining,
  tangent-preserving derivative and decrease-paid transport to the existing
  planar-field appendix proof and its full C-span exports. It is an overview
  of that proof, not a theorem that arbitrary local equal-pairing fields glue.
- **N2 actual negative hypotheses:** separate the seed/cap homogeneity
  distinction; accumulating bad centers; active gradients at the true
  minimizer; failure of affine independence/strictly positive zero weights;
  and the quadratic secant decomposition. Relevant existing declarations
  include `DEmbedding.branch_zero`, `branch_old_hasGradient`,
  `phiFirst_zero`, `branch_last_hasGradient`, `center_tendsto` and
  `center_nonstationary`; `LEmbedding.branch_zero`, `branchGradient_zero`,
  `branch_hasGradient`, `copyCenter_tendsto` and `center_nonstationary`;
  `LQuadraticSeed.branch_hasGradient`; and
  `AffineWhitening.coordinateGradient_equiv`. These are prefixed by
  `BfgsVerification`. Select the precise source spans from the canonical
  claims register, rather than guessing a module-level endpoint proves each
  new sentence. Duplicate zero gradients imply failed affine independence;
  positive weight on the lone nonzero gradient prevents a zero weighted sum;
  an invertible coordinate change preserves those obstructions. These are
  explicit deductions, not necessity claims for convergence.
- **N5 figures/tables:** add the new `art:shrinking-scales` and any new scaling
  table labels as illustrations or comparisons of existing constructions.
  Negative `kind` must contain `illustration` for drawings, because the ledger
  assembler uses that string to produce `ILLUSTRATION_ONLY`. Preserve exact
  certificate inputs; a schematic position is not new numerical evidence.

## Reassemble once, then use the existing gates

`assemble_claim_ledger.py` is usable after the component refresh. It resolves
named-label locations and checks export membership, then regenerates
`editorial/CLAIM_LEDGER.json` and `companion/PROOF_CORRESPONDENCE.html`.
However, it copies unnumbered/root locations and proof locations directly;
it does not establish that the copied anchors, proof spans or stored statement
excerpts match current TeX. Its missing-statement scan covers named theorem
environments, not every new equation or figure. The explicit checks above
therefore belong in the bounded refresh receipt, not in an unsupported green
interpretation of the assembler.

Likewise, `verify_release_inputs.py` checks component article hashes and the
ledger's stored empty unmapped list. Updating hashes alone could leave stale
correspondence while passing these particular checks. Preserve all existing
21-check protections and run them after actual component review and assembly.
No permanent weakening or extra verification system is needed.

`editorial/build.sh` regenerates the companion and shared appendix and then
assembles the ledger before LaTeX. Consequently refresh against those final
generated sources; if the generator changes a mapped companion passage,
recalculate its root location/hash before the final gate. Keep the canonical
172 companion source spans and 3,087 source exports intact, with their own
generator preservation check. Finish with the actual build/reference/visual
evidence required for this revision, separately from the retained Lean runs.
