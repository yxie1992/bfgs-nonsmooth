# Agent briefs used for the Lean coverage

The coverage was produced by one agent per group of TeX files, each followed by an
independent reviewer agent and a fix pass by the original agent. These are the
briefs, kept for provenance and for the companion phase. `{...}` marks the
per-group parts.

## Coverage agent

> You are working in the git repository /home/yxie/MyProjects/BFGS-nonsmooth/bfgs-nonsmooth: a
> research article on BFGS for nonsmooth optimization (`paper/`), a long companion report
> (`companion/`), and a large Lean 4 formalization (main library
> `bfgs_lean_stage1/BfgsVerification`, article package `bfgs_lean_article`). The overall goal:
> every mathematical claim of the article and the companion is stated by a Lean theorem
> ("literal Lean coverage"). Several agents cover different files at the same time. You handle
> {FILES}.
>
> **Read first.** (1) `editorial/lean_coverage/README.md` — method, statuses, rules and shared
> Lean forms (binding). (2) A finished model, e.g.
> `bfgs_lean_article/BfgsArticle/Coverage/Article/MatrixAlgebra.lean` with
> `register/A_matrix_algebra.json`: docstrings starting ``Item `<id>` (`<file>:<a>-<b>`)``,
> standing assumptions written out, objects introduced by the text as variables with defining
> equations, `_` for unused standing hypotheses, a non-vacuity `example`. (3) Your TeX files in
> full and the context you need ({CONTEXT}). (4) Your registers {REGISTERS} and modules
> {MODULES} (namespace `BfgsCoverage.<Article|Companion>.<Name>`).
>
> **Starting points (verify; not final).** {HINTS: paper ↔ Lean correspondences from
> `TODO_LEAN_REVIEW.md` "Checked and matching", ledger records located in the files, known
> subtleties}.
>
> **Lean workflow.** `export PATH="$HOME/.elan/bin:$PATH"`; from `bfgs_lean_article/`:
> `LEAN_NUM_THREADS=4 lake env lean <module file>` (seconds). At most one Lean process at a
> time; never `lake build`, `lake update`, `lake clean`; scratch files in `/tmp/opencode/{TAG}/`.
> Search names/signatures in `bfgs_lean_stage1/master_report/DECLARATION_INDEX.json`, then read
> the library files. Never `native_decide`.
>
> **Produce.** (1) Modules compiling with no errors, no `sorry`, no forbidden shortcuts; every
> named result exactly as in the TeX; each displayed claim inside a proof under the standing
> assumptions at that point; definitions with unfolding theorems. (2) Registers filled: every
> item a status and its fields; prose items (`kind: "prose"`, `anchor`, `lines`, id
> `<A|C>/<stem>/prose/<nnn>`) for claims outside proofs not in a display or environment (also
> table cells, caption claims, remarks); inside proofs only displayed formulas. (3)
> Discrepancies: false/ambiguous/unprovable as written → `DISCREPANCY` + entry (item,
> description, severity, corrected wording, Lean statement of the corrected claim or a
> counterexample). Never weaken silently. (4) `python3 editorial/lean_coverage/check_coverage.py
> --strict --allow-discrepancies {TEXFILES}` exits 0. Edit no other file; do not commit.
>
> **Final answer.** Counts by status; each declaration with its item(s); discrepancies; items
> not covered; substantial new proofs; check times; notes for other agents.

## Reviewer agent

> You are an independent reviewer of Lean coverage work that another agent did. Be skeptical:
> verify everything yourself. Scope: {TEX FILES, REGISTERS, MODULES, CONTEXT}. Check:
> (1) completeness — every sentence asserting a mathematical fact is itemized;
> (2) LEAN/DEFINITION/OPEN items — the Lean statement equals the TeX claim (hypotheses,
> conclusion, quantifier order, constants, strict vs non-strict, Euclidean vs sup norm, domains,
> vacuity), reading the library definitions used; unfolding theorems match the displayed
> definitions; (3) PART_OF/PROOF/SAME_AS targets really contain or imply the claim;
> (4) NON_CLAIM items assert nothing; (5) each recorded discrepancy, and anything that should be
> one; (6) hygiene (no `sorry`/axioms/`native_decide`/debug options/`unsafe`; imports; docstrings;
> non-vacuity examples). {SPECIFIC POINTS}. You may run Lean (one process at a time, scratch in
> `/tmp/opencode/review_{TAG}/`); edit no repository file. Final answer: counts per category; a
> findings table (item, verdict, problem, fix); confidence and limits.

## Lessons from the article (apply them up front)

- Summaries that drop hypotheses: if false as phrased (a real counterexample), `DISCREPANCY`
  (imprecision); otherwise `SAME_AS` with a note listing the implicit hypotheses. A witness that
  only shows convergence to a different minimizer does not refute a summary.
- `SAME_AS` must not point at a `DISCREPANCY` item; point at the parts that are true.
- "For every run" statements need an exhibited admissible run on that objective (non-vacuity);
  existing runs: `UnexcitedMetric.run` (u²+|v|), the |x| run in `Global.lean` (`absRun`),
  `fourMaxRun` in `Verification.lean`, the quadratic run in `Energy.lean`.
- Statements narrower or wider than the TeX are mismatches: state the paper's version (add a
  specialization when the Lean result is more general).
- Hessian convention: `(∀ᶠ z in 𝓝 x, DifferentiableAt ℝ F z) ∧ DifferentiableAt ℝ (fderiv ℝ F) x`.
- The specified line search is `NonStrictLineSearch.fromMetric` for every trial budget N ≥ 5;
  "the run of the implementation" uses `implemented_run_unique`.
- Coverage modules cannot import each other; small helpers get duplicated under each namespace.
