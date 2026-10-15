# Lean coverage of the article and the companion

Goal: every mathematical claim in the article (`paper/`) and the companion
(`companion/`) is stated by a Lean theorem, checked by Lean, with only the
standard axioms. Agreed scope (author, 14 October 2026):

- **Covered items:** every definition, every named result (theorem, lemma,
  proposition, corollary, also results given as headings or in prose), every
  displayed formula asserted as true (also inside proofs), and every claim in the
  abstract, introduction, remarks, tables and captions.
- **Proofs:** a proof is covered by the Lean proof of its result. Displayed
  claims inside a proof are items of their own. Undisplayed connecting steps are
  left to the line-by-line reading of the proofs.
- **Non-theorem content:** open questions are stated in Lean without proof and
  marked open. Literature results that the documents use are proved in Lean.
  History, motivation, descriptions of software or computer runs, and literature
  that is only mentioned are classified as non-claims, each with a reason.

## Files

- `extract_items.py` finds the mechanical items of every included TeX file:
  theorem-like environments, proofs, displayed formulas, figures, tables, the
  abstract and result headings. `--init` creates or extends the register files.
- `register/<A|C>_<stem>.json`: one register per TeX file (`A` article, `C`
  companion). Each item has an `id`, `kind`, `lines`, `sha256` of its source,
  a `status` and the fields that status needs. Prose claims are added by hand
  with `kind: "prose"`, an `anchor` (a short verbatim quote) and `lines`, and ids
  `<A|C>/<stem>/prose/<nnn>`.
- `check_coverage.py [--strict] [TEX_FILE ...]` validates the registers.
- Lean: `bfgs_lean_article/BfgsArticle/Coverage/Article/<Name>.lean` and
  `.../Coverage/Companion/<Name>.lean`, namespace `BfgsCoverage.Article.<Name>`
  or `BfgsCoverage.Companion.<Name>`. The register field `lean_module` names it.
- `AGENT_BRIEFS.md`: the briefs of the coverage and reviewer agents, and the
  prompts of the companion groups.
- `companion_hints.py` writes `hints/<stem>.json` (git-ignored): for each
  companion file, its claim-ledger records with their Lean exports.
- `pause_notes/<group>.md`: the reading notes and item plans of the companion
  agents paused on 14 October 2026 (see `HANDOFF.md`).

## Statuses

| Status | Meaning | Required fields |
|---|---|---|
| `LEAN` | A coverage theorem states the claim. | `lean`: names; the first is declared in the file's coverage module |
| `DEFINITION` | Defines notation or an object. | `lean`: the Lean definitions, plus a coverage theorem that unfolds them to the displayed formula when they are not literally that formula |
| `PART_OF` | Part of another item's statement (e.g. a display inside a theorem). | `of` |
| `PROOF` | A proof; covered by the Lean proof of item `of`. | `of` |
| `SAME_AS` | Restates or weakens another item, or combines several (abstract, introduction, summaries). | `of`: an item id or a list of ids |
| `OPEN` | An open question, stated in Lean without proof. | `lean` |
| `NON_CLAIM` | Not a mathematical claim. | `reason` |
| `DISCREPANCY` | False or not provable as written. | an entry in `discrepancies` |
| `TODO` | Not yet covered. | `reason` |

Every item may have a `note`. `discrepancies` entries have `item`,
`description`, `severity` (`error`, `imprecision` or `typo`) and, when there is
one, the Lean name of a corrected statement or counterexample.

## Rules for coverage theorems

The finished pilot, `bfgs_lean_article/BfgsArticle/Coverage/Article/MatrixAlgebra.lean`
with `register/A_matrix_algebra.json`, is the model to follow.

1. **Same statement.** Same hypotheses, same conclusion, same quantifier order
   and constants as the TeX. A more general Lean theorem is fine as the proof,
   but the coverage theorem states the paper's version. Never weaken a claim to
   make it provable; if it is false or unprovable as written, use `DISCREPANCY`.
2. **Displays inside proofs** are stated under the standing assumptions of the
   proof at that point: the result's hypotheses and the objects and facts the
   proof has introduced before the display. Objects that the text introduces
   ("put $v=Hg$") are variables with their defining equation as a hypothesis,
   `(v : Vec n) (hv : v = H *ᵥ g)`; inside a proof, introduce them with
   `obtain ⟨v, hv⟩ : ∃ v, v = H *ᵥ g := ⟨_, rfl⟩`. A display that both defines
   notation and asserts something (e.g. "$A=Z^THZ\succ0$") is `LEAN` for the
   assertion, with a `note` on the definitions. Standing hypotheses that a proof
   does not use get names starting with `_` (do not disable the linter).
3. **Docstring.** Each coverage declaration has a docstring that starts with
   ``Item `<id>` (`<tex file>:<first>-<last>`)`` (the checker compares these
   lines with the register) and gives the claim in TeX, verbatim or with notation
   expanded.
4. **Readable statements.** Write statements with the library's definitions,
   unfolding `...Target` propositions so that the statement can be compared
   with the TeX without chasing definitions. Use the shared forms below, so that
   the same hypothesis reads the same in every file.
5. **No shortcuts.** No `sorry`, `admit`, `axiom`, `native_decide`,
   `decide := true` tricks with `Lean.ofReduceBool`, `implemented_by`,
   `@[extern]`, `unsafe`, or `set_option debug.*`.
6. **Imports.** Import library modules (`BfgsVerification...`), the article
   supplements (`MixedBenchmark`, `ArticleBranchRegularity`, `ArticleGeometry`,
   `ConvexBalance`, `negative_scaling`, `OriginalClaimInterpretation`) and
   existing `BfgsArticle.<Module>` files, never the root `BfgsArticle`. An article
   coverage module imports no other coverage module. A companion coverage module
   may import the article coverage modules (`BfgsArticle.Coverage.Article.*`,
   complete since 14 October 2026), never another companion coverage module.
7. **Conventions.** `Vec n := Fin n → ℝ` carries the sup norm; Euclidean
   quantities are explicit (`sqNorm`, `dot`, `euclideanVector`).
8. **Non-vacuity.** Each module with standing assumptions ends with an `example`
   showing that they can all hold at once.
9. **Proof steps.** Undisplayed steps of a proof need no item. Theorems that state
   them anyway may be listed in the `lean` field of the `PROOF` item; every
   `lean` name of every item is checked by the axiom audit.

## Shared Lean forms

| Paper | Lean |
|---|---|
| $H\succ0$ | `H.PosDef` |
| $s=-\alpha Hg$ | `s = -α • (H *ᵥ g)` (definitionally `bfgsStep H g α`) |
| the inverse update `art:update` | `inverseBFGS H s y` |
| $q=g^THg$, $\beta$ of `art:minor-hierarchy` | variables with `q = dot g (H *ᵥ g)`, `β = -dot y (H *ᵥ g) / q` |
| $Z$ with $j$ orthonormal columns | `Z : Matrix (Fin n) (Fin j) ℝ`, `Zᵀ * Z = 1` |
| $\operatorname{Gram}_H(y,Z)$ | `metricGram H (fromCols (replicateCol Unit y) Z)` |
| $[a\ b]$ | `(Matrix.of ![a, b])ᵀ` |
| an admissible run (Definition `art:admissible`) | `AdmissibleBFGSRun` (see the energy module once written) |

## Finding declarations

Search the names in `bfgs_lean_stage1/master_report/DECLARATION_INDEX.json`
(each entry has `signature`, `module`, `source_path`, `source_range`) and read the
matching library files; this is faster than the claim ledger, whose export lists
are coarse unions.

## Checking

    export PATH="$HOME/.elan/bin:$PATH"
    cd bfgs_lean_article && LEAN_NUM_THREADS=4 lake env lean BfgsArticle/Coverage/Article/Energy.lean
    python3 editorial/lean_coverage/check_coverage.py paper/sections/energy.tex

Checking a module takes seconds once the library is built (loading even
`import BfgsVerification` takes about 3 s). Never run `lake build`, `lake update`
or `lake clean` while other agents work in the package. A recorded
`DISCREPANCY` stays open until the manuscript is corrected, so while it is open
use `check_coverage.py --strict --allow-discrepancies`.

`lake build` compiles every coverage module (they are imported by
`BfgsArticle.lean`); the axiom audit includes every Lean name in the registers;
the kernel replay re-checks the coverage modules with lean4checker.
