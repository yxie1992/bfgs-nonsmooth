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

## Statuses

| Status | Meaning | Required fields |
|---|---|---|
| `LEAN` | A coverage theorem states the claim. | `lean`: names; the first is declared in the file's coverage module |
| `DEFINITION` | Defines notation or an object. | `lean`: the Lean definitions, plus a coverage theorem that unfolds them to the displayed formula when they are not literally that formula |
| `PART_OF` | Part of another item's statement (e.g. a display inside a theorem). | `of` |
| `PROOF` | A proof; covered by the Lean proof of item `of`. | `of` |
| `SAME_AS` | Restates or weakens another item (abstract, introduction, summaries). | `of` |
| `OPEN` | An open question, stated in Lean without proof. | `lean` |
| `NON_CLAIM` | Not a mathematical claim. | `reason` |
| `DISCREPANCY` | False or not provable as written. | an entry in `discrepancies` |
| `TODO` | Not yet covered. | `reason` |

Every item may have a `note`. `discrepancies` entries have `item`,
`description`, `severity` (`error`, `imprecision` or `typo`) and, when there is
one, the Lean name of a corrected statement or counterexample.

## Rules for coverage theorems

1. **Same statement.** Same hypotheses, same conclusion, same quantifier order
   and constants as the TeX. A more general Lean theorem is fine as the proof,
   but the coverage theorem states the paper's version. Never weaken a claim to
   make it provable; if it is false or unprovable as written, use `DISCREPANCY`.
2. **Displays inside proofs** are stated under the standing assumptions of the
   proof at that point: the result's hypotheses and the objects and facts the
   proof has introduced before the display.
3. **Docstring.** Each coverage declaration has a docstring with the item id,
   `file:lines`, and the claim in TeX (verbatim, or with notation expanded).
4. **Readable statements.** Write statements with the library's definitions,
   unfolding `...Target` propositions so that the statement can be compared
   with the TeX without chasing definitions.
5. **No shortcuts.** No `sorry`, `admit`, `axiom`, `native_decide`,
   `decide := true` tricks with `Lean.ofReduceBool`, `implemented_by`,
   `@[extern]`, `unsafe`, or `set_option debug.*`.
6. **Imports.** Import library modules (`BfgsVerification...`), the article
   supplements (`MixedBenchmark`, `ArticleBranchRegularity`, `ArticleGeometry`,
   `ConvexBalance`, `negative_scaling`, `OriginalClaimInterpretation`) and
   existing `BfgsArticle.<Module>` files, never the root `BfgsArticle` and never
   another coverage module.
7. **Conventions.** `Vec n := Fin n → ℝ` carries the sup norm; Euclidean
   quantities are explicit (`sqNorm`, `dot`, `euclideanVector`).

## Checking

    export PATH="$HOME/.elan/bin:$PATH"
    cd bfgs_lean_article && LEAN_NUM_THREADS=4 lake env lean BfgsArticle/Coverage/Article/Energy.lean
    python3 editorial/lean_coverage/check_coverage.py paper/sections/energy.tex

`lake build` compiles every coverage module (they are imported by
`BfgsArticle.lean`); the axiom audit includes every Lean name in the registers;
the kernel replay re-checks the coverage modules with lean4checker.
