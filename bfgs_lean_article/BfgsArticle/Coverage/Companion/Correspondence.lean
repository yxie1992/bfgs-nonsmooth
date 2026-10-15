import BfgsArticle.Coverage.Article.Global

/-!
# Lean coverage: `companion/correspondence.tex`

Appendix B of the companion ("Complete correspondence and reproduction", label
`comp:correspondence`), written by hand. Register:
`editorial/lean_coverage/register/C_correspondence.json`.

## Reading

* The sentences about the source release, the frozen baseline, the correspondence records, the
  pinned project and the build tools are `NON_CLAIM`; every commit, path, count and command was
  checked (frozen commit `00362c02…` in `editorial/BASELINE.json`; release `7f53b4c`; 172 source
  spans in `companion/SOURCE_CORRESPONDENCE.json`; the records of the table; `scripts/bootstrap.sh`,
  `editorial/build.sh`, `editorial/vendor/svjour3/`, `paper/figures/`). Stale (step 2): "Source
  transformations preserve the corrected mathematical assertions" (line 62), since the 13 October
  2026 transformations generalize the lower-curvature failures to every admissible pair of
  line-search constants; the table row `SOURCE_CORRESPONDENCE.json` names the file
  `companion/SOURCE_CORRESPONDENCE.json` without its directory.
* Three sentences restate results and are `SAME_AS` the article and chapter items: what the
  article proves (lines 15-17), the companion results outside the article (lines 17-20: Theorems 7.A
  and 7.C, 11.1 and 11.2, the parabolic family of Chapter 10, the lifting theorem, the rates, the
  scalar convergence of Chapter 5), and the constant-Hessian family of Chapter 13 (lines 20-22,
  Theorem `L:thm:global`; the article keeps the same statement as its appendix Proposition
  `art:quadratic_failure`).
* No item needs its own Lean statement. The `example` below shows that the run statements named by
  the summaries of lines 15-20 (coercive homogeneous convergence, the scalar baseline) are not
  vacuous.
-/

noncomputable section
open BfgsVerification

namespace BfgsCoverage.Companion.Correspondence

/-- Non-vacuity for Items `C/correspondence/prose/007` (`companion/correspondence.tex:15-17`) and
`C/correspondence/prose/008` (`companion/correspondence.tex:17-20`): the coercive homogeneous
convergence theorem and the scalar convergence proposition quantify over infinite admissible runs,
and such runs exist, for example on the coercive homogeneous scalar objective $|x|$ (the article's
explicit run `Global.absRun`, $x_k=(-1/2)^k$). -/
example : ∃ (F : Vec 1 → ℝ), (∀ x, F x = |x 0|) ∧ Nonempty (AdmissibleBFGSRun 1 F) :=
  ⟨_, fun _ => rfl, ⟨BfgsCoverage.Article.Global.absRun (fun x : Vec 1 => |x 0|) fun _ => rfl⟩⟩

end BfgsCoverage.Companion.Correspondence
