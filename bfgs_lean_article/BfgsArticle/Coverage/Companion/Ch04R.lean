import BfgsArticle.Coverage.Article.Global
import BfgsArticle.Coverage.Article.Local
import BfgsVerification.RadialCentralDifference
import BfgsVerification.RadialNormConvention
import BfgsVerification.ReconstructedFourPieceTargets
import BfgsVerification.FirstDifferencePenalty
import BfgsVerification.AffineKinkCells
import BfgsVerification.FiniteMaxRadialSufficiency
import BfgsVerification.FiniteMaxCentralAsymptotic
import BfgsVerification.FiniteMaxRadialObstruction
import BfgsVerification.ParabolicRadialBoundary
import BfgsVerification.CenteredNuclear
import BfgsVerification.CenteredRectangularNuclear
import BfgsVerification.PoweredGaugeProfiles
import BfgsVerification.CellDerivativeMatching
import BfgsVerification.RunShift
import BfgsVerification.AffineWhiteningGeometry
import OriginalClaimInterpretation
import BfgsArticle.AdmissibleRunExistence

/-!
# Lean coverage: `companion/chapters/04_R.tex`

Chapter R of the companion report ("Radial modeling and finite partitions"): the radial secant
condition (RS), its equivalent inward form (IR) (Theorem `R:thm:equiv`) with both proofs, the
derivative-free central form, the optimizer-intercept form (SP) and homogeneous intercepts, the
reconstructed four-piece realization, finite polyhedral partitions (Theorem `R:thm:plq`), the
common families of Section 4.6, the parabolic ridge and the spectral example of Section 4.7, and
the relation to earlier work. Register: `editorial/lean_coverage/register/C_04_R.json`.

## Standing assumptions

The setting of lines 30-36 is written out in every theorem that uses it:

* `hF : ConvexOn ℝ univ F` with `F : Vec n → ℝ` is "$F$ finite and convex";
* `xstar` with `hmin : ∀ x, F xstar ≤ F x` is the minimizer $x_*$, and $F_*$ is `F xstar`;
* `b` with `hb : F xstar < b`, and `K` with `hK_def : K = {x | F x ≤ b}` and
  `hK : IsCompact K`, is the compact sublevel $K=\{F\le b\}$, $b>F_*$;
* the bounds of display `disp/002` are `R G` with `hR : 0 < R`, `hG : 0 < G`,
  `hRK : ∀ x ∈ K, ‖euclideanVector (x - xstar)‖ ≤ R` and `hGK` (every subgradient $v$ at a point
  of $K$, i.e. `∀ y, F x + dot v (y - x) ≤ F y`, has `‖euclideanVector v‖ ≤ G`).

The displays of the proof of Theorem `R:thm:equiv` add the hypotheses described before each
group (a band `η` with its constants, the pair or the inward point, and the variables $T$, $N$,
$a$, $D_F$, $\theta_\eta$ with their defining equations). Objects introduced by the text
($\delta$, $a$, $\mathcal L$ of the four-piece realization, $\psi$, $\gamma_j$, $A_j$, the cells
$P_i$ and extensions $f_i$, the example objectives) are variables with their defining equations
as hypotheses. A hypothesis whose name starts with `_` is a standing assumption that the Lean
proof does not use.

## Notation and readings

* A gradient $g=\nabla F(x)$ at a differentiable point is `HasFDerivAt F (gradientFunctional g) x`
  (`gradientFunctional g v = dot g v`); $r_x$ is `x - xstar`; $T(x,z)=y^Ts$ and $N(x,z)=y^Tr_z$
  are `dot (h - g) (z - x)` and `dot (h - g) (z - xstar)`; $D_F(z,x)$ is
  `F z - F x - dot g (z - x)` (the library's `RadialCertificate.supportingError`) and $b_F(x)$
  is `dot g (x - xstar) - (F x - F xstar)` (`RadialCertificate.optimizerIntercept`).
* `Vec n` carries the sup norm; Euclidean norms are explicit (`‖euclideanVector v‖`).
* (RS), (IR), the central bound of display `disp/022` and (SP) are the definitions `RS`, `IR`,
  `Central` and `SP`, with real constants. Since 15 October 2026 (wording point W19) the chapter
  states (RS) and (IR) with "$C_\eta\ge0$" and "$M_\eta\ge0$", as the article does: these are
  `RSNonneg` and `IRNonneg`, equivalent to `RS` and `IR` (`RSNonneg_iff`, `IRNonneg_iff`; a
  constant can be replaced by its positive part), and Theorem `R:thm:equiv` in that form is
  `equiv_nonneg`. `RS_iff_article` and `IR_iff_article` show that they are the article's
  conditions; `*_iff_library` relate them to the library's predicates. `rs_constant_nonneg` shows
  that an (RS) constant is automatically nonnegative on bands that contain a point strictly between
  the band threshold and $b$; the coverage theorems of the degenerate cases $a=0$ (line 149) and
  $a_\pm=0$ (display `disp/023`) use it, so they hold for every real (RS) constant.
* "Homogeneous of degree $p$" is `∀ t ≥ 0, ∀ x, F (t • x) = t ^ p * F x` with the real power
  (`InterceptExamples.PositiveDegree`); "sublinear" (gauge) is `Sublinear` (convex and positively
  homogeneous of degree one).
* "Smooth" losses and summands are read as convex and locally $C^{1,1}$
  (`CenteredSmoothSublinear.LocallyC11On univ ψ`), as in the proof of Theorem `R:thm:plq`
  (lines 300-307 call its $C^{1,1}$ extensions "smooth") and in the article's parallel results;
  this includes $C^{1,1}$, $C^2$ (`locallyC11_of_contDiff_two`) and $C^\infty$ functions. The
  strictness claim of line 309 is proved for both readings: `plq_broader_2d` excludes every
  differentiable summand, `plq_broader` (dimension one) every $C^2$ summand. "$C^{1,1}$
  extension" in Theorem `R:thm:plq` is
  `DifferentiableOn ℝ f V ∧ ∃ L, LipschitzOnWith L (fderiv ℝ f) V` on an open $V$ (the locally
  $C^{1,1}$ form is `plq_theorem_local`); "a neighborhood of $x_*$" is `N ∈ 𝓝 xstar`.
* An admissible full-BFGS run is `AdmissibleBFGSRun n F` (arbitrary $H_0\succ0$, fixed
  $0<c_1<c_2<1$); "every sufficiently low-starting run" is
  `∃ ε, 0 < ε ∧ ∀ run, F (run.x 0) ≤ F xstar + ε → ...`, with $\varepsilon$ chosen before the
  run.

## Items

| Item | Lines | Lean |
|---|---|---|
| `disp/002` | 35-37 | `bounds_exist` |
| `disp/003` | 41-44 | `secant_notation` (notation) |
| `disp/004`, `disp/005` | 46-52 | `supporting_error_nonneg`, `curvature_split` |
| prose `006`, `disp/006` (RS) | 53-59 | `RSNonneg`, `RS` (line 53 names it "the radial secant condition" since 15 October 2026, wording point W8) |
| `theorem/R:thm:equiv` with `disp/007` (IR) | 73-82 | `equiv_nonneg`, `equiv`, `IRNonneg`, `IR` |
| `disp/008`, `disp/009` | 91-97 | `inward_probe_at_z`, `swap_identity` |
| `disp/010`, `disp/011` | 99-105 | `inward_probe_at_x`, `inward_probe_common` |
| `disp/012`, `disp/013` | 107-115 | `inward_probe_large_case`, `inward_to_radial` |
| `disp/014` to `disp/016` | 124-134 | `theta_choice`, `inner_band`, `a_nonneg` |
| `disp/017`, `disp/018` | 136-144 | `pair_identities`, `a_bound` |
| `disp/019` | 146-148 | `error_bound_pos`, `error_bound_zero` |
| `disp/020` | 159-161 | `profile` (definition) |
| `disp/022`, `disp/023` | 169-176 | `central_equivalence`, `radial_pair_bounds` |
| `disp/024` to `disp/026` (SP) | 189-204 | `intercept_def`, `radial_numerator_intercepts`, `SP` |
| `disp/028`, `disp/029` | 214-223 | `degree_intercept_at_reference`, `midpoint_bound` |
| `disp/030` | 227-229 | `compact_homogeneous_intercept` |
| `disp/031`, `disp/032` | 234-241 | `fourPiece_FD`, `fourPiece_constants` |
| `disp/033` | 243-245 | `fourPiece_objective_formula` |
| `disp/034`, `disp/035` | 247-258 | `fourPiece_branches`, `fourPiece_branch_values` |
| `disp/037`, `disp/038` | 266-280 | `fourPiece_transformed_data`, `fourPiece_band` |
| `theorem/R:thm:plq` with `disp/039` | 292-298 | `plq_theorem`, `plq_theorem_local` |
| `proof/001` with `disp/040` | 299-308 | `plq_gradient_agreement`, `plq_inward_taylor` |
| `disp/041`, `disp/042` | 329-337 | `sublinear_radial`, `powered_radial` |
| `disp/043` | 339-341 | `mixed_powers_covered` |
| `disp/044` | 364-367 | `finite_max_branch_test` |
| `disp/045` to `disp/047` | 387-399 | `parabolic_objective`, `parabolic_pair`, `parabolic_ratio` |
| `disp/048`, `disp/049` | 409-418 | `spectral_objective`, `spectral_vectors` |
| `disp/050`, `disp/051` | 420-428 | `spectral_pair_form`, `spectral_ratio` |

`disp/001` (the setting) is not a claim; `disp/021` is the article's `A/global/prose/017`;
`disp/027` and `disp/036` are parts of the claims that use them. The claims of the text (prose
items) are covered by the theorems whose docstrings cite them, from `locally_lipschitz_bound`
(`prose/004`) to `svt_specialization` (`prose/106`); the register lists them all. Undisplayed
steps of proofs are stated where useful (`inward_probe_small_case`, `ir_with_eight_C`,
`central_le_five`, `plq_gradient_agreement`).

## Non-vacuity

The examples at the end show that the standing assumptions can hold: the setting with the
displays of both proofs of Theorem `R:thm:equiv` (both cases $N\ge0$, $N<0$ and $a>0$, $a=0$)
and display `disp/023`, on the benchmark $F(u,v)=u^2+|v|$; Theorem `R:thm:plq` with display
`disp/040`, on $|x|$ with two cells; display `disp/043`; the polyhedral-loss and
Euclidean-residual theorems of Sections 4.6.2-4.6.3 (on the benchmark) and the fused
$\ell_1$ theorem (on the benchmark composed with an invertible linear map); display `disp/044`
(on $|x|=\max\{x,-x\}$); the homogeneous-intercept statements (on $|x|$); `plq_covered_objective`,
`plq_covered_loss` (the loss $0$ plus the piecewise quadratic example of
`plq_hessians_and_jumps`) and `smooth_plus_polyhedral_covered` (the benchmark as
$u^2+\max\{v,-v\}$); `centered_nuclear_smooth_covered` (with $\psi=0$); `gauge_sublinear` (an
asymmetric interval); and the four-piece parameters. `plq_hessians_and_jumps` and `plq2d_covered`
are themselves instances of the hypotheses of Theorem `R:thm:plq`, and the four-piece and
spectral statements are about fixed objects.

Statements about every (sufficiently low-starting) admissible run are shown non-vacuous by
explicit runs. For every $\varepsilon>0$, tails (`AdmissibleBFGSRun.shift`, `exists_low_run`)
starting below $F_*+\varepsilon$ exist for the library's `UnexcitedMetric.run` on the benchmark
(`benchRun`), its whitened copy `AffineWhitening.run`, `Article.Global.absRun` on $|x|$, and
`plq_example_run` (built by `Article.Global.oneDimRun` inside the cell $[0,1]$) on
$F(x)=x^2+\max\{x,0\}^2+|x-1|$ of `plq_hessians_and_jumps` and `plq_broader`; on the
two-dimensional witness $u^2+v^2+(2+|u|)|v|$ of `plq_broader_2d`, low-starting runs exist by the
general existence theorem (`plq2d_low_runs`). `benchRun`
starts in the sublevel of `mixed_powers_covered`; `absRun` is also a run on the Euclidean norm of
$\R^1$ (`euclidean_norm_recovered`); `fourPiece_failure_run` exhibits its own run; and admissible
runs on the nuclear norm of `centered_nuclear_covered` (and of `centered_nuclear_smooth_covered`
with $\psi=0$) exist by the general existence theorem
`AdmissibleRunExistence.exists_admissible_run` (`nuclear_run_exists`, with
`nuclear_differentiableAt`, `nuclear_not_differentiableAt`, `nuclear_line_countable` and
`nuclear_gradient_ne_zero`).
-/

noncomputable section
open scoped Topology
open Set Filter Matrix BfgsVerification

namespace BfgsCoverage.Companion.Ch04R

/-! ### The conditions of the chapter -/

/-- Item `C/04_R/disp/006` (`companion/chapters/04_R.tex:54-59`), the radial secant condition
(RS) with real constants, as printed before 15 October 2026:
\[ \forall\eta>0\ \exists C_\eta<\infty:\quad N(x,z)^2\le C_\eta T(x,z)\quad\text{if }
F_*+\eta\le F(z)\le F(x),\ x,z\in K,\ T>0, \]
for differentiable endpoints $x,z$ (line 60) with gradients $g,h$, $T=(h-g)^T(z-x)$,
$N=(h-g)^T(z-x_*)$. The display now states $C_\eta\ge0$ (wording point W19): that is `RSNonneg`,
equivalent to this definition (`RSNonneg_iff`) and to the article's condition with $C_\eta\ge0$
(`RS_iff_article`). The coverage theorems of the chapter use this form. -/
def RS {n : ℕ} (F : Vec n → ℝ) (xstar : Vec n) (K : Set (Vec n)) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ C : ℝ,
    ∀ x z g h : Vec n, x ∈ K → z ∈ K →
      HasFDerivAt F (gradientFunctional g) x → HasFDerivAt F (gradientFunctional h) z →
      F xstar + η ≤ F z → F z ≤ F x → 0 < dot (h - g) (z - x) →
      (dot (h - g) (z - xstar)) ^ 2 ≤ C * dot (h - g) (z - x)

/-- Item `C/04_R/disp/007` (`companion/chapters/04_R.tex:75-80`), inward radial smoothness (IR)
with real constants, as printed before 15 October 2026: "For every $\eta>0$, there exist
$M_\eta<\infty$ and $\theta_\eta\in(0,1/2]$ such that, at every differentiable $x\in K$ with
$F(x)\ge F_*+\eta$,
\[ 0\le F(x-tr_x)-F(x)+t\nabla F(x)^Tr_x\le\frac{M_\eta}2t^2,\qquad0\le t\le\theta_\eta." \]
The theorem now states $M_\eta\ge0$ (wording point W19): that is `IRNonneg`, equivalent to this
definition (`IRNonneg_iff`) and to the article's condition with $M_\eta\ge0$ (`IR_iff_article`). -/
def IR {n : ℕ} (F : Vec n → ℝ) (xstar : Vec n) (K : Set (Vec n)) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ M θ : ℝ, 0 < θ ∧ θ ≤ 1 / 2 ∧
    ∀ x g : Vec n, x ∈ K → HasFDerivAt F (gradientFunctional g) x → F xstar + η ≤ F x →
      ∀ t : ℝ, 0 ≤ t → t ≤ θ →
        0 ≤ F (x - t • (x - xstar)) - F x + t * dot g (x - xstar) ∧
          F (x - t • (x - xstar)) - F x + t * dot g (x - xstar) ≤ M / 2 * t ^ 2

/-- Item `C/04_R/disp/006` (`companion/chapters/04_R.tex:54-59`), the radial secant condition (RS)
as printed since 15 October 2026 (wording point W19; before "$\exists C_\eta<\infty$"):
\[ \forall\eta>0\ \exists C_\eta\ge0:\quad N(x,z)^2\le C_\eta T(x,z)\quad\text{if }
F_*+\eta\le F(z)\le F(x),\ x,z\in K,\ T>0, \]
for differentiable endpoints $x,z$ (line 60) with gradients $g,h$, $T=(h-g)^T(z-x)$,
$N=(h-g)^T(z-x_*)$. Item `C/04_R/prose/006` (`companion/chapters/04_R.tex:53`) names it: "The
radial secant condition is the following positive-band condition:" (since 15 October 2026,
wording point W8; before "The preceding report assumes the following positive-band
condition:"). -/
def RSNonneg {n : ℕ} (F : Vec n → ℝ) (xstar : Vec n) (K : Set (Vec n)) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧
    ∀ x z g h : Vec n, x ∈ K → z ∈ K →
      HasFDerivAt F (gradientFunctional g) x → HasFDerivAt F (gradientFunctional h) z →
      F xstar + η ≤ F z → F z ≤ F x → 0 < dot (h - g) (z - x) →
      (dot (h - g) (z - xstar)) ^ 2 ≤ C * dot (h - g) (z - x)

/-- Item `C/04_R/disp/007` (`companion/chapters/04_R.tex:75-80`), inward radial smoothness (IR) as
printed since 15 October 2026 (wording point W19; before "$M_\eta<\infty$"): "For every
$\eta>0$, there exist $M_\eta\ge0$ and $\theta_\eta\in(0,1/2]$ such that, at every differentiable
$x\in K$ with $F(x)\ge F_*+\eta$,
\[ 0\le F(x-tr_x)-F(x)+t\nabla F(x)^Tr_x\le\frac{M_\eta}2t^2,\qquad0\le t\le\theta_\eta." \] -/
def IRNonneg {n : ℕ} (F : Vec n → ℝ) (xstar : Vec n) (K : Set (Vec n)) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ M θ : ℝ, 0 ≤ M ∧ 0 < θ ∧ θ ≤ 1 / 2 ∧
    ∀ x g : Vec n, x ∈ K → HasFDerivAt F (gradientFunctional g) x → F xstar + η ≤ F x →
      ∀ t : ℝ, 0 ≤ t → t ≤ θ →
        0 ≤ F (x - t • (x - xstar)) - F x + t * dot g (x - xstar) ∧
          F (x - t • (x - xstar)) - F x + t * dot g (x - xstar) ≤ M / 2 * t ^ 2

/-- (RS) with nonnegative constants is (RS) with real constants: a constant can be replaced by
$\max(C_\eta,0)$. -/
theorem RSNonneg_iff {n : ℕ} (F : Vec n → ℝ) (xstar : Vec n) (K : Set (Vec n)) :
    RSNonneg F xstar K ↔ RS F xstar K := by
  constructor
  · intro hR η hη
    obtain ⟨C, -, hC⟩ := hR η hη
    exact ⟨C, hC⟩
  · intro hR η hη
    obtain ⟨C, hC⟩ := hR η hη
    refine ⟨max C 0, le_max_right _ _, fun x z g k hx hz hg hk h1 h2 hT => ?_⟩
    exact (hC x z g k hx hz hg hk h1 h2 hT).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hT.le)

/-- (IR) with nonnegative constants is (IR) with real constants: a constant can be replaced by
$\max(M_\eta,0)$. -/
theorem IRNonneg_iff {n : ℕ} (F : Vec n → ℝ) (xstar : Vec n) (K : Set (Vec n)) :
    IRNonneg F xstar K ↔ IR F xstar K := by
  constructor
  · intro hI η hη
    obtain ⟨M, θ, -, hθ, hθ', hM⟩ := hI η hη
    exact ⟨M, θ, hθ, hθ', hM⟩
  · intro hI η hη
    obtain ⟨M, θ, hθ, hθ', hM⟩ := hI η hη
    refine ⟨max M 0, θ, le_max_right _ _, hθ, hθ', fun x g hx hg hb t h0 h1 => ?_⟩
    obtain ⟨hlo, hup⟩ := hM x g hx hg hb t h0 h1
    exact ⟨hlo, hup.trans (mul_le_mul_of_nonneg_right (by linarith [le_max_left M 0])
      (sq_nonneg t))⟩

theorem RS_iff_library {n : ℕ} (F : Vec n → ℝ) (xstar : Vec n) (K : Set (Vec n)) :
    RS F xstar K ↔ RadialCertificate.HasRadialSecantBounds F K xstar := by
  constructor
  · intro h η hη
    obtain ⟨C, hC⟩ := h η hη
    exact ⟨C, fun x z g h hx hz hb ho hg hh ht => hC x z g h hx hz hg hh hb ho ht⟩
  · intro h η hη
    obtain ⟨C, hC⟩ := h η hη
    exact ⟨C, fun x z g h hx hz hg hh hb ho ht => hC x z g h hx hz hb ho hg hh ht⟩

theorem IR_iff_library {n : ℕ} (F : Vec n → ℝ) (xstar : Vec n) (K : Set (Vec n)) :
    IR F xstar K ↔ RadialCertificate.HasInwardTaylorBounds F K xstar := by
  constructor
  · intro h η hη
    obtain ⟨M, θ, hθ, hθ', hM⟩ := h η hη
    refine ⟨M, θ, hθ, hθ', fun x g hx hb hg t h0 h1 => ?_⟩
    rw [RadialCertificate.inward_error_eq]
    exact hM x g hx hg hb t h0 h1
  · intro h η hη
    obtain ⟨M, θ, hθ, hθ', hM⟩ := h η hη
    refine ⟨M, θ, hθ, hθ', fun x g hx hg hb t h0 h1 => ?_⟩
    have h' := hM x g hx hb hg t h0 h1
    rw [RadialCertificate.inward_error_eq] at h'
    exact h'


/-- (RS) is the article's radial secant condition `art:radial-condition`, whose constants are
nonnegative: a constant can be replaced by $\max(C_\eta,0)$. -/
theorem RS_iff_article {n : ℕ} (F : Vec n → ℝ) (xstar : Vec n) (K : Set (Vec n)) :
    RS F xstar K ↔ Article.Global.RadialSecantCondition F xstar K :=
  (RS_iff_library F xstar K).trans (Article.Global.radialSecantCondition_iff F xstar K).symm

/-- (IR) is the article's inward model condition `art:inward-condition`, whose constants are
nonnegative: a constant can be replaced by $\max(M_\eta,0)$. -/
theorem IR_iff_article {n : ℕ} (F : Vec n → ℝ) (xstar : Vec n) (K : Set (Vec n)) :
    IR F xstar K ↔ Article.Global.InwardModelCondition F xstar K :=
  (IR_iff_library F xstar K).trans (Article.Global.inwardModelCondition_iff F xstar K).symm

/-! ### Helpers -/

theorem dot_swap_neg {n : ℕ} (a b x y : Vec n) : dot (a - b) (x - y) = dot (b - a) (y - x) := by
  unfold dot
  exact Finset.sum_congr rfl (fun i _ => by simp only [Pi.sub_apply]; ring)

theorem dot_swap_neg' {n : ℕ} (g x y : Vec n) : dot g (x - y) = -dot g (y - x) := by
  unfold dot
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun i _ => by simp only [Pi.sub_apply]; ring)

/-- Along a segment toward a minimizer, convexity lowers the value strictly once the endpoint
lies above the minimum. -/
theorem inward_lt {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F) (xstar y : Vec n)
    (hy : F xstar < F y) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    F (y - t • (y - xstar)) < F y := by
  have he : y - t • (y - xstar) = (1 - t) • y + t • xstar := by module
  have hc := hF.2 (mem_univ y) (mem_univ xstar) (by linarith) ht0.le (by ring : (1 - t) + t = 1)
  rw [he]
  simp only [smul_eq_mul] at hc
  nlinarith

/-- Uniqueness of the gradient at a differentiable point. -/
theorem gradient_unique {n : ℕ} {F : Vec n → ℝ} {x g h : Vec n}
    (hg : HasFDerivAt F (gradientFunctional g) x) (hh : HasFDerivAt F (gradientFunctional h) x) :
    g = h := by
  have he : gradientFunctional g = gradientFunctional h := hg.unique hh
  ext i
  have := congrArg (fun l : Vec n →L[ℝ] ℝ => l (Pi.single i 1)) he
  simpa [gradientFunctional_apply, dot, Pi.single_apply] using this

/-- The Euclidean gradient bound of the setting applies to every gradient at a point of $K$. -/
theorem gradient_bound {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F) {K : Set (Vec n)}
    {G : ℝ} (hGK : ∀ x ∈ K, ∀ v : Vec n, (∀ y, F x + dot v (y - x) ≤ F y) →
      ‖euclideanVector v‖ ≤ G) {x g : Vec n} (hx : x ∈ K)
    (hg : HasFDerivAt F (gradientFunctional g) x) : sqNorm g ≤ G ^ 2 :=
  Article.Global.sqNorm_le_of_norm_le (hGK x hx g (fun y => by
    linarith [convex_supporting_inequality hF hg y]))

/-- **Nonnegativity of (RS) constants.** If $C$ is a constant of (RS) for the band $\eta>0$ on the
compact sublevel $K=\{F\le b\}$, and the band contains a point $w$ strictly between its
threshold and $b$, then $C\ge0$: the band then contains a differentiable pair on opposite
sides of $x_*$ with positive curvature $T$, and $N^2\le CT$ forces $C\ge0$. -/
theorem rs_constant_nonneg {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F) (xstar : Vec n)
    (b : ℝ) (K : Set (Vec n)) (hK_def : K = {x | F x ≤ b}) (hK : IsCompact K)
    (η C : ℝ) (hη : 0 < η)
    (hC : ∀ x z g h : Vec n, x ∈ K → z ∈ K →
      HasFDerivAt F (gradientFunctional g) x → HasFDerivAt F (gradientFunctional h) z →
      F xstar + η ≤ F z → F z ≤ F x → 0 < dot (h - g) (z - x) →
      (dot (h - g) (z - xstar)) ^ 2 ≤ C * dot (h - g) (z - x))
    (w : Vec n) (hw1 : F xstar + η < F w) (hw2 : F w < b) : 0 ≤ C := by
  have hc := convex_continuous hF
  set r := w - xstar with hr
  have hr0 : r ≠ 0 := by
    intro h0
    have hw : w = xstar := sub_eq_zero.mp h0
    rw [hw] at hw1
    linarith
  obtain ⟨Mb, hMb⟩ := hK.isBounded.exists_norm_le
  have hrpos : 0 < ‖r‖ := norm_pos_iff.mpr hr0
  set Λ := (|Mb| + ‖xstar‖ + 1) / ‖r‖ with hΛ
  have hΛpos : 0 < Λ := by positivity
  have hout : b < F (xstar - Λ • r) := by
    by_contra hle
    push_neg at hle
    have hmem : xstar - Λ • r ∈ K := by rw [hK_def]; exact hle
    have h1 := hMb _ hmem
    have h2 : Λ * ‖r‖ = |Mb| + ‖xstar‖ + 1 := by rw [hΛ]; field_simp
    have h3 : ‖Λ • r‖ ≤ ‖xstar‖ + ‖xstar - Λ • r‖ := by
      calc ‖Λ • r‖ = ‖xstar - (xstar - Λ • r)‖ := by congr 1; abel
        _ ≤ ‖xstar‖ + ‖xstar - Λ • r‖ := norm_sub_le _ _
    rw [norm_smul, Real.norm_of_nonneg hΛpos.le] at h3
    linarith [le_abs_self Mb]
  have hφc : ContinuousOn (fun s : ℝ => F (xstar - s • r)) (Icc 0 Λ) :=
    (hc.comp (continuous_const.sub (continuous_id.smul continuous_const))).continuousOn
  have hmemI : F w ∈ Icc (F (xstar - (0 : ℝ) • r)) (F (xstar - Λ • r)) := by
    simp only [zero_smul, sub_zero]
    constructor <;> linarith
  obtain ⟨s0, hs0I, hs0⟩ := intermediate_value_Icc hΛpos.le hφc hmemI
  have hs0pos : 0 < s0 := by
    rcases eq_or_lt_of_le hs0I.1 with h | h
    · rw [← h] at hs0
      simp only [zero_smul, sub_zero] at hs0
      linarith
    · exact h
  set q := xstar - s0 • r with hq
  have hFq : F q = F w := hs0
  set σ := s0 / (1 + s0) with hσ
  have hσ0 : 0 < σ := by positivity
  have hσ1 : σ < 1 := by rw [hσ, div_lt_one (by linarith)]; linarith
  have h1σ : (1 - σ) * s0 = σ := by rw [hσ]; field_simp
  have hm : σ • w + (1 - σ) • q = xstar := by
    calc σ • w + (1 - σ) • q = σ • w + (1 - σ) • xstar - ((1 - σ) * s0) • (w - xstar) := by
          rw [hq, hr]; module
      _ = σ • w + (1 - σ) • xstar - σ • (w - xstar) := by rw [h1σ]
      _ = xstar := by module
  have hcm : ∀ y : Vec n, Continuous (fun x : Vec n => F (σ • x + (1 - σ) • y)) := fun y =>
    hc.comp ((continuous_id.const_smul σ).add continuous_const)
  have hcm' : ∀ x : Vec n, Continuous (fun y : Vec n => F (σ • x + (1 - σ) • y)) := fun x =>
    hc.comp (continuous_const.add (continuous_id.const_smul (1 - σ)))
  have hD : Dense {x : Vec n | DifferentiableAt ℝ F x} :=
    MeasureTheory.Measure.dense_of_ae (convex_ae_differentiable hF)
  set O1 := {x : Vec n | F xstar + η < F x ∧ F x < b ∧ F (σ • x + (1 - σ) • q) < F xstar + η}
    with hO1
  have hO1o : IsOpen O1 :=
    (isOpen_lt continuous_const hc).inter ((isOpen_lt hc continuous_const).inter
      (isOpen_lt (hcm q) continuous_const))
  have hwO1 : w ∈ O1 := ⟨hw1, hw2, by rw [hm]; linarith⟩
  obtain ⟨x', hx'D, hx'O⟩ := hD.exists_mem_open hO1o ⟨w, hwO1⟩
  set O2 := {y : Vec n | F xstar + η < F y ∧ F y < b ∧ F (σ • x' + (1 - σ) • y) < F xstar + η}
    with hO2
  have hO2o : IsOpen O2 :=
    (isOpen_lt continuous_const hc).inter ((isOpen_lt hc continuous_const).inter
      (isOpen_lt (hcm' x') continuous_const))
  have hqO2 : q ∈ O2 := ⟨by rw [hFq]; exact hw1, by rw [hFq]; exact hw2, hx'O.2.2⟩
  obtain ⟨z', hz'D, hz'O⟩ := hD.exists_mem_open hO2o ⟨q, hqO2⟩
  have hg' := hasFDerivAt_coordinateGradient (show DifferentiableAt ℝ F x' from hx'D)
  have hh' := hasFDerivAt_coordinateGradient (show DifferentiableAt ℝ F z' from hz'D)
  set g' := coordinateGradient F x'
  set h' := coordinateGradient F z'
  have hx'K : x' ∈ K := by rw [hK_def]; exact hx'O.2.1.le
  have hz'K : z' ∈ K := by rw [hK_def]; exact hz'O.2.1.le
  -- positive curvature
  have hT : 0 < dot (h' - g') (z' - x') := by
    refine lt_of_not_ge (fun hT => ?_)
    have hsplit := RadialCertificate.secantCurvature_eq_errors F x' z' g' h'
    have hD2 := RadialCertificate.supportingError_nonneg hF hh' x'
    unfold RadialCertificate.secantCurvature RadialCertificate.supportingError at hsplit hD2
    have hsupp := convex_supporting_inequality hF hg' (σ • x' + (1 - σ) • z')
    have he : σ • x' + (1 - σ) • z' - x' = (1 - σ) • (z' - x') := by module
    rw [he, dot_smul_right] at hsupp
    have hmid := hz'O.2.2
    have hx1 := hx'O.1
    have hz1 := hz'O.1
    have h1 : F z' - F x' ≤ dot g' (z' - x') := by linarith
    have h2 : (1 - σ) * (F z' - F x') ≤ (1 - σ) * dot g' (z' - x') :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    nlinarith
  have hfinal : ∀ N T : ℝ, 0 < T → N ^ 2 ≤ C * T → 0 ≤ C := by
    intro N T hT0 hNT
    refine le_of_not_gt (fun hneg => ?_)
    nlinarith [sq_nonneg N, mul_neg_of_neg_of_pos hneg hT0]
  rcases le_total (F z') (F x') with hord | hord
  · exact hfinal _ _ hT (hC x' z' g' h' hx'K hz'K hg' hh' hz'O.1.le hord hT)
  · have hT' : 0 < dot (g' - h') (x' - z') := by rw [dot_swap_neg]; exact hT
    exact hfinal _ _ hT' (hC z' x' h' g' hz'K hx'K hh' hg' hx'O.1.le hord hT')

/-! ### Section 4.1: setup (lines 28-62) -/

/-- Item `C/04_R/disp/002` (`companion/chapters/04_R.tex:35-37`): "Fix bounds $R>0$ and $G>0$
such that $\|r_x\|\le R$, $\|g\|\le G$ $(x\in K,\ g\in\partial F(x))$." In the setting of
lines 30-34 ($F$ finite and convex, $x_*$ a minimizer, $K=\{F\le b\}$ compact, $b>F_*$), such
bounds exist. Norms are Euclidean, and $g\in\partial F(x)$ is
$F(x)+g^T(y-x)\le F(y)$ for all $y$. -/
theorem bounds_exist {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F) (xstar : Vec n)
    (_hmin : ∀ x, F xstar ≤ F x) (b : ℝ) (_hb : F xstar < b) (K : Set (Vec n))
    (_hK_def : K = {x | F x ≤ b}) (hK : IsCompact K) :
    ∃ R G : ℝ, 0 < R ∧ 0 < G ∧ (∀ x ∈ K, ‖euclideanVector (x - xstar)‖ ≤ R) ∧
      ∀ x ∈ K, ∀ g : Vec n, (∀ y, F x + dot g (y - x) ≤ F y) → ‖euclideanVector g‖ ≤ G := by
  obtain ⟨Λ, R, hΛ, hR, hΛK, hRK⟩ := Article.Global.exists_subgradient_and_radius_bounds hF xstar hK
  exact ⟨R, Λ, hR, hΛ, hRK, hΛK⟩

/-- Item `C/04_R/prose/004` (`companion/chapters/04_R.tex:38`): "Such a subgradient bound
exists because a finite convex function is locally Lipschitz on the whole space." A finite
convex $F$ on $\R^n$ is locally Lipschitz, and on the compact $K$ its subgradients are bounded in
Euclidean norm. (The library proves the bound from local boundedness of $F$.) -/
theorem locally_lipschitz_bound {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    {K : Set (Vec n)} (hK : IsCompact K) :
    LocallyLipschitz F ∧ ∃ G : ℝ, 0 < G ∧
      ∀ x ∈ K, ∀ g : Vec n, (∀ y, F x + dot g (y - x) ≤ F y) → ‖euclideanVector g‖ ≤ G := by
  refine ⟨hF.locallyLipschitz, ?_⟩
  obtain ⟨Λ, R, hΛ, -, hΛK, -⟩ := Article.Global.exists_subgradient_and_radius_bounds hF 0 hK
  exact ⟨Λ, hΛ, hΛK⟩

/-- Item `C/04_R/disp/003` (`companion/chapters/04_R.tex:41-44`): the notation
$g=\nabla F(x)$, $h=\nabla F(z)$, $y=h-g$, $s=z-x$, $T(x,z)=y^Ts$, $N(x,z)=y^Tr_z$ for
differentiable $x,z\in K$ (line 40, "For differentiable $x,z\in K$, put"; "$\in K$" added on 15
October 2026, wording point W20). A gradient $g=\nabla F(x)$ is
`HasFDerivAt F (gradientFunctional g) x`, where `gradientFunctional g v = dot g v`; the library's
`secantCurvature x z g h` is $T$ and `radialNumerator xstar z g h` is $N$. -/
theorem secant_notation {n : ℕ} (xstar x z g h y s : Vec n) (hy : y = h - g) (hs : s = z - x) :
    RadialCertificate.secantCurvature x z g h = dot y s ∧
      RadialCertificate.radialNumerator xstar z g h = dot y (z - xstar) ∧
      (∀ v, gradientFunctional g v = dot g v) := by
  subst hy hs
  exact ⟨rfl, rfl, gradientFunctional_apply g⟩

/-- Item `C/04_R/disp/004` (`companion/chapters/04_R.tex:46-48`): the supporting-plane error
\[ D_F(z,x)=F(z)-F(x)-g^T(z-x)\ge0. \]
Stated in the setting of the section, with the bounds $R,G$; $D$ is $D_F(z,x)$ with its
defining equation (the library's `supportingError F x g z`). Only $x$ is differentiable
(line 49); $z$ is arbitrary. -/
theorem supporting_error_nonneg {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (xstar : Vec n) (_hmin : ∀ x, F xstar ≤ F x) (b : ℝ) (_hb : F xstar < b)
    (K : Set (Vec n)) (_hK_def : K = {x | F x ≤ b}) (_hK : IsCompact K)
    (R G : ℝ) (_hR : 0 < R) (_hG : 0 < G)
    (_hRK : ∀ x ∈ K, ‖euclideanVector (x - xstar)‖ ≤ R)
    (_hGK : ∀ x ∈ K, ∀ v : Vec n, (∀ y, F x + dot v (y - x) ≤ F y) → ‖euclideanVector v‖ ≤ G)
    (x z g : Vec n) (hg : HasFDerivAt F (gradientFunctional g) x)
    (D : ℝ) (hD : D = F z - F x - dot g (z - x)) :
    D = RadialCertificate.supportingError F x g z ∧ 0 ≤ D := by
  refine ⟨hD, ?_⟩
  rw [hD]
  linarith [convex_supporting_inequality hF hg z]

/-- Item `C/04_R/disp/005` (`companion/chapters/04_R.tex:50-52`):
\[ T=D_F(z,x)+D_F(x,z),\qquad 0\le T\le T_{\max}:=4GR, \]
for differentiable $x,z\in K$, in the setting of the section with the bounds $R,G$; $T$ and
$T_{\max}$ are variables with their defining equations. -/
theorem curvature_split {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (xstar : Vec n) (_hmin : ∀ x, F xstar ≤ F x) (b : ℝ) (_hb : F xstar < b)
    (K : Set (Vec n)) (_hK_def : K = {x | F x ≤ b}) (_hK : IsCompact K)
    (R G : ℝ) (hR : 0 < R) (hG : 0 < G)
    (hRK : ∀ x ∈ K, ‖euclideanVector (x - xstar)‖ ≤ R)
    (hGK : ∀ x ∈ K, ∀ v : Vec n, (∀ y, F x + dot v (y - x) ≤ F y) → ‖euclideanVector v‖ ≤ G)
    (x z g h : Vec n) (hx : x ∈ K) (hz : z ∈ K)
    (hg : HasFDerivAt F (gradientFunctional g) x) (hh : HasFDerivAt F (gradientFunctional h) z)
    (T Tmax : ℝ) (hT : T = dot (h - g) (z - x)) (hTmax : Tmax = 4 * G * R) :
    T = (F z - F x - dot g (z - x)) + (F x - F z - dot h (x - z)) ∧ 0 ≤ T ∧ T ≤ Tmax := by
  have hsplit := RadialCertificate.secantCurvature_eq_errors F x z g h
  unfold RadialCertificate.secantCurvature RadialCertificate.supportingError at hsplit
  have h1 := convex_supporting_inequality hF hg z
  have h2 := convex_supporting_inequality hF hh x
  have hle := RadialCertificate.secantCurvature_le_four_mul xstar x z g h G R hG.le hR.le
    (gradient_bound hF hGK hx hg) (gradient_bound hF hGK hz hh)
    (Article.Global.sqNorm_le_of_norm_le (hRK x hx))
    (Article.Global.sqNorm_le_of_norm_le (hRK z hz))
  unfold RadialCertificate.secantCurvature at hle
  refine ⟨hT.trans hsplit, ?_, ?_⟩
  · rw [hT, hsplit]
    linarith
  · rw [hT, hTmax]
    exact hle

/-- The supporting error at $x$ is at most $T$ (line 200: "$0\le D_F(z,x)\le T\le T_{\max}$"),
for differentiable $x,z$. -/
theorem error_le_curvature {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    {x z g h : Vec n} (hg : HasFDerivAt F (gradientFunctional g) x)
    (hh : HasFDerivAt F (gradientFunctional h) z) :
    0 ≤ F z - F x - dot g (z - x) ∧ F z - F x - dot g (z - x) ≤ dot (h - g) (z - x) := by
  have hsplit := RadialCertificate.secantCurvature_eq_errors F x z g h
  unfold RadialCertificate.secantCurvature RadialCertificate.supportingError at hsplit
  have h1 := convex_supporting_inequality hF hg z
  have h2 := convex_supporting_inequality hF hh x
  constructor <;> linarith

/-! ### Section 4.2: Theorem `R:thm:equiv` -/

/-- Item `C/04_R/theorem/R:thm:equiv` (`companion/chapters/04_R.tex:73-82`), Theorem
`R:thm:equiv` ("Inward radial smoothness is equivalent to (RS)"), including its display
`C/04_R/disp/007` (equation (4.IR), lines 75-80). "On the compact sublevel $K$, condition (RS)
is equivalent, up to constants, to [(IR)]. No differentiability of $x-tr_x$ is required. The
sampled point is a convex combination of $x$ and $x_*$, so it remains in $K$." In the setting
of lines 30-34 ($F$ finite convex, $x_*$ a minimizer, $K=\{F\le b\}$ compact, $b>F_*$). (IR)
asks for a gradient only at $x$ (`IR`); the sampled points are those with
$0\le t\le\theta_\eta\le1/2$.

The proof is the library's `radial_iff_inward_on_compact_sublevel`: (IR)⇒(RS) is
`radial_of_inward_on_compact` (the subsection of lines 89-116, displays `inward_probe_at_z` to
`inward_to_radial` below), and (RS)⇒(IR) is `inward_of_radial_on_compact_sublevel` (lines
122-151, displays `theta_choice` to `error_bound_pos` below, then approximation). Here (RS) and
(IR) have real constants; with the nonnegative constants printed since 15 October 2026 (W19) the
theorem is `equiv_nonneg`. -/
theorem equiv {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F) (xstar : Vec n)
    (hmin : ∀ x, F xstar ≤ F x) (b : ℝ) (hb : F xstar < b) (K : Set (Vec n))
    (hK_def : K = {x | F x ≤ b}) (hK : IsCompact K) :
    (RS F xstar K ↔ IR F xstar K) ∧
      ∀ x ∈ K, ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 2 →
        x - t • (x - xstar) = (1 - t) • x + t • xstar ∧ x - t • (x - xstar) ∈ K := by
  refine ⟨?_, fun x hx t ht0 ht1 => ⟨by module, Article.Global.inward_point_mem hF xstar hmin b hb
    K hK_def hK hx ht0 (by linarith)⟩⟩
  rw [RS_iff_library, IR_iff_library]
  subst hK_def
  exact RadialCertificate.radial_iff_inward_on_compact_sublevel hF xstar hmin b hb hK

/-- Item `C/04_R/theorem/R:thm:equiv` (`companion/chapters/04_R.tex:73-82`), Theorem
`R:thm:equiv` as printed since 15 October 2026, with (RS) and (IR) stated with nonnegative
constants (wording point W19: "$\exists C_\eta\ge0$" in (4.RS), "there exist $M_\eta\ge0$ and
$\theta_\eta\in(0,1/2]$" in (4.IR)): on the compact sublevel $K$, (RS) is equivalent, up to
constants, to (IR), and the sampled points $x-tr_x$, $0\le t\le1/2$, are convex combinations of
$x$ and $x_*$ in $K$. From `equiv` with `RSNonneg_iff` and `IRNonneg_iff`. -/
theorem equiv_nonneg {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F) (xstar : Vec n)
    (hmin : ∀ x, F xstar ≤ F x) (b : ℝ) (hb : F xstar < b) (K : Set (Vec n))
    (hK_def : K = {x | F x ≤ b}) (hK : IsCompact K) :
    (RSNonneg F xstar K ↔ IRNonneg F xstar K) ∧
      ∀ x ∈ K, ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 2 →
        x - t • (x - xstar) = (1 - t) • x + t • xstar ∧ x - t • (x - xstar) ∈ K := by
  obtain ⟨h1, h2⟩ := equiv hF xstar hmin b hb K hK_def hK
  exact ⟨(RSNonneg_iff F xstar K).trans (h1.trans (IRNonneg_iff F xstar K).symm), h2⟩

/-- (IR) with the factor $\|r_x\|^2$ placed in the upper bound (line 83). -/
def IRScaled {n : ℕ} (F : Vec n → ℝ) (xstar : Vec n) (K : Set (Vec n)) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ M θ : ℝ, 0 < θ ∧ θ ≤ 1 / 2 ∧
    ∀ x g : Vec n, x ∈ K → HasFDerivAt F (gradientFunctional g) x → F xstar + η ≤ F x →
      ∀ t : ℝ, 0 ≤ t → t ≤ θ →
        0 ≤ F (x - t • (x - xstar)) - F x + t * dot g (x - xstar) ∧
          F (x - t • (x - xstar)) - F x + t * dot g (x - xstar) ≤
            M / 2 * t ^ 2 * ‖euclideanVector (x - xstar)‖ ^ 2

/-- Item `C/04_R/prose/012` (`companion/chapters/04_R.tex:83`): "A factor $\|r_x\|^2$ can
alternatively be placed in the upper bound: on a positive objective band, the two conventions
are equivalent because $\eta/G\le\|r_x\|\le R$." In the setting with the bounds $R,G$: at every
differentiable $x\in K$ with $F(x)\ge F_*+\eta$, $\eta/G\le\|r_x\|\le R$ (Euclidean norm); and
(IR) is equivalent on $K$ to the version with the factor $\|r_x\|^2$ (`IRScaled`). -/
theorem norm_convention {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (xstar : Vec n) (_hmin : ∀ x, F xstar ≤ F x) (b : ℝ) (_hb : F xstar < b)
    (K : Set (Vec n)) (_hK_def : K = {x | F x ≤ b}) (hK : IsCompact K)
    (R G : ℝ) (_hR : 0 < R) (hG : 0 < G)
    (hRK : ∀ x ∈ K, ‖euclideanVector (x - xstar)‖ ≤ R)
    (hGK : ∀ x ∈ K, ∀ v : Vec n, (∀ y, F x + dot v (y - x) ≤ F y) → ‖euclideanVector v‖ ≤ G) :
    (∀ η : ℝ, 0 < η → ∀ x g : Vec n, x ∈ K → HasFDerivAt F (gradientFunctional g) x →
      F xstar + η ≤ F x → η / G ≤ ‖euclideanVector (x - xstar)‖ ∧
        ‖euclideanVector (x - xstar)‖ ≤ R) ∧
      (IR F xstar K ↔ IRScaled F xstar K) := by
  refine ⟨fun η hη x g hx hg hband =>
    ⟨RadialNormConvention.positive_band_radius_lower hF xstar hη hG
      (gradient_bound hF hGK hx hg) hband hg, hRK x hx⟩, ?_⟩
  have hS : IRScaled F xstar K ↔ RadialNormConvention.HasNormScaledInwardBounds F K xstar := by
    constructor
    · intro h η hη
      obtain ⟨M, θ, hθ, hθ', hM⟩ := h η hη
      refine ⟨M, θ, hθ, hθ', fun x g hx hb hg t h0 h1 => ?_⟩
      rw [RadialCertificate.inward_error_eq]
      exact hM x g hx hg hb t h0 h1
    · intro h η hη
      obtain ⟨M, θ, hθ, hθ', hM⟩ := h η hη
      refine ⟨M, θ, hθ, hθ', fun x g hx hg hb t h0 h1 => ?_⟩
      have h' := hM x g hx hb hg t h0 h1
      rw [RadialCertificate.inward_error_eq] at h'
      exact h'
  rw [hS, IR_iff_library]
  exact RadialNormConvention.inward_iff_norm_scaled_on_compact hF hK xstar


/-! ### Proof that (IR) implies (RS) (lines 89-116)

Standing assumptions of the displays: the setting with the bounds $R,G$, condition (IR), a
fixed band $\eta>0$ with its constants $M\in\R$, $\theta\in(0,1/2]$ and their inward bounds
(`hMθ`), and differentiable endpoints $x,z\in K$ on that band, $F_*+\eta\le F(z)\le F(x)$, with
$T>0$; $T$, $N$ and the supporting errors are variables with their defining equations. -/

/-- Item `C/04_R/disp/008` (`companion/chapters/04_R.tex:91-93`): "If $N\ge0$, evaluate the
supporting plane at $x$ at the inward test point $z-tr_z$. Convexity and (IR) at $z$ give
\[ tN\le D_F(z,x)+\frac M2t^2,\qquad 0\le t\le\theta." \] -/
theorem inward_probe_at_z {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (xstar : Vec n) (_hmin : ∀ x, F xstar ≤ F x) (b : ℝ) (_hb : F xstar < b)
    (K : Set (Vec n)) (_hK_def : K = {x | F x ≤ b}) (_hK : IsCompact K)
    (R G : ℝ) (_hR : 0 < R) (_hG : 0 < G)
    (_hRK : ∀ x ∈ K, ‖euclideanVector (x - xstar)‖ ≤ R)
    (_hGK : ∀ x ∈ K, ∀ v : Vec n, (∀ y, F x + dot v (y - x) ≤ F y) → ‖euclideanVector v‖ ≤ G)
    (_hIR : IR F xstar K) (η : ℝ) (_hη : 0 < η) (M θ : ℝ) (_hθ : 0 < θ) (_hθ' : θ ≤ 1 / 2)
    (hMθ : ∀ x g : Vec n, x ∈ K → HasFDerivAt F (gradientFunctional g) x → F xstar + η ≤ F x →
      ∀ t : ℝ, 0 ≤ t → t ≤ θ →
        0 ≤ F (x - t • (x - xstar)) - F x + t * dot g (x - xstar) ∧
          F (x - t • (x - xstar)) - F x + t * dot g (x - xstar) ≤ M / 2 * t ^ 2)
    (x z g h : Vec n) (_hx : x ∈ K) (hz : z ∈ K)
    (hg : HasFDerivAt F (gradientFunctional g) x) (hh : HasFDerivAt F (gradientFunctional h) z)
    (hzband : F xstar + η ≤ F z) (_horder : F z ≤ F x)
    (T N : ℝ) (_hT_def : T = dot (h - g) (z - x)) (hN_def : N = dot (h - g) (z - xstar))
    (_hT : 0 < T) (_hN : 0 ≤ N) (Dzx : ℝ) (hDzx : Dzx = F z - F x - dot g (z - x))
    (t : ℝ) (ht0 : 0 ≤ t) (htθ : t ≤ θ) :
    t * N ≤ Dzx + M / 2 * t ^ 2 := by
  have hir : RadialCertificate.supportingError F z h (RadialCertificate.inwardPoint xstar z t) ≤
      M / 2 * t ^ 2 := by
    rw [RadialCertificate.inward_error_eq]
    exact (hMθ z h hz hh hzband t ht0 htθ).2
  have hp := RadialCertificate.inward_probe hF xstar x z g h hg M t hir
  rw [hN_def, hDzx]
  unfold RadialCertificate.radialNumerator RadialCertificate.supportingError at hp
  linarith

/-- Item `C/04_R/disp/009` (`companion/chapters/04_R.tex:95-97`): in the case $N<0$,
\[ (g-h)^Tr_x=T-N\ge|N|. \] -/
theorem swap_identity {n : ℕ} {F : Vec n → ℝ} (_hF : ConvexOn ℝ univ F)
    (xstar : Vec n) (_hmin : ∀ x, F xstar ≤ F x) (b : ℝ) (_hb : F xstar < b)
    (K : Set (Vec n)) (_hK_def : K = {x | F x ≤ b}) (_hK : IsCompact K)
    (R G : ℝ) (_hR : 0 < R) (_hG : 0 < G)
    (_hRK : ∀ x ∈ K, ‖euclideanVector (x - xstar)‖ ≤ R)
    (_hGK : ∀ x ∈ K, ∀ v : Vec n, (∀ y, F x + dot v (y - x) ≤ F y) → ‖euclideanVector v‖ ≤ G)
    (_hIR : IR F xstar K) (η : ℝ) (_hη : 0 < η) (M θ : ℝ) (_hθ : 0 < θ) (_hθ' : θ ≤ 1 / 2)
    (_hMθ : ∀ x g : Vec n, x ∈ K → HasFDerivAt F (gradientFunctional g) x → F xstar + η ≤ F x →
      ∀ t : ℝ, 0 ≤ t → t ≤ θ →
        0 ≤ F (x - t • (x - xstar)) - F x + t * dot g (x - xstar) ∧
          F (x - t • (x - xstar)) - F x + t * dot g (x - xstar) ≤ M / 2 * t ^ 2)
    (x z g h : Vec n) (_hx : x ∈ K) (_hz : z ∈ K)
    (_hg : HasFDerivAt F (gradientFunctional g) x) (_hh : HasFDerivAt F (gradientFunctional h) z)
    (_hzband : F xstar + η ≤ F z) (_horder : F z ≤ F x)
    (T N : ℝ) (hT_def : T = dot (h - g) (z - x)) (hN_def : N = dot (h - g) (z - xstar))
    (hT : 0 < T) (hN : N < 0) :
    dot (g - h) (x - xstar) = T - N ∧ |N| ≤ T - N := by
  have hs := RadialCertificate.radialNumerator_swap xstar x z g h
  unfold RadialCertificate.radialNumerator RadialCertificate.secantCurvature at hs
  refine ⟨by rw [hT_def, hN_def, ← hs, dot_swap_neg], ?_⟩
  rw [abs_of_neg hN]
  linarith

/-- Item `C/04_R/disp/010` (`companion/chapters/04_R.tex:99-101`): "If $N<0$, use the inward
test point $x-tr_x$ and the supporting plane at $z$ … we instead obtain
\[ t(T-N)\le D_F(x,z)+\frac M2t^2," \]
for $0\le t\le\theta$, with $D_F(x,z)=F(x)-F(z)-h^T(x-z)$. -/
theorem inward_probe_at_x {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (xstar : Vec n) (_hmin : ∀ x, F xstar ≤ F x) (b : ℝ) (_hb : F xstar < b)
    (K : Set (Vec n)) (_hK_def : K = {x | F x ≤ b}) (_hK : IsCompact K)
    (R G : ℝ) (_hR : 0 < R) (_hG : 0 < G)
    (_hRK : ∀ x ∈ K, ‖euclideanVector (x - xstar)‖ ≤ R)
    (_hGK : ∀ x ∈ K, ∀ v : Vec n, (∀ y, F x + dot v (y - x) ≤ F y) → ‖euclideanVector v‖ ≤ G)
    (_hIR : IR F xstar K) (η : ℝ) (_hη : 0 < η) (M θ : ℝ) (_hθ : 0 < θ) (_hθ' : θ ≤ 1 / 2)
    (hMθ : ∀ x g : Vec n, x ∈ K → HasFDerivAt F (gradientFunctional g) x → F xstar + η ≤ F x →
      ∀ t : ℝ, 0 ≤ t → t ≤ θ →
        0 ≤ F (x - t • (x - xstar)) - F x + t * dot g (x - xstar) ∧
          F (x - t • (x - xstar)) - F x + t * dot g (x - xstar) ≤ M / 2 * t ^ 2)
    (x z g h : Vec n) (hx : x ∈ K) (_hz : z ∈ K)
    (hg : HasFDerivAt F (gradientFunctional g) x) (hh : HasFDerivAt F (gradientFunctional h) z)
    (hzband : F xstar + η ≤ F z) (horder : F z ≤ F x)
    (T N : ℝ) (hT_def : T = dot (h - g) (z - x)) (hN_def : N = dot (h - g) (z - xstar))
    (_hT : 0 < T) (_hN : N < 0) (Dxz : ℝ) (hDxz : Dxz = F x - F z - dot h (x - z))
    (t : ℝ) (ht0 : 0 ≤ t) (htθ : t ≤ θ) :
    t * (T - N) ≤ Dxz + M / 2 * t ^ 2 := by
  have hir : RadialCertificate.supportingError F x g (RadialCertificate.inwardPoint xstar x t) ≤
      M / 2 * t ^ 2 := by
    rw [RadialCertificate.inward_error_eq]
    exact (hMθ x g hx hg (hzband.trans horder) t ht0 htθ).2
  have hp := RadialCertificate.inward_probe hF xstar z x h g hh M t hir
  rw [RadialCertificate.radialNumerator_swap xstar x z g h] at hp
  rw [hT_def, hN_def, hDxz]
  unfold RadialCertificate.secantCurvature RadialCertificate.radialNumerator
    RadialCertificate.supportingError at hp
  linarith

/-- Item `C/04_R/disp/011` (`companion/chapters/04_R.tex:103-105`): "In either case there is a
number $A\in[|N|,2GR]$ and a supporting error $D\in\{D_F(z,x),D_F(x,z)\}$ such that
\[ tA\le D+\frac M2t^2\quad(0\le t\le\theta)." \] -/
theorem inward_probe_common {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (xstar : Vec n) (hmin : ∀ x, F xstar ≤ F x) (b : ℝ) (hb : F xstar < b)
    (K : Set (Vec n)) (hK_def : K = {x | F x ≤ b}) (hK : IsCompact K)
    (R G : ℝ) (hR : 0 < R) (hG : 0 < G)
    (hRK : ∀ x ∈ K, ‖euclideanVector (x - xstar)‖ ≤ R)
    (hGK : ∀ x ∈ K, ∀ v : Vec n, (∀ y, F x + dot v (y - x) ≤ F y) → ‖euclideanVector v‖ ≤ G)
    (hIR : IR F xstar K) (η : ℝ) (hη : 0 < η) (M θ : ℝ) (hθ : 0 < θ) (hθ' : θ ≤ 1 / 2)
    (hMθ : ∀ x g : Vec n, x ∈ K → HasFDerivAt F (gradientFunctional g) x → F xstar + η ≤ F x →
      ∀ t : ℝ, 0 ≤ t → t ≤ θ →
        0 ≤ F (x - t • (x - xstar)) - F x + t * dot g (x - xstar) ∧
          F (x - t • (x - xstar)) - F x + t * dot g (x - xstar) ≤ M / 2 * t ^ 2)
    (x z g h : Vec n) (hx : x ∈ K) (hz : z ∈ K)
    (hg : HasFDerivAt F (gradientFunctional g) x) (hh : HasFDerivAt F (gradientFunctional h) z)
    (hzband : F xstar + η ≤ F z) (horder : F z ≤ F x)
    (T N : ℝ) (hT_def : T = dot (h - g) (z - x)) (hN_def : N = dot (h - g) (z - xstar))
    (hT : 0 < T) (Dzx Dxz : ℝ) (hDzx : Dzx = F z - F x - dot g (z - x))
    (hDxz : Dxz = F x - F z - dot h (x - z)) :
    ∃ A D : ℝ, |N| ≤ A ∧ A ≤ 2 * G * R ∧ (D = Dzx ∨ D = Dxz) ∧
      ∀ t : ℝ, 0 ≤ t → t ≤ θ → t * A ≤ D + M / 2 * t ^ 2 := by
  by_cases hN : 0 ≤ N
  · refine ⟨N, Dzx, (abs_of_nonneg hN).le, ?_, Or.inl rfl, fun t h0 h1 =>
      inward_probe_at_z hF xstar hmin b hb K hK_def hK R G hR hG hRK hGK hIR η hη M θ hθ hθ' hMθ
        x z g h hx hz hg hh hzband horder T N hT_def hN_def hT hN Dzx hDzx t h0 h1⟩
    rw [hN_def]
    exact (le_abs_self _).trans (RadialCertificate.abs_radialNumerator_le_two_mul xstar z g h G R
      hG.le hR.le (gradient_bound hF hGK hx hg) (gradient_bound hF hGK hz hh)
      (Article.Global.sqNorm_le_of_norm_le (hRK z hz)))
  · have hNneg : N < 0 := lt_of_not_ge hN
    obtain ⟨hswap, habs⟩ := swap_identity hF xstar hmin b hb K hK_def hK R G hR hG hRK hGK hIR η hη
      M θ hθ hθ' hMθ x z g h hx hz hg hh hzband horder T N hT_def hN_def hT hNneg
    refine ⟨T - N, Dxz, habs, ?_, Or.inr rfl, fun t h0 h1 =>
      inward_probe_at_x hF xstar hmin b hb K hK_def hK R G hR hG hRK hGK hIR η hη M θ hθ hθ' hMθ
        x z g h hx hz hg hh hzband horder T N hT_def hN_def hT hNneg Dxz hDxz t h0 h1⟩
    rw [← hswap]
    have hab := RadialCertificate.abs_radialNumerator_le_two_mul xstar x h g G R hG.le hR.le
      (gradient_bound hF hGK hz hh) (gradient_bound hF hGK hx hg)
      (Article.Global.sqNorm_le_of_norm_le (hRK x hx))
    unfold RadialCertificate.radialNumerator at hab
    calc dot (g - h) (x - xstar) = dot (h - g) (xstar - x) := (dot_swap_neg h g xstar x).symm
      _ ≤ |dot (g - h) (x - xstar)| := by rw [dot_swap_neg]; exact le_abs_self _
      _ ≤ 2 * G * R := hab

/-- Proof of Theorem `R:thm:equiv`, undisplayed claim of line 106 (not a register item): "When
$M>0$ and $A\le M\theta$, take $t=A/M$ to get $A^2\le2MD$." -/
theorem inward_probe_small_case {A D M θ : ℝ} (hA : 0 ≤ A) (hM : 0 < M) (hAM : A ≤ M * θ)
    (hprobe : ∀ t : ℝ, 0 ≤ t → t ≤ θ → t * A ≤ D + M / 2 * t ^ 2) : A ^ 2 ≤ 2 * M * D := by
  have ht : A / M ≤ θ := (div_le_iff₀ hM).2 (by linarith)
  have hp := hprobe (A / M) (div_nonneg hA hM.le) ht
  have he : M * (A / M) = A := mul_div_cancel₀ A hM.ne'
  nlinarith [mul_le_mul_of_nonneg_left hp hM.le]

/-- Item `C/04_R/disp/012` (`companion/chapters/04_R.tex:107-109`): "Otherwise take $t=\theta$;
if $A>M\theta$, then $D\ge A\theta/2$, so
\[ A^2\le\frac{4GR}{\theta}D." \]
Stated under the standing assumptions and the conclusion of display `disp/011` ($A$, $D$ as
variables with its properties), in the case $A>M\theta$. -/
theorem inward_probe_large_case {n : ℕ} {F : Vec n → ℝ} (_hF : ConvexOn ℝ univ F)
    (xstar : Vec n) (_hmin : ∀ x, F xstar ≤ F x) (b : ℝ) (_hb : F xstar < b)
    (K : Set (Vec n)) (_hK_def : K = {x | F x ≤ b}) (_hK : IsCompact K)
    (R G : ℝ) (hR : 0 < R) (hG : 0 < G)
    (_hRK : ∀ x ∈ K, ‖euclideanVector (x - xstar)‖ ≤ R)
    (_hGK : ∀ x ∈ K, ∀ v : Vec n, (∀ y, F x + dot v (y - x) ≤ F y) → ‖euclideanVector v‖ ≤ G)
    (_hIR : IR F xstar K) (η : ℝ) (_hη : 0 < η) (M θ : ℝ) (hθ : 0 < θ) (_hθ' : θ ≤ 1 / 2)
    (_hMθ : ∀ x g : Vec n, x ∈ K → HasFDerivAt F (gradientFunctional g) x → F xstar + η ≤ F x →
      ∀ t : ℝ, 0 ≤ t → t ≤ θ →
        0 ≤ F (x - t • (x - xstar)) - F x + t * dot g (x - xstar) ∧
          F (x - t • (x - xstar)) - F x + t * dot g (x - xstar) ≤ M / 2 * t ^ 2)
    (x z g h : Vec n) (_hx : x ∈ K) (_hz : z ∈ K)
    (_hg : HasFDerivAt F (gradientFunctional g) x) (_hh : HasFDerivAt F (gradientFunctional h) z)
    (_hzband : F xstar + η ≤ F z) (_horder : F z ≤ F x)
    (T N : ℝ) (_hT_def : T = dot (h - g) (z - x)) (_hN_def : N = dot (h - g) (z - xstar))
    (_hT : 0 < T) (Dzx Dxz : ℝ) (_hDzx : Dzx = F z - F x - dot g (z - x))
    (_hDxz : Dxz = F x - F z - dot h (x - z))
    (A D : ℝ) (hA : |N| ≤ A) (hAB : A ≤ 2 * G * R) (_hD : D = Dzx ∨ D = Dxz)
    (hprobe : ∀ t : ℝ, 0 ≤ t → t ≤ θ → t * A ≤ D + M / 2 * t ^ 2) (hAM : M * θ < A) :
    A * θ / 2 ≤ D ∧ A ^ 2 ≤ 4 * G * R / θ * D := by
  have hA0 : 0 ≤ A := (abs_nonneg N).trans hA
  have hp := hprobe θ hθ.le le_rfl
  have hMθ2 : M * θ ^ 2 < A * θ := by nlinarith
  have hDA : A * θ / 2 ≤ D := by nlinarith
  refine ⟨hDA, ?_⟩
  have hA2 : A ≤ 2 * D / θ := by rw [le_div_iff₀ hθ]; linarith
  have hGR : 0 ≤ 2 * G * R := by positivity
  calc A ^ 2 = A * A := by ring
    _ ≤ (2 * G * R) * A := mul_le_mul_of_nonneg_right hAB hA0
    _ ≤ (2 * G * R) * (2 * D / θ) := mul_le_mul_of_nonneg_left hA2 hGR
    _ = 4 * G * R / θ * D := by ring

/-- Item `C/04_R/disp/013`, equation `R:eq:IRtoRS` (`companion/chapters/04_R.tex:111-115`):
\[ N^2\le CT,\qquad C=\max\left\{2M,\frac{4GR}{\theta}\right\}. \]
Under the standing assumptions of the subsection ($M$ real). The proof is the paper's:
`inward_probe_common` gives $A$, $D$, the library's `inward_probe_quadratic_bound` (applied with
$\max\{M,0\}$; the cases of lines 106-110) bounds $A^2$, and $D\le T$, $N^2\le A^2$. -/
theorem inward_to_radial {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (xstar : Vec n) (hmin : ∀ x, F xstar ≤ F x) (b : ℝ) (hb : F xstar < b)
    (K : Set (Vec n)) (hK_def : K = {x | F x ≤ b}) (hK : IsCompact K)
    (R G : ℝ) (hR : 0 < R) (hG : 0 < G)
    (hRK : ∀ x ∈ K, ‖euclideanVector (x - xstar)‖ ≤ R)
    (hGK : ∀ x ∈ K, ∀ v : Vec n, (∀ y, F x + dot v (y - x) ≤ F y) → ‖euclideanVector v‖ ≤ G)
    (hIR : IR F xstar K) (η : ℝ) (hη : 0 < η) (M θ : ℝ) (hθ : 0 < θ) (hθ' : θ ≤ 1 / 2)
    (hMθ : ∀ x g : Vec n, x ∈ K → HasFDerivAt F (gradientFunctional g) x → F xstar + η ≤ F x →
      ∀ t : ℝ, 0 ≤ t → t ≤ θ →
        0 ≤ F (x - t • (x - xstar)) - F x + t * dot g (x - xstar) ∧
          F (x - t • (x - xstar)) - F x + t * dot g (x - xstar) ≤ M / 2 * t ^ 2)
    (x z g h : Vec n) (hx : x ∈ K) (hz : z ∈ K)
    (hg : HasFDerivAt F (gradientFunctional g) x) (hh : HasFDerivAt F (gradientFunctional h) z)
    (hzband : F xstar + η ≤ F z) (horder : F z ≤ F x)
    (T N : ℝ) (hT_def : T = dot (h - g) (z - x)) (hN_def : N = dot (h - g) (z - xstar))
    (hT : 0 < T) (C : ℝ) (hC : C = max (2 * M) (4 * G * R / θ)) :
    N ^ 2 ≤ C * T := by
  obtain ⟨A, D, hA, hAB, hD, hprobe⟩ := inward_probe_common hF xstar hmin b hb K hK_def hK R G hR hG
    hRK hGK hIR η hη M θ hθ hθ' hMθ x z g h hx hz hg hh hzband horder T N hT_def hN_def hT _ _
    rfl rfl
  have hA0 : 0 ≤ A := (abs_nonneg N).trans hA
  have hD0 : 0 ≤ D := by
    rcases hD with rfl | rfl
    · linarith [convex_supporting_inequality hF hg z]
    · linarith [convex_supporting_inequality hF hh x]
  have hDT : D ≤ T := by
    have h1 := (error_le_curvature hF hg hh).2
    have h2 := (error_le_curvature hF hh hg).2
    rw [hT_def]
    rcases hD with rfl | rfl
    · exact h1
    · rw [dot_swap_neg] at h2; exact h2
  set M' := max M 0 with hM'
  have hprobe' : ∀ t : ℝ, 0 ≤ t → t ≤ θ → t * A ≤ D + M' / 2 * t ^ 2 := fun t h0 h1 => by
    have := hprobe t h0 h1
    have : M / 2 * t ^ 2 ≤ M' / 2 * t ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith [le_max_left M 0]) (sq_nonneg t)
    linarith
  have hq := RadialCertificate.inward_probe_quadratic_bound hA0 hAB hD0 (le_max_right M 0) hθ
    hprobe'
  have hconst : max (2 * M') (2 * (2 * G * R) / θ) = C := by
    rw [hC, hM']
    have hpos : 0 < 4 * G * R / θ := by positivity
    have he : 2 * (2 * G * R) / θ = 4 * G * R / θ := by ring
    rw [he]
    rcases le_total M 0 with hM0 | hM0
    · rw [max_eq_right hM0, mul_zero, max_eq_right hpos.le,
        max_eq_right (by linarith : 2 * M ≤ 4 * G * R / θ)]
    · rw [max_eq_left hM0]
  rw [hconst] at hq
  have hC0 : 0 ≤ C := by rw [hC]; exact le_trans (by positivity) (le_max_right _ _)
  have hNA : N ^ 2 ≤ A ^ 2 := by
    have := abs_le_abs_of_nonneg (abs_nonneg N) hA
    rw [← sq_abs N]
    nlinarith [abs_nonneg N]
  exact hNA.trans (hq.trans (mul_le_mul_of_nonneg_left hDT hC0))


/-! ### Proof that (RS) implies (IR) (lines 122-151)

Standing assumptions of the displays: the setting with the bounds $R,G$, condition (RS) and a
fixed $\eta>0$; then $\theta_\eta$ with its defining equation, a point $x\in K$ on the
$\eta$-band, $0\le t\le\theta_\eta$ and $z=x-tr_x$; from display `disp/016` on, both endpoints
are differentiable with gradients $g,h$, and $a$ is a variable with its defining equation;
from display `disp/018` on, $C$ is a constant of (RS) on the $\eta/2$-band (hypothesis `hC`). -/

/-- Item `C/04_R/disp/014` (`companion/chapters/04_R.tex:124-126`): "Fix $\eta>0$ and choose
\[ \theta_\eta=\min\left\{\frac12,\frac{\eta}{4GR}\right\}." \]
This is an admissible (IR) parameter: $\theta_\eta\in(0,1/2]$. -/
theorem theta_choice {n : ℕ} {F : Vec n → ℝ} (_hF : ConvexOn ℝ univ F)
    (xstar : Vec n) (_hmin : ∀ x, F xstar ≤ F x) (b : ℝ) (_hb : F xstar < b)
    (K : Set (Vec n)) (_hK_def : K = {x | F x ≤ b}) (_hK : IsCompact K)
    (R G : ℝ) (hR : 0 < R) (hG : 0 < G)
    (_hRK : ∀ x ∈ K, ‖euclideanVector (x - xstar)‖ ≤ R)
    (_hGK : ∀ x ∈ K, ∀ v : Vec n, (∀ y, F x + dot v (y - x) ≤ F y) → ‖euclideanVector v‖ ≤ G)
    (_hRS : RS F xstar K) (η : ℝ) (hη : 0 < η)
    (θ : ℝ) (hθ_def : θ = min (1 / 2) (η / (4 * G * R))) :
    0 < θ ∧ θ ≤ 1 / 2 := by
  rw [hθ_def]
  exact ⟨lt_min (by norm_num) (by positivity), min_le_left _ _⟩

/-- Item `C/04_R/disp/015` (`companion/chapters/04_R.tex:128-130`): "For $x$ on the $\eta$-band
and $z=x-tr_x$, the Lipschitz bound on $K$ gives
\[ F(z)\ge F(x)-GtR\ge F_*+3\eta/4." \]
No differentiability is used (the Lipschitz bound is `Article.Global.lipschitz_on_K`). -/
theorem inner_band {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (xstar : Vec n) (hmin : ∀ x, F xstar ≤ F x) (b : ℝ) (hb : F xstar < b)
    (K : Set (Vec n)) (hK_def : K = {x | F x ≤ b}) (hK : IsCompact K)
    (R G : ℝ) (hR : 0 < R) (hG : 0 < G)
    (hRK : ∀ x ∈ K, ‖euclideanVector (x - xstar)‖ ≤ R)
    (hGK : ∀ x ∈ K, ∀ v : Vec n, (∀ y, F x + dot v (y - x) ≤ F y) → ‖euclideanVector v‖ ≤ G)
    (_hRS : RS F xstar K) (η : ℝ) (_hη : 0 < η)
    (θ : ℝ) (hθ_def : θ = min (1 / 2) (η / (4 * G * R)))
    (x : Vec n) (hx : x ∈ K) (hxband : F xstar + η ≤ F x) (t : ℝ) (ht0 : 0 ≤ t) (htθ : t ≤ θ)
    (z : Vec n) (hz : z = x - t • (x - xstar)) :
    F x - G * t * R ≤ F z ∧ F xstar + 3 * η / 4 ≤ F x - G * t * R := by
  have hθ1 : θ ≤ 1 / 2 := by rw [hθ_def]; exact min_le_left _ _
  have hθ2 : θ ≤ η / (4 * G * R) := by rw [hθ_def]; exact min_le_right _ _
  have hzK : z ∈ K := by
    rw [hz]
    exact Article.Global.inward_point_mem hF xstar hmin b hb K hK_def hK hx ht0 (by linarith)
  have hlip := Article.Global.lipschitz_on_K hF G hGK hx hzK
  have hxz : x - z = t • (x - xstar) := by rw [hz]; abel
  rw [hxz, Article.Global.norm_euclideanVector_smul, abs_of_nonneg ht0] at hlip
  have hr := hRK x hx
  have h1 : G * (t * ‖euclideanVector (x - xstar)‖) ≤ G * t * R := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_left hr (by positivity)
  have h2 : G * t * R ≤ η / 4 := by
    have h4 := (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * G * R)).mp (htθ.trans hθ2)
    nlinarith
  constructor
  · have := (abs_le.mp hlip).2
    linarith
  · linarith

/-- Item `C/04_R/disp/016` (`companion/chapters/04_R.tex:132-134`): "First suppose both
endpoints are differentiable. Put $a=(\nabla F(x)-\nabla F(z))^Tr_x\ge0$." -/
theorem a_nonneg {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (xstar : Vec n) (_hmin : ∀ x, F xstar ≤ F x) (b : ℝ) (_hb : F xstar < b)
    (K : Set (Vec n)) (_hK_def : K = {x | F x ≤ b}) (_hK : IsCompact K)
    (R G : ℝ) (_hR : 0 < R) (_hG : 0 < G)
    (_hRK : ∀ x ∈ K, ‖euclideanVector (x - xstar)‖ ≤ R)
    (_hGK : ∀ x ∈ K, ∀ v : Vec n, (∀ y, F x + dot v (y - x) ≤ F y) → ‖euclideanVector v‖ ≤ G)
    (_hRS : RS F xstar K) (η : ℝ) (_hη : 0 < η)
    (θ : ℝ) (_hθ_def : θ = min (1 / 2) (η / (4 * G * R)))
    (x : Vec n) (_hx : x ∈ K) (_hxband : F xstar + η ≤ F x) (t : ℝ) (ht0 : 0 ≤ t) (_htθ : t ≤ θ)
    (z : Vec n) (hz : z = x - t • (x - xstar))
    (g h : Vec n) (hg : HasFDerivAt F (gradientFunctional g) x)
    (hh : HasFDerivAt F (gradientFunctional h) z) (a : ℝ) (ha_def : a = dot (g - h) (x - xstar)) :
    0 ≤ a := by
  have hT := (error_le_curvature hF hg hh)
  have hid := (RadialCertificate.inward_secant_identities xstar x g h t).1
  unfold RadialCertificate.secantCurvature RadialCertificate.inwardPoint at hid
  rw [← hz] at hid
  rw [hid] at hT
  rcases eq_or_lt_of_le ht0 with h0 | h0
  · have hzx : z = x := by rw [hz, ← h0, zero_smul, sub_zero]
    rw [hzx] at hh
    rw [ha_def, gradient_unique hg hh, sub_self]
    simp [dot]
  · rw [ha_def]
    nlinarith [hT.1, hT.2]

/-- Item `C/04_R/disp/017` (`companion/chapters/04_R.tex:136-138`): "Then
$T(x,z)=ta$, $N(x,z)=-(1-t)a$." -/
theorem pair_identities {n : ℕ} {F : Vec n → ℝ} (_hF : ConvexOn ℝ univ F)
    (xstar : Vec n) (_hmin : ∀ x, F xstar ≤ F x) (b : ℝ) (_hb : F xstar < b)
    (K : Set (Vec n)) (_hK_def : K = {x | F x ≤ b}) (_hK : IsCompact K)
    (R G : ℝ) (_hR : 0 < R) (_hG : 0 < G)
    (_hRK : ∀ x ∈ K, ‖euclideanVector (x - xstar)‖ ≤ R)
    (_hGK : ∀ x ∈ K, ∀ v : Vec n, (∀ y, F x + dot v (y - x) ≤ F y) → ‖euclideanVector v‖ ≤ G)
    (_hRS : RS F xstar K) (η : ℝ) (_hη : 0 < η)
    (θ : ℝ) (_hθ_def : θ = min (1 / 2) (η / (4 * G * R)))
    (x : Vec n) (_hx : x ∈ K) (_hxband : F xstar + η ≤ F x) (t : ℝ) (_ht0 : 0 ≤ t) (_htθ : t ≤ θ)
    (z : Vec n) (hz : z = x - t • (x - xstar))
    (g h : Vec n) (_hg : HasFDerivAt F (gradientFunctional g) x)
    (_hh : HasFDerivAt F (gradientFunctional h) z) (a : ℝ) (ha_def : a = dot (g - h) (x - xstar)) :
    dot (h - g) (z - x) = t * a ∧ dot (h - g) (z - xstar) = -(1 - t) * a := by
  have hid := RadialCertificate.inward_secant_identities xstar x g h t
  unfold RadialCertificate.secantCurvature RadialCertificate.radialNumerator
    RadialCertificate.inwardPoint at hid
  rw [← hz, ← ha_def] at hid
  exact hid

/-- Item `C/04_R/disp/018` (`companion/chapters/04_R.tex:140-144`): "Using (RS) on the
$\eta/2$-band, if $a>0$,
\[ (1-t)^2a^2\le C_{\eta/2}ta,\qquad a\le\frac{C_{\eta/2}t}{(1-t)^2}." \]
$C$ is a constant of (RS) on the $\eta/2$-band (`hC`). -/
theorem a_bound {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (xstar : Vec n) (hmin : ∀ x, F xstar ≤ F x) (b : ℝ) (hb : F xstar < b)
    (K : Set (Vec n)) (hK_def : K = {x | F x ≤ b}) (hK : IsCompact K)
    (R G : ℝ) (hR : 0 < R) (hG : 0 < G)
    (hRK : ∀ x ∈ K, ‖euclideanVector (x - xstar)‖ ≤ R)
    (hGK : ∀ x ∈ K, ∀ v : Vec n, (∀ y, F x + dot v (y - x) ≤ F y) → ‖euclideanVector v‖ ≤ G)
    (hRS : RS F xstar K) (η : ℝ) (hη : 0 < η)
    (θ : ℝ) (hθ_def : θ = min (1 / 2) (η / (4 * G * R)))
    (x : Vec n) (hx : x ∈ K) (hxband : F xstar + η ≤ F x) (t : ℝ) (ht0 : 0 ≤ t) (htθ : t ≤ θ)
    (z : Vec n) (hz : z = x - t • (x - xstar))
    (g h : Vec n) (hg : HasFDerivAt F (gradientFunctional g) x)
    (hh : HasFDerivAt F (gradientFunctional h) z) (a : ℝ) (ha_def : a = dot (g - h) (x - xstar))
    (C : ℝ)
    (hC : ∀ x z g h : Vec n, x ∈ K → z ∈ K →
      HasFDerivAt F (gradientFunctional g) x → HasFDerivAt F (gradientFunctional h) z →
      F xstar + η / 2 ≤ F z → F z ≤ F x → 0 < dot (h - g) (z - x) →
      (dot (h - g) (z - xstar)) ^ 2 ≤ C * dot (h - g) (z - x)) (ha : 0 < a) :
    (1 - t) ^ 2 * a ^ 2 ≤ C * t * a ∧ a ≤ C * t / (1 - t) ^ 2 := by
  have hθ1 : θ ≤ 1 / 2 := by rw [hθ_def]; exact min_le_left _ _
  have hid := pair_identities hF xstar hmin b hb K hK_def hK R G hR hG hRK hGK hRS η hη θ hθ_def
    x hx hxband t ht0 htθ z hz g h hg hh a ha_def
  have ht : 0 < t := by
    rcases eq_or_lt_of_le ht0 with h0 | h0
    · have hzx : z = x := by rw [hz, ← h0, zero_smul, sub_zero]
      rw [hzx] at hh
      rw [ha_def, gradient_unique hg hh, sub_self] at ha
      simp [dot] at ha
    · exact h0
  have hzK : z ∈ K := by
    rw [hz]
    exact Article.Global.inward_point_mem hF xstar hmin b hb K hK_def hK hx ht0 (by linarith)
  have hzband := (inner_band hF xstar hmin b hb K hK_def hK R G hR hG hRK hGK hRS η hη θ hθ_def
    x hx hxband t ht0 htθ z hz)
  have hzord : F z ≤ F x := by
    rw [hz]
    exact RadialCertificate.inward_value_le hF xstar hmin x ht0 (by linarith)
  have hTpos : 0 < dot (h - g) (z - x) := by rw [hid.1]; positivity
  have hRSb := hC x z g h hx hzK hg hh (by linarith [hzband.1, hzband.2]) hzord hTpos
  rw [hid.1, hid.2] at hRSb
  have h1 : (1 - t) ^ 2 * a ^ 2 ≤ C * t * a := by nlinarith
  refine ⟨h1, ?_⟩
  have h1t : 0 < (1 - t) ^ 2 := by nlinarith
  rw [le_div_iff₀ h1t]
  have : (1 - t) ^ 2 * a * a ≤ C * t * a := by nlinarith
  nlinarith

/-- Item `C/04_R/disp/019` (`companion/chapters/04_R.tex:146-148`): "Convexity supplies
\[ 0\le D_F(z,x)\le ta\le4C_{\eta/2}t^2." \]
In the case $a>0$ of display `disp/018`; $D$ is $D_F(z,x)=F(z)-F(x)-g^T(z-x)$. The case
$a=0$ is `error_bound_zero`. -/
theorem error_bound_pos {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (xstar : Vec n) (hmin : ∀ x, F xstar ≤ F x) (b : ℝ) (hb : F xstar < b)
    (K : Set (Vec n)) (hK_def : K = {x | F x ≤ b}) (hK : IsCompact K)
    (R G : ℝ) (hR : 0 < R) (hG : 0 < G)
    (hRK : ∀ x ∈ K, ‖euclideanVector (x - xstar)‖ ≤ R)
    (hGK : ∀ x ∈ K, ∀ v : Vec n, (∀ y, F x + dot v (y - x) ≤ F y) → ‖euclideanVector v‖ ≤ G)
    (hRS : RS F xstar K) (η : ℝ) (hη : 0 < η)
    (θ : ℝ) (hθ_def : θ = min (1 / 2) (η / (4 * G * R)))
    (x : Vec n) (hx : x ∈ K) (hxband : F xstar + η ≤ F x) (t : ℝ) (ht0 : 0 ≤ t) (htθ : t ≤ θ)
    (z : Vec n) (hz : z = x - t • (x - xstar))
    (g h : Vec n) (hg : HasFDerivAt F (gradientFunctional g) x)
    (hh : HasFDerivAt F (gradientFunctional h) z) (a : ℝ) (ha_def : a = dot (g - h) (x - xstar))
    (C : ℝ)
    (hC : ∀ x z g h : Vec n, x ∈ K → z ∈ K →
      HasFDerivAt F (gradientFunctional g) x → HasFDerivAt F (gradientFunctional h) z →
      F xstar + η / 2 ≤ F z → F z ≤ F x → 0 < dot (h - g) (z - x) →
      (dot (h - g) (z - xstar)) ^ 2 ≤ C * dot (h - g) (z - x)) (D : ℝ)
    (hD : D = F z - F x - dot g (z - x)) (ha : 0 < a) :
    0 ≤ D ∧ D ≤ t * a ∧ t * a ≤ 4 * C * t ^ 2 := by
  have hθ1 : θ ≤ 1 / 2 := by rw [hθ_def]; exact min_le_left _ _
  have hid := pair_identities hF xstar hmin b hb K hK_def hK R G hR hG hRK hGK hRS η hη θ hθ_def
    x hx hxband t ht0 htθ z hz g h hg hh a ha_def
  have hab := a_bound hF xstar hmin b hb K hK_def hK R G hR hG hRK hGK hRS η hη θ hθ_def
    x hx hxband t ht0 htθ z hz g h hg hh a ha_def C hC ha
  have hE := error_le_curvature hF hg hh
  rw [hid.1] at hE
  refine ⟨hD ▸ hE.1, hD ▸ hE.2, ?_⟩
  have h1t : (1 / 4 : ℝ) ≤ (1 - t) ^ 2 := by nlinarith
  have hCt : 0 ≤ C * t := by
    have h0 : 0 < (1 - t) ^ 2 * a ^ 2 := by positivity
    nlinarith [hab.1]
  have ha4 : a ≤ 4 * (C * t) := by
    have h2 := hab.2
    rw [le_div_iff₀ (by nlinarith)] at h2
    nlinarith
  nlinarith

/-- Proof of Theorem `R:thm:equiv`, undisplayed claim of line 149 (not a register item): "If
$a=0$, the same conclusion follows from $D_F(z,x)\le ta=0$." This uses $C_{\eta/2}\ge0$, which
(4.RS) states since 15 October 2026 (wording point W19) and which holds anyway for an (RS)
constant with real values, because the $\eta/2$-band contains the point $z$ strictly between its
threshold and $b$ when $t>0$ (`rs_constant_nonneg`); the statement below assumes only `RS`. -/
theorem error_bound_zero {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (xstar : Vec n) (hmin : ∀ x, F xstar ≤ F x) (b : ℝ) (hb : F xstar < b)
    (K : Set (Vec n)) (hK_def : K = {x | F x ≤ b}) (hK : IsCompact K)
    (R G : ℝ) (hR : 0 < R) (hG : 0 < G)
    (hRK : ∀ x ∈ K, ‖euclideanVector (x - xstar)‖ ≤ R)
    (hGK : ∀ x ∈ K, ∀ v : Vec n, (∀ y, F x + dot v (y - x) ≤ F y) → ‖euclideanVector v‖ ≤ G)
    (hRS : RS F xstar K) (η : ℝ) (hη : 0 < η)
    (θ : ℝ) (hθ_def : θ = min (1 / 2) (η / (4 * G * R)))
    (x : Vec n) (hx : x ∈ K) (hxband : F xstar + η ≤ F x) (t : ℝ) (ht0 : 0 ≤ t) (htθ : t ≤ θ)
    (z : Vec n) (hz : z = x - t • (x - xstar))
    (g h : Vec n) (hg : HasFDerivAt F (gradientFunctional g) x)
    (hh : HasFDerivAt F (gradientFunctional h) z) (a : ℝ) (ha_def : a = dot (g - h) (x - xstar))
    (C : ℝ)
    (hC : ∀ x z g h : Vec n, x ∈ K → z ∈ K →
      HasFDerivAt F (gradientFunctional g) x → HasFDerivAt F (gradientFunctional h) z →
      F xstar + η / 2 ≤ F z → F z ≤ F x → 0 < dot (h - g) (z - x) →
      (dot (h - g) (z - xstar)) ^ 2 ≤ C * dot (h - g) (z - x)) (D : ℝ)
    (hD : D = F z - F x - dot g (z - x)) (ha : a = 0) :
    0 ≤ D ∧ D ≤ t * a ∧ t * a ≤ 4 * C * t ^ 2 := by
  have hθ1 : θ ≤ 1 / 2 := by rw [hθ_def]; exact min_le_left _ _
  have hid := pair_identities hF xstar hmin b hb K hK_def hK R G hR hG hRK hGK hRS η hη θ hθ_def
    x hx hxband t ht0 htθ z hz g h hg hh a ha_def
  have hE := error_le_curvature hF hg hh
  rw [hid.1] at hE
  refine ⟨hD ▸ hE.1, hD ▸ hE.2, ?_⟩
  rw [ha, mul_zero]
  rcases eq_or_lt_of_le ht0 with h0 | h0
  · rw [← h0]; simp
  · have hzband := (inner_band hF xstar hmin b hb K hK_def hK R G hR hG hRK hGK hRS η hη θ hθ_def
      x hx hxband t ht0 htθ z hz)
    have hzlt : F z < F x := by
      rw [hz]
      exact inward_lt hF xstar x (by linarith) h0 (by linarith)
    have hxb : F x ≤ b := by rw [hK_def] at hx; exact hx
    have hC0 := rs_constant_nonneg hF xstar b K hK_def hK (η / 2) C (by positivity) hC z
      (by linarith [hzband.1, hzband.2]) (by linarith)
    positivity

/-- Proof of Theorem `R:thm:equiv`, undisplayed claim of line 149 (not a register item): "Thus
(IR) holds with $M_\eta=8C_{\eta/2}$", for differentiable inner endpoints $z=x-tr_x$
(displays `disp/016`-`disp/019` and `error_bound_zero`). -/
theorem ir_with_eight_C {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (xstar : Vec n) (hmin : ∀ x, F xstar ≤ F x) (b : ℝ) (hb : F xstar < b)
    (K : Set (Vec n)) (hK_def : K = {x | F x ≤ b}) (hK : IsCompact K)
    (R G : ℝ) (hR : 0 < R) (hG : 0 < G)
    (hRK : ∀ x ∈ K, ‖euclideanVector (x - xstar)‖ ≤ R)
    (hGK : ∀ x ∈ K, ∀ v : Vec n, (∀ y, F x + dot v (y - x) ≤ F y) → ‖euclideanVector v‖ ≤ G)
    (hRS : RS F xstar K) (η : ℝ) (hη : 0 < η)
    (θ : ℝ) (hθ_def : θ = min (1 / 2) (η / (4 * G * R)))
    (x : Vec n) (hx : x ∈ K) (hxband : F xstar + η ≤ F x) (t : ℝ) (ht0 : 0 ≤ t) (htθ : t ≤ θ)
    (z : Vec n) (hz : z = x - t • (x - xstar))
    (g h : Vec n) (hg : HasFDerivAt F (gradientFunctional g) x)
    (hh : HasFDerivAt F (gradientFunctional h) z) (C : ℝ)
    (hC : ∀ x z g h : Vec n, x ∈ K → z ∈ K →
      HasFDerivAt F (gradientFunctional g) x → HasFDerivAt F (gradientFunctional h) z →
      F xstar + η / 2 ≤ F z → F z ≤ F x → 0 < dot (h - g) (z - x) →
      (dot (h - g) (z - xstar)) ^ 2 ≤ C * dot (h - g) (z - x)) :
    0 ≤ F z - F x + t * dot g (x - xstar) ∧
        F z - F x + t * dot g (x - xstar) ≤ 8 * C / 2 * t ^ 2 := by
  have he : F z - F x + t * dot g (x - xstar) = F z - F x - dot g (z - x) := by
    have hzx : z - x = (-t) • (x - xstar) := by rw [hz]; module
    rw [hzx, dot_smul_right]
    ring
  rw [he]
  have hnn := a_nonneg hF xstar hmin b hb K hK_def hK R G hR hG hRK hGK hRS η hη θ hθ_def
    x hx hxband t ht0 htθ z hz g h hg hh _ rfl
  rcases eq_or_lt_of_le hnn with h0 | h0
  · obtain ⟨h1, h2, h3⟩ := error_bound_zero hF xstar hmin b hb K hK_def hK R G hR hG hRK hGK hRS η
      hη θ hθ_def x hx hxband t ht0 htθ z hz g h hg hh _ rfl C hC _ rfl h0.symm
    exact ⟨h1, by linarith⟩
  · obtain ⟨h1, h2, h3⟩ := error_bound_pos hF xstar hmin b hb K hK_def hK R G hR hG hRK hGK hRS η
      hη θ hθ_def x hx hxband t ht0 htθ z hz g h hg hh _ rfl C hC _ rfl h0
    exact ⟨h1, by linarith⟩


/-! ### Interpretation and a derivative-free version (lines 157-177) -/

/-- Item `C/04_R/disp/020` (`companion/chapters/04_R.tex:159-161`): for a unit direction $d$,
the scalar function $\varphi_d(\rho)=F(x_*+\rho d)$, $\rho>0$. -/
def profile {n : ℕ} (F : Vec n → ℝ) (xstar d : Vec n) (ρ : ℝ) : ℝ := F (xstar + ρ • d)

/-- At a differentiable point $x_*+\rho d$ with gradient $g$, $\varphi_d'(\rho)=g^Td$. -/
theorem profile_hasDerivAt {n : ℕ} {F : Vec n → ℝ} {xstar d g : Vec n} {ρ : ℝ}
    (hg : HasFDerivAt F (gradientFunctional g) (xstar + ρ • d)) :
    HasDerivAt (profile F xstar d) (dot g d) ρ := by
  have hpath : HasDerivAt (fun s : ℝ => xstar + s • d) d ρ := by
    simpa using ((hasDerivAt_id ρ).smul_const d).const_add xstar
  have h := hg.comp_hasDerivAt ρ hpath
  rw [gradientFunctional_apply] at h
  exact h

/-- Item `C/04_R/prose/015` (`companion/chapters/04_R.tex:162`): "On compact positive objective
bands, the equivalent conditions control the change of its scalar derivative uniformly over
directions." In the setting with the bounds $R,G$, under (RS) (equivalently (IR), Theorem
`R:thm:equiv`): for every $\eta>0$ there is $L$ such that for every Euclidean unit direction $d$
and all $0<\rho'<\rho$ with $x_*+\rho d\in K$ and $x_*+\rho'd$ on the $\eta$-band, both points
differentiable, $0\le\varphi_d'(\rho)-\varphi_d'(\rho')\le L(\rho-\rho')$. The proof applies
(RS) to the radial pair and uses $\rho'\ge\eta/G$ (line 83); $L=\max\{C_\eta,0\}G^2/\eta^2$. -/
theorem scalar_derivative_control {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (xstar : Vec n) (hmin : ∀ x, F xstar ≤ F x) (b : ℝ) (hb : F xstar < b)
    (K : Set (Vec n)) (hK_def : K = {x | F x ≤ b}) (hK : IsCompact K)
    (R G : ℝ) (_hR : 0 < R) (hG : 0 < G)
    (_hRK : ∀ x ∈ K, ‖euclideanVector (x - xstar)‖ ≤ R)
    (hGK : ∀ x ∈ K, ∀ v : Vec n, (∀ y, F x + dot v (y - x) ≤ F y) → ‖euclideanVector v‖ ≤ G)
    (hRS : RS F xstar K) :
    ∀ η : ℝ, 0 < η → ∃ L : ℝ, ∀ d : Vec n, ‖euclideanVector d‖ = 1 →
      ∀ ρ ρ' : ℝ, 0 < ρ' → ρ' < ρ → xstar + ρ • d ∈ K → F xstar + η ≤ F (xstar + ρ' • d) →
        DifferentiableAt ℝ F (xstar + ρ • d) → DifferentiableAt ℝ F (xstar + ρ' • d) →
        0 ≤ deriv (profile F xstar d) ρ - deriv (profile F xstar d) ρ' ∧
          deriv (profile F xstar d) ρ - deriv (profile F xstar d) ρ' ≤ L * (ρ - ρ') := by
  intro η hη
  obtain ⟨C, hC⟩ := hRS η hη
  refine ⟨max C 0 * G ^ 2 / η ^ 2, ?_⟩
  intro d hd ρ ρ' hρ' hρρ' hxK hband hdx hdz
  set x := xstar + ρ • d with hx
  set z := xstar + ρ' • d with hz
  have hg := hasFDerivAt_coordinateGradient hdx
  have hh := hasFDerivAt_coordinateGradient hdz
  set g := coordinateGradient F x
  set h := coordinateGradient F z
  rw [(profile_hasDerivAt hg).deriv, (profile_hasDerivAt hh).deriv]
  have hρ : 0 < ρ := hρ'.trans hρρ'
  -- z is on the segment from x to xstar
  set τ := 1 - ρ' / ρ with hτ
  have hτ0 : 0 ≤ τ := by rw [hτ, sub_nonneg, div_le_one hρ]; exact hρρ'.le
  have hτ1 : τ ≤ 1 := by rw [hτ]; linarith [div_pos hρ' hρ]
  have hzx : z = x - τ • (x - xstar) := by
    rw [hz, hx, hτ]
    have : ρ' = (1 - (1 - ρ' / ρ)) * ρ := by field_simp
    rw [show xstar + ρ • d - (1 - ρ' / ρ) • (xstar + ρ • d - xstar) =
      xstar + ((1 - (1 - ρ' / ρ)) * ρ) • d by module, ← this]
  have hzK : z ∈ K := by
    rw [hzx]
    exact Article.Global.inward_point_mem hF xstar hmin b hb K hK_def hK hxK hτ0 hτ1
  have hzord : F z ≤ F x := by
    rw [hzx]; exact RadialCertificate.inward_value_le hF xstar hmin x hτ0 hτ1
  have hTdef : dot (h - g) (z - x) = (ρ - ρ') * (dot g d - dot h d) := by
    have he : z - x = (ρ' - ρ) • d := by rw [hz, hx]; module
    rw [he, dot_smul_right, dot_sub_left]
    ring
  have hNdef : dot (h - g) (z - xstar) = -ρ' * (dot g d - dot h d) := by
    have he : z - xstar = ρ' • d := by rw [hz]; abel
    rw [he, dot_smul_right, dot_sub_left]
    ring
  have hE := error_le_curvature hF hg hh
  rw [hTdef] at hE
  have hδ0 : 0 ≤ dot g d - dot h d := by
    by_cases h0 : dot g d - dot h d < 0
    · nlinarith [hE.1, hE.2]
    · exact not_lt.mp h0
  refine ⟨hδ0, ?_⟩
  have hρ'lo : η / G ≤ ρ' := by
    have h1 := RadialNormConvention.positive_band_radius_lower hF xstar hη hG
      (gradient_bound hF hGK hzK hh) hband hh
    have he : z - xstar = ρ' • d := by rw [hz]; abel
    rw [he, Article.Global.norm_euclideanVector_smul, hd, abs_of_pos hρ', mul_one] at h1
    exact h1
  have hηGpos : 0 < η / G := div_pos hη hG
  have hρ'sq : η ^ 2 / G ^ 2 ≤ ρ' ^ 2 := by
    rw [← div_pow]; exact pow_le_pow_left₀ hηGpos.le hρ'lo 2
  rcases eq_or_lt_of_le hδ0 with h0 | h0
  · rw [← h0]
    have : 0 ≤ max C 0 * G ^ 2 / η ^ 2 * (ρ - ρ') := by
      apply mul_nonneg _ (by linarith)
      exact div_nonneg (mul_nonneg (le_max_right _ _) (sq_nonneg _)) (sq_nonneg _)
    exact this
  · set δ := dot g d - dot h d with hδ
    have hTpos : 0 < dot (h - g) (z - x) := by rw [hTdef]; exact mul_pos (by linarith) h0
    have hrs := hC x z g h hxK hzK hg hh hband hzord hTpos
    rw [hTdef, hNdef] at hrs
    have h1 : ρ' ^ 2 * δ ≤ C * (ρ - ρ') := by nlinarith
    have h2 : ρ' ^ 2 * δ ≤ max C 0 * (ρ - ρ') :=
      h1.trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (by linarith))
    have h3 : η ^ 2 / G ^ 2 * δ ≤ ρ' ^ 2 * δ := mul_le_mul_of_nonneg_right hρ'sq h0.le
    have hη2 : 0 < η ^ 2 := by positivity
    have hG2 : 0 < G ^ 2 := by positivity
    have h4 : η ^ 2 / G ^ 2 * δ ≤ max C 0 * (ρ - ρ') := h3.trans h2
    rw [div_mul_eq_mul_div, div_le_iff₀ hG2] at h4
    rw [div_mul_eq_mul_div, mul_assoc, le_div_iff₀ hη2] at *
    nlinarith

/-- Item `C/04_R/prose/016` (`companion/chapters/04_R.tex:162`): "Angular derivatives may
jump." The benchmark $F(u,v)=u^2+|v|$, $x_*=0$, satisfies (IR) and (RS) on every compact
sublevel $\{F\le b\}$, $b>0$, yet at every point $(u,0)$ its derivative in the direction
$(0,1)$, orthogonal to the ray through $(u,0)$, jumps: $F((u,0)+s(0,1))=F(u,0)+|s|$, and $F$ is not
differentiable there. -/
theorem angular_jump (F : Vec 2 → ℝ) (hF_def : ∀ x, F x = (x 0) ^ 2 + |x 1|) :
    (∀ b : ℝ, 0 < b → IsCompact {x | F x ≤ b} ∧ IR F 0 {x | F x ≤ b} ∧ RS F 0 {x | F x ≤ b}) ∧
      ∀ u : ℝ, dot (![u, 0] - 0) ![0, 1] = 0 ∧
        (∀ s : ℝ, F (![u, 0] + s • ![0, 1]) = F ![u, 0] + |s|) ∧
            ¬ DifferentiableAt ℝ F ![u, 0] := by
  obtain ⟨hmin, -, hsub⟩ := Article.Global.mixed_inward_condition F hF_def
  obtain ⟨hconv, -⟩ := Article.Global.mixed_hypotheses F hF_def
  have hF0 : F 0 = 0 := by simp [hF_def]
  refine ⟨fun b hb => ?_, fun u => ⟨by simp [dot, Fin.sum_univ_two], fun s => ?_,
    Article.Global.mixed_not_differentiable F hF_def u⟩⟩
  · obtain ⟨hK, hIR⟩ := hsub b hb
    have hIR' : IR F 0 {x | F x ≤ b} := (IR_iff_article F 0 _).mpr hIR
    refine ⟨hK, hIR', (equiv hconv 0 hmin b (by rw [hF0]; exact hb) _ rfl hK).1.mpr hIR'⟩
  · rw [hF_def, hF_def]
    simp

/-- Item `C/04_R/disp/022` (`companion/chapters/04_R.tex:169-172`): the derivative-free central
condition (equation `R:eq:central`):
for every $\eta>0$ there are $M_\eta$ and $\theta\in(0,1/2]$ with
$F(x_*+(1+t)r)+F(x_*+(1-t)r)-2F(x_*+r)\le M_\eta t^2$ for $0\le t\le\theta$ whenever the outer
point stays in $K=\{F\le b\}$ and the inner point is on the $\eta$-band. -/
def Central {n : ℕ} (F : Vec n → ℝ) (xstar : Vec n) (b : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ M θ : ℝ, 0 < θ ∧ θ ≤ 1 / 2 ∧
    ∀ r : Vec n, ∀ t : ℝ, 0 ≤ t → t ≤ θ →
      F (xstar + (1 + t) • r) ≤ b → F xstar + η ≤ F (xstar + (1 - t) • r) →
      F (xstar + (1 + t) • r) + F (xstar + (1 - t) • r) - 2 * F (xstar + r) ≤ M * t ^ 2

theorem Central_iff_library {n : ℕ} (F : Vec n → ℝ) (xstar : Vec n) (b : ℝ) :
    Central F xstar b ↔ RadialCertificate.HasNestedCentralBounds F xstar b := by
  have ho : ∀ (x : Vec n) (t : ℝ), RadialCertificate.outwardPoint xstar x t =
      xstar + (1 + t) • (x - xstar) := fun x t => by
    unfold RadialCertificate.outwardPoint RadialCertificate.inwardPoint; module
  have hi : ∀ (x : Vec n) (t : ℝ), RadialCertificate.inwardPoint xstar x t =
      xstar + (1 - t) • (x - xstar) := fun x t => by
    unfold RadialCertificate.inwardPoint; module
  constructor
  · intro h η hη
    obtain ⟨M, θ, hθ, hθ', hM⟩ := h η hη
    refine ⟨M, θ, hθ, hθ', fun x t h0 h1 hout hin => ?_⟩
    rw [ho] at hout
    rw [hi] at hin
    have := hM (x - xstar) t h0 h1 hout hin
    unfold RadialCertificate.centralDifference
    rw [ho, hi]
    simpa using this
  · intro h η hη
    obtain ⟨M, θ, hθ, hθ', hM⟩ := h η hη
    refine ⟨M, θ, hθ, hθ', fun r t h0 h1 hout hin => ?_⟩
    have hx : (xstar + r) - xstar = r := by abel
    have := hM (xstar + r) t h0 h1 (by rw [ho, hx]; exact hout) (by rw [hi, hx]; exact hin)
    unfold RadialCertificate.centralDifference at this
    rw [ho, hi, hx] at this
    exact this

/-- Item `C/04_R/disp/022`, equation `R:eq:central` (`companion/chapters/04_R.tex:169-172`): "On
slightly nested positive bands where both dilations remain in $K$, an equivalent function-value
formulation is a uniform bound
\[ F(x_*+(1+t)r)+F(x_*+(1-t)r)-2F(x_*+r)\le M_\eta t^2." \]
For finite convex $F$ with minimizer $x_*$: (RS) on a compact sublevel $\{F\le b\}$, $b>F_*$,
gives the central bound at the level $b$; the central bound at the level $b$ gives (IR) and (RS)
on every smaller sublevel $\{F\le b'\}$, $b'<b$ ("a local equivalence with constants allowed to
change", line 177); hence a compact positive sublevel with (RS) exists exactly when one with the
central bound exists. The bound is `Central` (the library's `HasNestedCentralBounds`,
`Central_iff_library`). -/
theorem central_equivalence {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F) (xstar : Vec n)
    (hmin : ∀ x, F xstar ≤ F x) :
    (∀ b : ℝ, F xstar < b → IsCompact {x | F x ≤ b} → RS F xstar {x | F x ≤ b} →
      Central F xstar b) ∧
    (∀ b b' : ℝ, b' < b → IsCompact {x | F x ≤ b} → Central F xstar b →
      IR F xstar {x | F x ≤ b'} ∧ RS F xstar {x | F x ≤ b'}) ∧
    ((∃ b : ℝ, F xstar < b ∧ IsCompact {x | F x ≤ b} ∧ RS F xstar {x | F x ≤ b}) ↔
      (∃ b : ℝ, F xstar < b ∧ IsCompact {x | F x ≤ b} ∧ Central F xstar b)) := by
  refine ⟨fun b hb _ hRS => ?_, fun b b' hbb hK hC => ?_, ?_⟩
  · rw [Central_iff_library]
    exact RadialCertificate.central_of_radial_on_sublevel hF xstar hmin b hb
      ((RS_iff_library F xstar _).mp hRS)
  · rw [Central_iff_library] at hC
    rw [IR_iff_library, RS_iff_library]
    exact ⟨RadialCertificate.inward_of_central_on_smaller_sublevel hF xstar hmin b b' hbb hK hC,
      RadialCertificate.radial_of_central_on_smaller_sublevel hF xstar hmin b b' hbb hK hC⟩
  · have h := RadialCertificate.local_radial_iff_nested_central hF xstar hmin
    simp only [← RS_iff_library, ← Central_iff_library] at h
    exact h


/-- Values along a radial triple: with $t>0$ and the inner point on a positive band, the values
strictly increase from the inner to the middle to the outer point. -/
theorem triple_order {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F) (xstar : Vec n)
    (hmin : ∀ x, F xstar ≤ F x) (r : Vec n) {t η : ℝ} (ht0 : 0 < t) (ht : t ≤ 1 / 2) (hη : 0 < η)
    (hin : F xstar + η ≤ F (xstar + (1 - t) • r)) :
    F (xstar + (1 - t) • r) < F (xstar + r) ∧ F (xstar + r) < F (xstar + (1 + t) • r) := by
  have hi : xstar + (1 - t) • r = (xstar + r) - t • ((xstar + r) - xstar) := by module
  have hm : xstar + r =
      (xstar + (1 + t) • r) - (t / (1 + t)) • ((xstar + (1 + t) • r) - xstar) := by
    have h1t : (1 + t) ≠ 0 := by linarith
    have : (t / (1 + t)) • ((xstar + (1 + t) • r) - xstar) = t • r := by
      rw [show (xstar + (1 + t) • r) - xstar = (1 + t) • r by abel, smul_smul,
        div_mul_cancel₀ _ h1t]
    rw [this]; module
  have hxm : F xstar < F (xstar + r) := by
    refine lt_of_not_ge (fun hle => ?_)
    have := RadialCertificate.inward_value_le hF xstar hmin (xstar + r) ht0.le (by linarith)
    rw [show RadialCertificate.inwardPoint xstar (xstar + r) t = xstar + (1 - t) • r by
      unfold RadialCertificate.inwardPoint; module] at this
    linarith
  have h1 : F (xstar + (1 - t) • r) < F (xstar + r) := by
    rw [hi]; exact inward_lt hF xstar _ hxm ht0 (by linarith)
  refine ⟨h1, ?_⟩
  have hxo : F xstar < F (xstar + (1 + t) • r) := by
    refine lt_of_not_ge (fun hle => ?_)
    have := RadialCertificate.inward_value_le hF xstar hmin (xstar + (1 + t) • r)
      (t := t / (1 + t)) (by positivity) (by rw [div_le_one (by linarith)]; linarith)
    unfold RadialCertificate.inwardPoint at this
    rw [← hm] at this
    linarith
  rw [hm]
  exact inward_lt hF xstar _ hxo (by positivity) (by rw [div_le_one (by linarith)]; linarith)

/-- Item `C/04_R/disp/023` (`companion/chapters/04_R.tex:174-176`): "Conversely, apply (RS) to
the outer/middle and middle/inner radial pairs. If $a_+$ and $a_-$ are their scalar derivative
differences in direction $r$, then
\[ a_+\le Ct,\qquad a_-\le Ct/(1-t)^2." \]
Standing assumptions: the setting, (RS) with a constant $C$ on the $\eta$-band (`hC`), a radial
triple $x_*+(1+t)r$, $x_*+r$, $x_*+(1-t)r$ with $0\le t\le1/2$, outer point in $K$, inner point on
the $\eta$-band, all three differentiable with gradients $g_o,g_m,g_i$;
$a_+=(g_o-g_m)^Tr$, $a_-=(g_m-g_i)^Tr$. The degenerate case $a_\pm=0<t$ uses $C\ge0$
(`rs_constant_nonneg`, with the middle point strictly inside the band). -/
theorem radial_pair_bounds {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F) (xstar : Vec n)
    (hmin : ∀ x, F xstar ≤ F x) (b : ℝ) (_hb : F xstar < b) (K : Set (Vec n))
    (hK_def : K = {x | F x ≤ b}) (hK : IsCompact K) (_hRS : RS F xstar K) (η : ℝ) (hη : 0 < η)
    (C : ℝ) (hC : ∀ x z g h : Vec n, x ∈ K → z ∈ K →
      HasFDerivAt F (gradientFunctional g) x → HasFDerivAt F (gradientFunctional h) z →
      F xstar + η ≤ F z → F z ≤ F x → 0 < dot (h - g) (z - x) →
      (dot (h - g) (z - xstar)) ^ 2 ≤ C * dot (h - g) (z - x))
    (r : Vec n) (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2)
    (hout : F (xstar + (1 + t) • r) ≤ b) (hin : F xstar + η ≤ F (xstar + (1 - t) • r))
    (go gm gi : Vec n) (hgo : HasFDerivAt F (gradientFunctional go) (xstar + (1 + t) • r))
    (hgm : HasFDerivAt F (gradientFunctional gm) (xstar + r))
    (hgi : HasFDerivAt F (gradientFunctional gi) (xstar + (1 - t) • r))
    (ap am : ℝ) (hap : ap = dot (go - gm) r) (ham : am = dot (gm - gi) r) :
    ap ≤ C * t ∧ am ≤ C * t / (1 - t) ^ 2 := by
  rcases eq_or_lt_of_le ht0 with h0 | h0
  · subst h0
    have h1 : xstar + (1 + (0 : ℝ)) • r = xstar + r := by simp
    have h2 : xstar + (1 - (0 : ℝ)) • r = xstar + r := by simp
    rw [h1] at hgo
    rw [h2] at hgi
    rw [hap, ham, gradient_unique hgo hgm, gradient_unique hgi hgm]
    simp [dot]
  obtain ⟨hlt1, hlt2⟩ := triple_order hF xstar hmin r h0 ht hη hin
  have hoK : xstar + (1 + t) • r ∈ K := by rw [hK_def]; exact hout
  have hmK : xstar + r ∈ K := by rw [hK_def]; exact (le_of_lt hlt2).trans hout
  have hiK : xstar + (1 - t) • r ∈ K := by rw [hK_def]; exact (hlt1.trans hlt2).le.trans hout
  have hC0 : 0 ≤ C := rs_constant_nonneg hF xstar b K hK_def hK η C hη hC (xstar + r)
    (by linarith) (by linarith)
  -- outer/middle pair
  have hTo : dot (gm - go) ((xstar + r) - (xstar + (1 + t) • r)) = t * ap := by
    rw [show (xstar + r) - (xstar + (1 + t) • r) = (-t) • r by module, dot_smul_right, hap,
      dot_sub_left, dot_sub_left]
    ring
  have hNo : dot (gm - go) ((xstar + r) - xstar) = -ap := by
    rw [show (xstar + r) - xstar = r by abel, hap, dot_sub_left, dot_sub_left]
    ring
  have hEo := error_le_curvature hF hgo hgm
  rw [hTo] at hEo
  have hap0 : 0 ≤ ap := by nlinarith [hEo.1, hEo.2]
  -- middle/inner pair
  have hTi : dot (gi - gm) ((xstar + (1 - t) • r) - (xstar + r)) = t * am := by
    rw [show (xstar + (1 - t) • r) - (xstar + r) = (-t) • r by module, dot_smul_right, ham,
      dot_sub_left, dot_sub_left]
    ring
  have hNi : dot (gi - gm) ((xstar + (1 - t) • r) - xstar) = -(1 - t) * am := by
    rw [show (xstar + (1 - t) • r) - xstar = (1 - t) • r by abel, dot_smul_right, ham,
      dot_sub_left, dot_sub_left]
    ring
  have hEi := error_le_curvature hF hgm hgi
  rw [hTi] at hEi
  have ham0 : 0 ≤ am := by nlinarith [hEi.1, hEi.2]
  constructor
  · rcases eq_or_lt_of_le hap0 with hz | hz
    · rw [← hz]; positivity
    · have hT : 0 < dot (gm - go) ((xstar + r) - (xstar + (1 + t) • r)) := by
        rw [hTo]; positivity
      have hrs := hC _ _ go gm hoK hmK hgo hgm (by linarith) hlt2.le hT
      rw [hTo, hNo] at hrs
      nlinarith
  · rcases eq_or_lt_of_le ham0 with hz | hz
    · rw [← hz]; positivity
    · have hT : 0 < dot (gi - gm) ((xstar + (1 - t) • r) - (xstar + r)) := by
        rw [hTi]; positivity
      have hrs := hC _ _ gm gi hmK hiK hgm hgi hin hlt1.le hT
      rw [hTi, hNi] at hrs
      have h1t : 0 < (1 - t) ^ 2 := by nlinarith
      rw [le_div_iff₀ h1t]
      nlinarith

/-- Proof of the equivalence `R:eq:central`, undisplayed claim of line 177 (not a register
item): "The central difference is at most $t(a_++a_-)\le5Ct^2$ for $t\le1/2$." Under the
standing assumptions of display `disp/023`. -/
theorem central_le_five {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F) (xstar : Vec n)
    (hmin : ∀ x, F xstar ≤ F x) (b : ℝ) (_hb : F xstar < b) (K : Set (Vec n))
    (hK_def : K = {x | F x ≤ b}) (hK : IsCompact K) (_hRS : RS F xstar K) (η : ℝ) (hη : 0 < η)
    (C : ℝ) (hC : ∀ x z g h : Vec n, x ∈ K → z ∈ K →
      HasFDerivAt F (gradientFunctional g) x → HasFDerivAt F (gradientFunctional h) z →
      F xstar + η ≤ F z → F z ≤ F x → 0 < dot (h - g) (z - x) →
      (dot (h - g) (z - xstar)) ^ 2 ≤ C * dot (h - g) (z - x))
    (r : Vec n) (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2)
    (hout : F (xstar + (1 + t) • r) ≤ b) (hin : F xstar + η ≤ F (xstar + (1 - t) • r))
    (go gm gi : Vec n) (hgo : HasFDerivAt F (gradientFunctional go) (xstar + (1 + t) • r))
    (hgm : HasFDerivAt F (gradientFunctional gm) (xstar + r))
    (hgi : HasFDerivAt F (gradientFunctional gi) (xstar + (1 - t) • r))
    (ap am : ℝ) (hap : ap = dot (go - gm) r) (ham : am = dot (gm - gi) r) :
    F (xstar + (1 + t) • r) + F (xstar + (1 - t) • r) - 2 * F (xstar + r) ≤ t * (ap + am) ∧
      t * (ap + am) ≤ 5 * C * t ^ 2 := by
  have hbd := radial_pair_bounds hF xstar hmin b _hb K hK_def hK _hRS η hη C hC r t ht0 ht hout hin
    go gm gi hgo hgm hgi ap am hap ham
  have hEo := (error_le_curvature hF hgm hgo).2
  have hEi := (error_le_curvature hF hgm hgi).2
  have e1 : (xstar + (1 + t) • r) - (xstar + r) = t • r := by module
  have e2 : (xstar + (1 - t) • r) - (xstar + r) = (-t) • r := by module
  rw [e1, dot_smul_right, dot_smul_right] at hEo
  rw [e2, dot_smul_right, dot_smul_right] at hEi
  have hap' : dot (go - gm) r = ap := hap.symm
  have ham' : dot (gi - gm) r = -am := by rw [ham, dot_sub_left, dot_sub_left]; ring
  rw [hap'] at hEo
  rw [ham'] at hEi
  constructor
  · nlinarith
  · rcases eq_or_lt_of_le ht0 with h0 | h0
    · rw [← h0]; simp
    obtain ⟨hlt1, hlt2⟩ := triple_order hF xstar hmin r h0 ht hη hin
    have hC0 : 0 ≤ C := rs_constant_nonneg hF xstar b K hK_def hK η C hη hC (xstar + r)
      (by linarith) (by rw [hK_def] at *; linarith)
    have h1t : (1 / 4 : ℝ) ≤ (1 - t) ^ 2 := by nlinarith
    have ham4 : am ≤ 4 * C * t := by
      have h2 := hbd.2
      rw [le_div_iff₀ (by nlinarith)] at h2
      nlinarith [mul_le_mul_of_nonneg_left h1t (mul_nonneg hC0 h0.le)]
    nlinarith [hbd.1]

/-- A compact sublevel $\{F\le b\}$, $b>F_*$, is left along every ray from $x_*$. -/
theorem exists_ray_exit {n : ℕ} {F : Vec n → ℝ} (xstar : Vec n) (b : ℝ) (K : Set (Vec n))
    (hK_def : K = {x | F x ≤ b}) (hK : IsCompact K) (e : Vec n) (he : e ≠ 0) :
    ∃ S : ℝ, 0 < S ∧ b < F (xstar + S • e) := by
  obtain ⟨Mb, hMb⟩ := hK.isBounded.exists_norm_le
  have hepos : 0 < ‖e‖ := norm_pos_iff.mpr he
  refine ⟨(|Mb| + ‖xstar‖ + 1) / ‖e‖, by positivity, ?_⟩
  refine lt_of_not_ge (fun hle => ?_)
  have hmem : xstar + ((|Mb| + ‖xstar‖ + 1) / ‖e‖) • e ∈ K := by rw [hK_def]; exact hle
  have h1 := hMb _ hmem
  have h3 : ‖((|Mb| + ‖xstar‖ + 1) / ‖e‖) • e‖ ≤
      ‖xstar‖ + ‖xstar + ((|Mb| + ‖xstar‖ + 1) / ‖e‖) • e‖ := by
    calc ‖((|Mb| + ‖xstar‖ + 1) / ‖e‖) • e‖ =
        ‖(xstar + ((|Mb| + ‖xstar‖ + 1) / ‖e‖) • e) - xstar‖ := by congr 1; abel
      _ ≤ ‖xstar + ((|Mb| + ‖xstar‖ + 1) / ‖e‖) • e‖ + ‖xstar‖ := norm_sub_le _ _
      _ = _ := add_comm _ _
  rw [norm_smul, Real.norm_of_nonneg (by positivity), div_mul_cancel₀ _ hepos.ne'] at h3
  linarith [le_abs_self Mb]

/-- Item `C/04_R/prose/020` (`companion/chapters/04_R.tex:177`): "an outward point need not
remain in the original top boundary of $K$." In the setting: for every $x$ on the top level
$F(x)=b$ and every $t>0$, convexity gives
$F(x_*+(1+t)r_x)\ge F(x)+t(F(x)-F_*)>b$, so the outward point leaves $K$; and for $n\ge1$ such
top-level points exist. -/
theorem outward_leaves_K {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F) (xstar : Vec n)
    (_hmin : ∀ x, F xstar ≤ F x) (b : ℝ) (hb : F xstar < b) (K : Set (Vec n))
    (hK_def : K = {x | F x ≤ b}) (hK : IsCompact K) :
    (∀ x : Vec n, F x = b → ∀ t : ℝ, 0 < t →
      F x + t * (F x - F xstar) ≤ F (xstar + (1 + t) • (x - xstar)) ∧
        b < F (xstar + (1 + t) • (x - xstar))) ∧
      (1 ≤ n → ∃ x ∈ K, F x = b) := by
  refine ⟨fun x hx t ht => ?_, fun hn => ?_⟩
  · have hxo : x = (1 / (1 + t)) • (xstar + (1 + t) • (x - xstar)) + (t / (1 + t)) • xstar := by
      have h1t : (1 + t) ≠ 0 := by linarith
      rw [smul_add, smul_smul, one_div, inv_mul_cancel₀ h1t, one_smul]
      have ht' : t / (1 + t) = 1 - (1 + t)⁻¹ := by field_simp
      rw [ht']
      module
    have hc := hF.2 (mem_univ (xstar + (1 + t) • (x - xstar))) (mem_univ xstar)
      (by positivity : (0 : ℝ) ≤ 1 / (1 + t)) (by positivity : (0 : ℝ) ≤ t / (1 + t))
      (by field_simp)
    rw [← hxo] at hc
    simp only [smul_eq_mul] at hc
    have h1t : 0 < 1 + t := by linarith
    have key : (1 + t) * F x ≤ F (xstar + (1 + t) • (x - xstar)) + t * F xstar := by
      have := mul_le_mul_of_nonneg_left hc h1t.le
      field_simp at this
      linarith
    constructor
    · linarith
    · nlinarith
  · have he : (Pi.single (⟨0, hn⟩ : Fin n) (1 : ℝ) : Vec n) ≠ 0 := by
      intro h0
      have := congrFun h0 ⟨0, hn⟩
      simp at this
    obtain ⟨S, hS, hSb⟩ := exists_ray_exit xstar b K hK_def hK _ he
    have hc : ContinuousOn
        (fun s : ℝ => F (xstar + s • (Pi.single (⟨0, hn⟩ : Fin n) (1 : ℝ) : Vec n))) (Icc 0 S) :=
      ((convex_continuous hF).comp
        (continuous_const.add (continuous_id.smul continuous_const))).continuousOn
    have hmem : b ∈ Icc (F (xstar + (0 : ℝ) • (Pi.single (⟨0, hn⟩ : Fin n) (1 : ℝ) : Vec n)))
        (F (xstar + S • (Pi.single (⟨0, hn⟩ : Fin n) (1 : ℝ) : Vec n))) := by
      simp only [zero_smul, add_zero]
      exact ⟨hb.le, hSb.le⟩
    obtain ⟨s, -, hs⟩ := intermediate_value_Icc hS.le hc hmem
    exact ⟨_, by rw [hK_def]; exact hs.le, hs⟩


/-! ### Section 4.3: the height of the supporting plane at the optimizer (lines 187-230)

$b_F(x)=\nabla F(x)^Tr_x-(F(x)-F_*)$ is the library's `optimizerIntercept F xstar x g`. -/

/-- Item `C/04_R/disp/024` (`companion/chapters/04_R.tex:189-192`): "Define, at a differentiable
point,
\[ b_F(x)=F_*-\bigl[F(x)+\nabla F(x)^T(x_*-x)\bigr]=\nabla F(x)^Tr_x-(F(x)-F_*)\ge0." \]
$b_F(x)$ is a variable with its first defining expression; the claims are the second expression
and the sign (convexity; the minimality of $x_*$ is not used). It is the library's
`optimizerIntercept`. -/
theorem intercept_def {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F) (xstar : Vec n)
    (_hmin : ∀ x, F xstar ≤ F x) (x g : Vec n) (hg : HasFDerivAt F (gradientFunctional g) x)
    (bF : ℝ) (hbF : bF = F xstar - (F x + dot g (xstar - x))) :
    bF = dot g (x - xstar) - (F x - F xstar) ∧ 0 ≤ bF ∧
      bF = RadialCertificate.optimizerIntercept F xstar x g := by
  have he : dot g (xstar - x) = -dot g (x - xstar) := by rw [dot_swap_neg' g xstar x]
  have h1 : bF = dot g (x - xstar) - (F x - F xstar) := by rw [hbF, he]; ring
  refine ⟨h1, ?_, h1⟩
  rw [hbF]
  linarith [convex_supporting_inequality hF hg xstar]

/-- Item `C/04_R/prose/022` (`companion/chapters/04_R.tex:193`): "It is also the supporting
error $D_F(x_*,x)$." $b_F(x)=F(x_*)-F(x)-\nabla F(x)^T(x_*-x)$. -/
theorem intercept_eq_error {n : ℕ} (F : Vec n → ℝ) (xstar x g : Vec n) :
    dot g (x - xstar) - (F x - F xstar) = F xstar - F x - dot g (xstar - x) := by
  have := RadialCertificate.optimizerIntercept_eq_error F xstar x g
  unfold RadialCertificate.optimizerIntercept RadialCertificate.supportingError at this
  exact this

/-- Item `C/04_R/disp/025`, equation `R:eq:intercept` (`companion/chapters/04_R.tex:196-199`):
"A direct calculation gives $N(x,z)=D_F(z,x)+b_F(z)-b_F(x)$", for differentiable $x,z$ with
gradients $g,h$. -/
theorem radial_numerator_intercepts {n : ℕ} (F : Vec n → ℝ) (xstar x z g h : Vec n)
    (_hg : HasFDerivAt F (gradientFunctional g) x) (_hh : HasFDerivAt F (gradientFunctional h) z) :
    dot (h - g) (z - xstar) = (F z - F x - dot g (z - x)) +
      (dot h (z - xstar) - (F z - F xstar)) - (dot g (x - xstar) - (F x - F xstar)) :=
  RadialCertificate.radialNumerator_eq_error_intercepts F xstar x z g h

/-- Item `C/04_R/disp/026` (`companion/chapters/04_R.tex:201-204`): the condition (SP),
\[ |b_F(z)-b_F(x)|^2\le C'T(x,z), \]
for every band $\eta>0$ with a real constant $C'$, on the pairs and bands of (RS). -/
def SP {n : ℕ} (F : Vec n → ℝ) (xstar : Vec n) (K : Set (Vec n)) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ C' : ℝ,
    ∀ x z g h : Vec n, x ∈ K → z ∈ K →
      HasFDerivAt F (gradientFunctional g) x → HasFDerivAt F (gradientFunctional h) z →
      F xstar + η ≤ F z → F z ≤ F x → 0 < dot (h - g) (z - x) →
      |(dot h (z - xstar) - (F z - F xstar)) - (dot g (x - xstar) - (F x - F xstar))| ^ 2 ≤
        C' * dot (h - g) (z - x)

theorem SP_iff_library {n : ℕ} (F : Vec n → ℝ) (xstar : Vec n) (K : Set (Vec n)) :
    SP F xstar K ↔ RadialCertificate.HasInterceptBounds F K xstar := by
  constructor
  · intro h η hη
    obtain ⟨C, hC⟩ := h η hη
    refine ⟨C, fun x z g h hx hz hb ho hg hh ht => ?_⟩
    have := hC x z g h hx hz hg hh hb ho ht
    rw [sq_abs] at this
    exact this
  · intro h η hη
    obtain ⟨C, hC⟩ := h η hη
    refine ⟨C, fun x z g h hx hz hg hh hb ho ht => ?_⟩
    rw [sq_abs]
    exact hC x z g h hx hz hb ho hg hh ht

/-- Item `C/04_R/prose/023` (`companion/chapters/04_R.tex:200`): "Since
$0\le D_F(z,x)\le T\le T_{\max}$, the radial condition is equivalent on the same bounded domains
to [(SP)]." In the setting, (RS) and (SP) are equivalent on the compact sublevel $K$ (the library's
`radial_iff_intercept_on_compact`, whose proof is the stated one: `error_le_curvature`,
`curvature_split`, `radial_numerator_intercepts`). -/
theorem rs_iff_sp {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F) (xstar : Vec n)
    (_hmin : ∀ x, F xstar ≤ F x) (b : ℝ) (_hb : F xstar < b) (K : Set (Vec n))
    (_hK_def : K = {x | F x ≤ b}) (hK : IsCompact K) :
    RS F xstar K ↔ SP F xstar K := by
  rw [RS_iff_library, SP_iff_library]
  exact RadialCertificate.radial_iff_intercept_on_compact hF hK xstar

/-- Item `C/04_R/prose/024` (`companion/chapters/04_R.tex:205`): "For example, (RS) with $C$
implies (SP) with $2C+2T_{\max}$, and conversely." For a band $\eta$, in the setting with the
bounds $R,G$ and $T_{\max}=4GR$: if $N^2\le CT$ for all pairs of the band then
$|b_F(z)-b_F(x)|^2\le(2C+2T_{\max})T$ for all of them, and if
$|b_F(z)-b_F(x)|^2\le CT$ for all of them then $N^2\le(2C+2T_{\max})T$. -/
theorem rs_sp_constants {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (xstar : Vec n) (_hmin : ∀ x, F xstar ≤ F x) (b : ℝ) (_hb : F xstar < b)
    (K : Set (Vec n)) (_hK_def : K = {x | F x ≤ b}) (_hK : IsCompact K)
    (R G : ℝ) (hR : 0 < R) (hG : 0 < G)
    (hRK : ∀ x ∈ K, ‖euclideanVector (x - xstar)‖ ≤ R)
    (hGK : ∀ x ∈ K, ∀ v : Vec n, (∀ y, F x + dot v (y - x) ≤ F y) → ‖euclideanVector v‖ ≤ G)
    (η C Tmax : ℝ) (hTmax : Tmax = 4 * G * R) :
    ((∀ x z g h : Vec n, x ∈ K → z ∈ K →
        HasFDerivAt F (gradientFunctional g) x → HasFDerivAt F (gradientFunctional h) z →
        F xstar + η ≤ F z → F z ≤ F x → 0 < dot (h - g) (z - x) →
        (dot (h - g) (z - xstar)) ^ 2 ≤ C * dot (h - g) (z - x)) →
      ∀ x z g h : Vec n, x ∈ K → z ∈ K →
        HasFDerivAt F (gradientFunctional g) x → HasFDerivAt F (gradientFunctional h) z →
        F xstar + η ≤ F z → F z ≤ F x → 0 < dot (h - g) (z - x) →
        |(dot h (z - xstar) - (F z - F xstar)) - (dot g (x - xstar) - (F x - F xstar))| ^ 2 ≤
          (2 * C + 2 * Tmax) * dot (h - g) (z - x)) ∧
    ((∀ x z g h : Vec n, x ∈ K → z ∈ K →
        HasFDerivAt F (gradientFunctional g) x → HasFDerivAt F (gradientFunctional h) z →
        F xstar + η ≤ F z → F z ≤ F x → 0 < dot (h - g) (z - x) →
        |(dot h (z - xstar) - (F z - F xstar)) - (dot g (x - xstar) - (F x - F xstar))| ^ 2 ≤
          C * dot (h - g) (z - x)) →
      ∀ x z g h : Vec n, x ∈ K → z ∈ K →
        HasFDerivAt F (gradientFunctional g) x → HasFDerivAt F (gradientFunctional h) z →
        F xstar + η ≤ F z → F z ≤ F x → 0 < dot (h - g) (z - x) →
        (dot (h - g) (z - xstar)) ^ 2 ≤ (2 * C + 2 * Tmax) * dot (h - g) (z - x)) := by
  have hpair : ∀ x z g h : Vec n, x ∈ K → z ∈ K →
      HasFDerivAt F (gradientFunctional g) x → HasFDerivAt F (gradientFunctional h) z →
      0 ≤ F z - F x - dot g (z - x) ∧ F z - F x - dot g (z - x) ≤ dot (h - g) (z - x) ∧
        dot (h - g) (z - x) ≤ Tmax ∧
        dot (h - g) (z - xstar) - (F z - F x - dot g (z - x)) =
          (dot h (z - xstar) - (F z - F xstar)) - (dot g (x - xstar) - (F x - F xstar)) := by
    intro x z g h hx hz hg hh
    obtain ⟨h1, h2⟩ := error_le_curvature hF hg hh
    have h3 := (curvature_split hF xstar _hmin b _hb K _hK_def _hK R G hR hG hRK hGK x z g h hx hz
      hg hh _ Tmax rfl hTmax).2.2
    have h4 := radial_numerator_intercepts F xstar x z g h hg hh
    exact ⟨h1, h2, h3, by linarith⟩
  constructor
  · intro hRS x z g h hx hz hg hh hb ho ht
    obtain ⟨h1, h2, h3, h4⟩ := hpair x z g h hx hz hg hh
    have := RadialCertificate.intercept_bound_of_radial h1 h2 h3 (hRS x z g h hx hz hg hh hb ho ht)
    rw [h4] at this
    rw [sq_abs]
    exact this
  · intro hSP x z g h hx hz hg hh hb ho ht
    obtain ⟨h1, h2, h3, h4⟩ := hpair x z g h hx hz hg hh
    have hs := hSP x z g h hx hz hg hh hb ho ht
    rw [sq_abs, ← h4] at hs
    exact RadialCertificate.radial_bound_of_intercept h1 h2 h3 hs

/-- Item `C/04_R/prose/025` (`companion/chapters/04_R.tex:205`): "Thus the full gradient need
not be Lipschitz; only the \emph{height at the optimizer} of its supporting plane needs this
curvature-relative regularity." The benchmark $F(u,v)=u^2+|v|$, $x_*=0$, satisfies (SP) on every
compact sublevel $\{F\le b\}$, $b>0$, but its gradient is not Lipschitz there: no $L$ satisfies
$\|\nabla F(y)-\nabla F(x)\|\le L\|y-x\|$ for all differentiable $x,y$ in the sublevel
(Euclidean norms). -/
theorem sp_without_lipschitz_gradient (F : Vec 2 → ℝ) (hF_def : ∀ x, F x = (x 0) ^ 2 + |x 1|) :
    ∀ b : ℝ, 0 < b → SP F 0 {x | F x ≤ b} ∧
      ¬ ∃ L : ℝ, ∀ x y g h : Vec 2, F x ≤ b → F y ≤ b →
        HasFDerivAt F (gradientFunctional g) x → HasFDerivAt F (gradientFunctional h) y →
        ‖euclideanVector (h - g)‖ ≤ L * ‖euclideanVector (y - x)‖ := by
  intro b hb
  obtain ⟨hmin, -, hsub⟩ := Article.Global.mixed_inward_condition F hF_def
  obtain ⟨hconv, -⟩ := Article.Global.mixed_hypotheses F hF_def
  have hF0 : F 0 = 0 := by simp [hF_def]
  obtain ⟨hK, -, hRS⟩ := (angular_jump F hF_def).1 b hb
  refine ⟨(rs_iff_sp hconv 0 hmin b (by rw [hF0]; exact hb) _ rfl hK).mp hRS, ?_⟩
  rintro ⟨L, hL⟩
  obtain rfl : F = UnexcitedMetric.objective := funext hF_def
  set ε := min (b / 2) (1 / (2 * (|L| + 1))) with hε
  have hε0 : 0 < ε := lt_min (by positivity) (by positivity)
  have hεb : ε ≤ b / 2 := min_le_left _ _
  have hεL : ε * (2 * (|L| + 1)) ≤ 1 := by
    have := min_le_right (b / 2) (1 / (2 * (|L| + 1)))
    rw [← hε] at this
    rwa [le_div_iff₀ (by positivity)] at this
  have hg1 := ArticleGeometry.mixed_ridge_gradient (u := 0) (v := ε) hε0.ne'
  have hg2 := ArticleGeometry.mixed_ridge_gradient (u := 0) (v := -ε) (by linarith)
  rw [Real.sign_of_pos hε0] at hg1
  rw [Real.sign_of_neg (by linarith)] at hg2
  have hF1 : UnexcitedMetric.objective ![0, ε] ≤ b := by
    rw [hF_def]; simp [abs_of_pos hε0]; linarith
  have hF2 : UnexcitedMetric.objective ![0, -ε] ≤ b := by
    rw [hF_def]; simp [abs_of_pos hε0]; linarith
  have h := hL _ _ _ _ hF1 hF2 hg1 hg2
  have hn1 : ‖euclideanVector (![2 * 0, -1] - ![2 * 0, 1] : Vec 2)‖ = 2 := by
    rw [Article.Global.norm_euclideanVector]
    simp [sqNorm, Fin.sum_univ_two]
    rw [show ((-1 : ℝ) - 1) ^ 2 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hn2 : ‖euclideanVector (![0, -ε] - ![0, ε] : Vec 2)‖ = 2 * ε := by
    rw [Article.Global.norm_euclideanVector]
    simp [sqNorm, Fin.sum_univ_two]
    rw [show (-ε - ε) ^ 2 = (2 * ε) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  rw [hn1, hn2] at h
  have : L * (2 * ε) ≤ |L| * (2 * ε) := mul_le_mul_of_nonneg_right (le_abs_self L) (by positivity)
  nlinarith


/-- Item `C/04_R/prose/027` (`companion/chapters/04_R.tex:207`): "For a degree-one homogeneous
function minimized at zero, $b_F\equiv0$." For finite convex positively homogeneous $F$ of degree
one with minimizer $x_*=0$: $b_F(x)=\nabla F(x)^Tx-(F(x)-F(0))=0$ at every differentiable $x$. -/
theorem homogeneous_intercept_zero {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (hh : Homogeneous.PositiveDegreeOne F) (_hmin : ∀ x, F 0 ≤ F x) (x g : Vec n)
    (hg : HasFDerivAt F (gradientFunctional g) x) :
    dot g (x - 0) - (F x - F 0) = 0 :=
  InterceptExamples.homogeneous_intercept_zero hF hh hg

/-- Item `C/04_R/prose/028` (`companion/chapters/04_R.tex:211`), with its display
`C/04_R/disp/027` (lines 208-210): "For $F(u,v)=u^2+|v|$, we have $b_F(u,v)=u^2$: crossing $v=0$
flips a gradient component but does not produce a jump in this scalar." Here $x_*=0$, and $(u,v)$
is `x : Vec 2` with $u=x_0$, $v=x_1$: at every differentiable point $b_F(x)=x_0^2$; on either
side of $v=0$ the gradient is $(2u,\pm1)$ while $b_F=u^2$ on both. -/
theorem benchmark_intercept (F : Vec 2 → ℝ) (hF_def : ∀ x, F x = (x 0) ^ 2 + |x 1|) :
    (∀ x g : Vec 2, HasFDerivAt F (gradientFunctional g) x →
      dot g (x - 0) - (F x - F 0) = (x 0) ^ 2) ∧
    ∀ u v : ℝ, 0 < v →
      HasFDerivAt F (gradientFunctional ![2 * u, 1]) ![u, v] ∧
        HasFDerivAt F (gradientFunctional ![2 * u, -1]) ![u, -v] ∧
        dot ![2 * u, 1] (![u, v] - 0) - (F ![u, v] - F 0) = u ^ 2 ∧
        dot ![2 * u, -1] (![u, -v] - 0) - (F ![u, -v] - F 0) = u ^ 2 := by
  obtain rfl : F = UnexcitedMetric.objective := funext hF_def
  have hall : ∀ x g : Vec 2, HasFDerivAt UnexcitedMetric.objective (gradientFunctional g) x →
      dot g (x - 0) - (UnexcitedMetric.objective x - UnexcitedMetric.objective 0) = (x 0) ^ 2 :=
    fun x g hg => InterceptExamples.quadratic_absolute_intercept hg
  refine ⟨hall, fun u v hv => ?_⟩
  have h1 := ArticleGeometry.mixed_ridge_gradient (u := u) (v := v) hv.ne'
  have h2 := ArticleGeometry.mixed_ridge_gradient (u := u) (v := -v) (by linarith)
  rw [Real.sign_of_pos hv] at h1
  rw [Real.sign_of_neg (by linarith)] at h2
  exact ⟨h1, h2, by simpa using hall _ _ h1, by simpa using hall _ _ h2⟩

/-- Item `C/04_R/prose/032` (`companion/chapters/04_R.tex:217`): "We use homogeneity under
nonnegative dilations, $F(tx)=t^pF(x)$ for $t\ge0$, with $t^0=1$ also at $t=0$." The library's
`InterceptExamples.PositiveDegree p F`, with the real power `t ^ p` (`Real.rpow`), for which
$0^0=1$. -/
theorem positiveDegree_def {n : ℕ} (p : ℝ) (F : Vec n → ℝ) :
    (InterceptExamples.PositiveDegree p F ↔ ∀ t : ℝ, 0 ≤ t → ∀ x, F (t • x) = t ^ p * F x) ∧
      (0 : ℝ) ^ (0 : ℝ) = 1 :=
  ⟨Iff.rfl, Real.rpow_zero 0⟩

/-- Item `C/04_R/prose/029` (`companion/chapters/04_R.tex:213`): "For a function homogeneous of
degree $p$, Euler's identity at a differentiable point is $\nabla F(x)^Tx=pF(x)$." -/
theorem euler_identity {n : ℕ} {F : Vec n → ℝ} {p : ℝ}
    (hh : ∀ t : ℝ, 0 ≤ t → ∀ x, F (t • x) = t ^ p * F x) (x g : Vec n)
    (hg : HasFDerivAt F (gradientFunctional g) x) : dot g x = p * F x :=
  InterceptExamples.degree_euler hh hg

/-- Item `C/04_R/disp/028` (`companion/chapters/04_R.tex:214-216`): "Consequently the
supporting-plane error at an arbitrary reference point $x_*$ is
\[ b_{F,x_*}(x)=(p-1)F(x)+F(x_*)-\nabla F(x)^Tx_*." \]
For $F$ homogeneous of degree $p$ and any point $x_*$ (no minimizer assumption, line 217), with
$b_{F,x_*}(x)=\nabla F(x)^T(x-x_*)-(F(x)-F(x_*))$. -/
theorem degree_intercept_at_reference {n : ℕ} {F : Vec n → ℝ} {p : ℝ}
    (hh : ∀ t : ℝ, 0 ≤ t → ∀ x, F (t • x) = t ^ p * F x) (xstar x g : Vec n)
    (hg : HasFDerivAt F (gradientFunctional g) x) :
    dot g (x - xstar) - (F x - F xstar) = (p - 1) * F x + F xstar - dot g xstar :=
  OriginalClaimInterpretation.degree_intercept_at_reference hh xstar hg

/-- Item `C/04_R/prose/031` (`companion/chapters/04_R.tex:217`): "At reference zero it reduces
to $(p-1)F(x)+F(0)$; the constant term cannot be discarded without a normalization." For $F$
homogeneous of degree $p$: $b_{F,0}(x)=(p-1)F(x)+F(0)$; and the positive constant $F\equiv1$ on
$\R^1$, homogeneous of degree $0$, has $b_{F,0}(x)=0\ne(0-1)F(x)$. -/
theorem reference_zero_intercept :
    (∀ (n : ℕ) (F : Vec n → ℝ) (p : ℝ), (∀ t : ℝ, 0 ≤ t → ∀ x, F (t • x) = t ^ p * F x) →
      ∀ x g : Vec n, HasFDerivAt F (gradientFunctional g) x →
        dot g (x - 0) - (F x - F 0) = (p - 1) * F x + F 0) ∧
      ∃ F : Vec 1 → ℝ, (∀ t : ℝ, 0 ≤ t → ∀ x, F (t • x) = t ^ (0 : ℝ) * F x) ∧
        ∀ x : Vec 1, HasFDerivAt F (gradientFunctional 0) x ∧
          dot 0 (x - 0) - (F x - F 0) ≠ ((0 : ℝ) - 1) * F x := by
  refine ⟨fun n F p hh x g hg => InterceptExamples.degree_intercept_with_zero_value hh hg,
    fun _ => 1, OriginalClaimInterpretation.positive_constant_homogeneous, fun x =>
    ⟨OriginalClaimInterpretation.positive_constant_derivative x, ?_⟩⟩
  have := OriginalClaimInterpretation.unrestricted_zero_degree_formula_fails x
  unfold RadialCertificate.optimizerIntercept at this
  exact this

/-- Item `C/04_R/prose/033` (`companion/chapters/04_R.tex:217`): "Thus degree zero forces $F$
to be constant." -/
theorem degree_zero_constant {n : ℕ} {F : Vec n → ℝ}
    (hh : ∀ t : ℝ, 0 ≤ t → ∀ x, F (t • x) = t ^ (0 : ℝ) * F x) (x : Vec n) : F x = F 0 :=
  OriginalClaimInterpretation.degree_zero_constant hh x

/-- Item `C/04_R/prose/035` (`companion/chapters/04_R.tex:219`): "More precisely, let $n\ge1$,
let $F:\mathbb R^n\to\mathbb R$ be finite, convex, nonnegative and homogeneous, and suppose
$\{F\le b\}$ is compact with $F(z)<b$ for some $z$. Then $p>0$." -/
theorem compact_positive_degree {n : ℕ} (hn : 1 ≤ n) {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (hnonneg : ∀ x, 0 ≤ F x) {p : ℝ} (hh : ∀ t : ℝ, 0 ≤ t → ∀ x, F (t • x) = t ^ p * F x)
    (b : ℝ) (hK : IsCompact {x | F x ≤ b}) (z : Vec n) (hz : F z < b) : 0 < p := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact OriginalClaimInterpretation.compact_nonnegative_homogeneity_positive_degree m hF hnonneg
    hh hz hK

/-- Item `C/04_R/disp/029` (`companion/chapters/04_R.tex:220-223`): "if $p\le0$, homogeneity at
dilation two and midpoint convexity give
\[ F(x)\le\tfrac12F(2x)+\tfrac12F(0)=2^{p-1}F(x)+\tfrac12F(0)." \]
Under the hypotheses of `compact_positive_degree` and the contradiction hypothesis $p\le0$
(not used by the display). -/
theorem midpoint_bound {n : ℕ} (_hn : 1 ≤ n) {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (_hnonneg : ∀ x, 0 ≤ F x) {p : ℝ} (hh : ∀ t : ℝ, 0 ≤ t → ∀ x, F (t • x) = t ^ p * F x)
    (b : ℝ) (_hK : IsCompact {x | F x ≤ b}) (z : Vec n) (_hz : F z < b) (_hp : p ≤ 0)
    (x : Vec n) :
    F x ≤ 1 / 2 * F ((2 : ℝ) • x) + 1 / 2 * F 0 ∧
      1 / 2 * F ((2 : ℝ) • x) + 1 / 2 * F 0 = (2 : ℝ) ^ (p - 1) * F x + 1 / 2 * F 0 := by
  constructor
  · have hc := hF.2 (mem_univ ((2 : ℝ) • x)) (mem_univ (0 : Vec n))
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
    have he : (1 / 2 : ℝ) • ((2 : ℝ) • x) + (1 / 2 : ℝ) • (0 : Vec n) = x := by
      rw [smul_smul, smul_zero, add_zero]; norm_num
    rw [he] at hc
    simpa only [smul_eq_mul] using hc
  · rw [hh 2 (by norm_num) x, Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
    ring

/-- Item `C/04_R/prose/037` (`companion/chapters/04_R.tex:226`): "Positive degree gives
$F(0)=0$. Any optimizer $x_*$ therefore has value zero. If $x_*\ne0$, homogeneity places the
unbounded ray $\{tx_*:t\ge0\}$ inside the compact sublevel, another contradiction. Thus zero is the
unique optimizer". Under the hypotheses of `compact_positive_degree`. -/
theorem compact_homogeneous_optimizer {n : ℕ} (hn : 1 ≤ n) {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (hnonneg : ∀ x, 0 ≤ F x) {p : ℝ}
    (hh : ∀ t : ℝ, 0 ≤ t → ∀ x, F (t • x) = t ^ p * F x)
    (b : ℝ) (hK : IsCompact {x | F x ≤ b}) (z : Vec n) (hz : F z < b) :
    F 0 = 0 ∧ (∀ x, F 0 ≤ F x) ∧ ∀ xs : Vec n, (∀ x, F xs ≤ F x) → F xs = 0 ∧ xs = 0 := by
  have hp := compact_positive_degree hn hF hnonneg hh b hK z hz
  have h0 : F 0 = 0 := InterceptExamples.degree_value_zero hp hh
  refine ⟨h0, fun x => by rw [h0]; exact hnonneg x, fun xs hxs => ?_⟩
  have hv : F xs = 0 := le_antisymm (by rw [← h0]; exact hxs 0) (hnonneg xs)
  refine ⟨hv, ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact OriginalClaimInterpretation.compact_homogeneous_minimizer_eq_zero m hF hnonneg hh hz hK
    (fun x _ => hxs x)

/-- Item `C/04_R/disp/030` (`companion/chapters/04_R.tex:227-229`): "Thus zero is the unique
optimizer and $b_F(x)=(p-1)F(x)$." Under the hypotheses of `compact_positive_degree`, for every
optimizer $x_*$ (no assumption that it is the origin) and every differentiable $x$. -/
theorem compact_homogeneous_intercept {n : ℕ} (hn : 1 ≤ n) {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (hnonneg : ∀ x, 0 ≤ F x) {p : ℝ}
    (hh : ∀ t : ℝ, 0 ≤ t → ∀ x, F (t • x) = t ^ p * F x)
    (b : ℝ) (hK : IsCompact {x | F x ≤ b}) (z : Vec n) (hz : F z < b) (xstar : Vec n)
    (hmin : ∀ x, F xstar ≤ F x) (x g : Vec n) (hg : HasFDerivAt F (gradientFunctional g) x) :
    dot g (x - xstar) - (F x - F xstar) = (p - 1) * F x := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact OriginalClaimInterpretation.compact_homogeneous_optimizer_intercept m hF hnonneg hh hz hK
    (fun x _ => hmin x) hg

/-- Item `C/04_R/prose/038` (`companion/chapters/04_R.tex:230`): "The chapter's hypothesis
$b>F_*$ supplies the strict witness by taking $z=x_*$." -/
theorem strict_witness {n : ℕ} {F : Vec n → ℝ} (xstar : Vec n) (b : ℝ) (hb : F xstar < b) :
    ∃ z, F z < b :=
  ⟨xstar, hb⟩

/-- Item `C/04_R/prose/039` (`companion/chapters/04_R.tex:230`): "Outside this compact context,
the positive constant function $F\equiv1$ has degree zero and intercept zero, whereas $(p-1)F=-1$;
its positive sublevels are noncompact." On $\R^1$: $F\equiv1$ is convex, nonnegative, minimized
everywhere, homogeneous of degree $0$, differentiable with $\nabla F=0$, $b_{F,0}(x)=0$,
$(0-1)F(x)=-1$, and $\{F\le b\}$ is not compact for $b>1=F_*$. -/
theorem constant_counterexample :
    ConvexOn ℝ univ (fun _ : Vec 1 => (1 : ℝ)) ∧ (∀ x : Vec 1, (0 : ℝ) ≤ (fun _ => (1 : ℝ)) x) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ x : Vec 1, (fun _ : Vec 1 => (1 : ℝ)) (t • x) =
        t ^ (0 : ℝ) * (fun _ : Vec 1 => (1 : ℝ)) x) ∧
      (∀ x : Vec 1, HasFDerivAt (fun _ : Vec 1 => (1 : ℝ)) (gradientFunctional 0) x ∧
        dot 0 (x - 0) - ((1 : ℝ) - 1) = 0 ∧ ((0 : ℝ) - 1) * 1 = -1) ∧
      ∀ b : ℝ, 1 < b → ¬ IsCompact {x : Vec 1 | (fun _ : Vec 1 => (1 : ℝ)) x ≤ b} := by
  refine ⟨OriginalClaimInterpretation.positive_constant_convex, fun _ => zero_le_one,
    OriginalClaimInterpretation.positive_constant_homogeneous, fun x =>
      ⟨OriginalClaimInterpretation.positive_constant_derivative x, by simp [dot], by norm_num⟩,
    fun b hb => ?_⟩
  exact OriginalClaimInterpretation.degree_zero_positive_sublevel_not_compact 0
    OriginalClaimInterpretation.positive_constant_homogeneous hb


/-! ### The explicit four-piece realization (lines 232-281)

$F_D$ is the library's `SeedOrbit.coerciveObjective` with the exact algebraic seed parameters
$c,d$ = `SeedOrbit.seedC`, `SeedOrbit.seedD` of Chapter D, and $F_R$ is
`ReconstructedFourPiece.objective`. The constants $\delta$, $a$ and the matrix of $\mathcal L$ are
variables with their defining equations (the library's `gap`, `valueScale`, `coordinate`). The
verified D run with parameters $c_1,c_2$ is `SeedOrbit.coerciveRun`, the transformed run is
`ReconstructedFourPiece.run`. -/

theorem fourPiece_consts (δ a : ℝ) (L : Mat 2) (hδ : δ = SeedOrbit.seedC - 16 * SeedOrbit.seedD - 1)
    (ha : a = 25 / (4 * δ)) (hL : L = !![1, 0; 0, 16 / 5]) :
    δ = ReconstructedFourPiece.gap ∧ a = ReconstructedFourPiece.valueScale ∧
      L = ReconstructedFourPiece.coordinate := by
  refine ⟨by rw [hδ, ReconstructedFourPiece.gap]; ring, ?_, hL⟩
  rw [ha, ReconstructedFourPiece.valueScale, div_div, show δ = ReconstructedFourPiece.gap by
    rw [hδ, ReconstructedFourPiece.gap]; ring]

/-- Item `C/04_R/disp/031` (`companion/chapters/04_R.tex:234-236`): "Let $c,d$ be the exact
algebraic seed parameters of Chapter~D, and let
$F_D(u,v)=\max\{u,-u-v/8,cu+dv,v-17\}$ be its verified coercive four-piece objective." The
library's objective of Chapter D is this maximum; it is finite, convex, coercive, with compact
sublevels. -/
theorem fourPiece_FD :
    (∀ x : Vec 2, SeedOrbit.coerciveObjective x =
      max (max (max (x 0) (-x 0 - x 1 / 8)) (SeedOrbit.seedC * x 0 + SeedOrbit.seedD * x 1))
        (x 1 - 17)) ∧
      ConvexOn ℝ univ SeedOrbit.coerciveObjective ∧
      (∀ b : ℝ, IsCompact {x | SeedOrbit.coerciveObjective x ≤ b}) ∧
      Tendsto SeedOrbit.coerciveObjective (cocompact (Vec 2)) atTop := by
  have hbr : ∀ (i : Fin 4) (x : Vec 2), SeedOrbit.coerciveFamily.branch i x =
      (![x 0, -x 0 - x 1 / 8, SeedOrbit.seedC * x 0 + SeedOrbit.seedD * x 1, x 1 - 17] :
        Vec 4) i := by
    intro i x
    fin_cases i <;>
      simp [SeedOrbit.coerciveFamily, MaxAffine.Family.branch, dot, Fin.sum_univ_two,
        SeedCycle.g0, SeedCycle.g1, SeedCycle.g2] <;> ring
  refine ⟨fun x => le_antisymm ?_ ?_, SeedOrbit.coerciveFamily.objective_convex,
    SeedOrbit.coercive_sublevels_compact,
    AffineWhitening.coercive_of_compact_sublevels SeedOrbit.coercive_sublevels_compact⟩
  · unfold SeedOrbit.coerciveObjective MaxAffine.Family.objective
    apply Finset.sup'_le
    intro i _
    rw [hbr]
    fin_cases i <;> simp
  · have h : ∀ i, SeedOrbit.coerciveFamily.branch i x ≤ SeedOrbit.coerciveObjective x :=
      fun i => SeedOrbit.coerciveFamily.branch_le i x
    simp only [hbr] at h
    have h0 : x 0 ≤ SeedOrbit.coerciveObjective x := by have := h 0; simp at this; linarith
    have h1 : -x 0 - x 1 / 8 ≤ SeedOrbit.coerciveObjective x := by
      have := h 1; simp at this; linarith
    have h2 : SeedOrbit.seedC * x 0 + SeedOrbit.seedD * x 1 ≤ SeedOrbit.coerciveObjective x := by
      have := h 2; simp at this; linarith
    have h3 : x 1 - 17 ≤ SeedOrbit.coerciveObjective x := by have := h 3; simp at this; linarith
    exact max_le (max_le (max_le h0 h1) h2) h3

/-- Item `C/04_R/disp/032` (`companion/chapters/04_R.tex:238-241`): "Define
$\delta=c-16d-1>0$, $a=\frac{25}{4\delta}>0$, $\mathcal L(u,v)=(u,16v/5)$." The matrix of
$\mathcal L$ is $\operatorname{diag}(1,16/5)$; the claims are $\delta>0$, $a>0$ and the formula
for $\mathcal L$. -/
theorem fourPiece_constants (δ a : ℝ) (L : Mat 2)
    (hδ : δ = SeedOrbit.seedC - 16 * SeedOrbit.seedD - 1)
    (ha : a = 25 / (4 * δ)) (hL : L = !![1, 0; 0, 16 / 5]) :
    0 < δ ∧ 0 < a ∧ ∀ z : Vec 2, L *ᵥ z = ![z 0, 16 * z 1 / 5] := by
  obtain ⟨rfl, rfl, rfl⟩ := fourPiece_consts δ a L hδ ha hL
  refine ⟨ReconstructedFourPiece.gap_pos, ReconstructedFourPiece.valueScale_pos, fun z => ?_⟩
  rw [ReconstructedFourPiece.coordinate_apply]
  ext i
  fin_cases i <;> simp; ring

/-- Item `C/04_R/disp/033` (`companion/chapters/04_R.tex:243-245`): the definition
$F_R(z)=aF_D(\mathcal Lz)+a-1$; the library's `ReconstructedFourPiece.objective` (a maximum of
four affine branches) unfolds to it. -/
theorem fourPiece_objective_formula (δ a : ℝ) (L : Mat 2)
    (hδ : δ = SeedOrbit.seedC - 16 * SeedOrbit.seedD - 1)
    (ha : a = 25 / (4 * δ)) (hL : L = !![1, 0; 0, 16 / 5]) (z : Vec 2) :
    ReconstructedFourPiece.objective z = a * SeedOrbit.coerciveObjective (L *ᵥ z) + a - 1 := by
  obtain ⟨rfl, rfl, rfl⟩ := fourPiece_consts δ a L hδ ha hL
  rw [ReconstructedFourPiece.objective_formula]
  ring

/-- Item `C/04_R/disp/034` (`companion/chapters/04_R.tex:247-252`): "Thus $F_R$ is the maximum of
the four affine functions $au+a-1$, $a(-u-2v/5)+a-1$, $a(cu+16dv/5)+a-1$, $16av/5-16a-1$." -/
theorem fourPiece_branches (δ a : ℝ) (L : Mat 2)
    (hδ : δ = SeedOrbit.seedC - 16 * SeedOrbit.seedD - 1)
    (ha : a = 25 / (4 * δ)) (hL : L = !![1, 0; 0, 16 / 5]) (z : Vec 2) :
    ReconstructedFourPiece.objective z =
      max (max (max (a * z 0 + a - 1) (a * (-z 0 - 2 * z 1 / 5) + a - 1))
        (a * (SeedOrbit.seedC * z 0 + 16 * SeedOrbit.seedD * z 1 / 5) + a - 1))
        (16 * a * z 1 / 5 - 16 * a - 1) := by
  have hpos := (fourPiece_constants δ a L hδ ha hL).2.1
  rw [fourPiece_objective_formula δ a L hδ ha hL z, (fourPiece_FD).1,
    (fourPiece_constants δ a L hδ ha hL).2.2 z]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [show ∀ w : ℝ, a * w + a - 1 = a * w + (a - 1) from fun w => by ring,
    mul_max_of_nonneg _ _ hpos.le, mul_max_of_nonneg _ _ hpos.le, mul_max_of_nonneg _ _ hpos.le,
    ← max_add_add_right, ← max_add_add_right, ← max_add_add_right]
  congr 1
  · congr 1
    · congr 1 <;> ring
    · ring
  · ring

/-- Item `C/04_R/prose/042` (`companion/chapters/04_R.tex:253`): "Chapter~D's own optimizer
remains $(-1,16)$." $(-1,16)$ is the unique minimizer of $F_D$, with value $-1$. -/
theorem fourPiece_D_optimizer :
    (∀ x, SeedOrbit.coerciveObjective ![-1, 16] ≤ SeedOrbit.coerciveObjective x) ∧
      SeedOrbit.coerciveObjective ![-1, 16] = -1 ∧
      ∀ x, SeedOrbit.coerciveObjective x = -1 → x = ![-1, 16] := by
  have h := SeedOrbit.coercive_minimum_value
  have he : SeedOrbit.coerciveOptimizer = ![-1, 16] := rfl
  rw [he] at h
  exact ⟨fun x => by rw [h]; exact SeedOrbit.coercive_lower_bound x, h,
    fun x hx => SeedOrbit.coercive_unique_optimizer hx⟩

/-- Item `C/04_R/prose/044` (`companion/chapters/04_R.tex:255`): "Since $\mathcal L$ is
invertible and $a>0$, $F_R$ is finite and convex with compact sublevels." -/
theorem fourPiece_convex_compact (δ a : ℝ) (L : Mat 2)
    (hδ : δ = SeedOrbit.seedC - 16 * SeedOrbit.seedD - 1)
    (ha : a = 25 / (4 * δ)) (hL : L = !![1, 0; 0, 16 / 5]) :
    L.det ≠ 0 ∧ 0 < a ∧ ConvexOn ℝ univ ReconstructedFourPiece.objective ∧
      ∀ b : ℝ, IsCompact {z | ReconstructedFourPiece.objective z ≤ b} := by
  have hpos := (fourPiece_constants δ a L hδ ha hL).2.1
  obtain ⟨-, -, rfl⟩ := fourPiece_consts δ a L hδ ha hL
  exact ⟨ReconstructedFourPiece.coordinate_det_ne, hpos, ReconstructedFourPiece.objective_convex,
    ReconstructedFourPiece.sublevels_compact⟩

/-- Item `C/04_R/prose/045` (`companion/chapters/04_R.tex:255`): "Chapter~\ref{comp:D}'s unique
optimizer $(-1,16)$ is carried to $(-1,5)$, and the minimum value remains $-1$." (Wording point
W22 applied on 15 October 2026; before "The unique D optimizer".) $\mathcal L(-1,5)=(-1,16)$,
$F_R(-1,5)=-1$ is the minimum, attained only at $(-1,5)$. -/
theorem fourPiece_optimizer (δ a : ℝ) (L : Mat 2)
    (hδ : δ = SeedOrbit.seedC - 16 * SeedOrbit.seedD - 1)
    (ha : a = 25 / (4 * δ)) (hL : L = !![1, 0; 0, 16 / 5]) :
    L *ᵥ ![-1, 5] = ![-1, 16] ∧ ReconstructedFourPiece.objective ![-1, 5] = -1 ∧
      (∀ z, ReconstructedFourPiece.objective ![-1, 5] ≤ ReconstructedFourPiece.objective z) ∧
      ∀ z, ReconstructedFourPiece.objective z = -1 → z = ![-1, 5] := by
  obtain ⟨-, -, rfl⟩ := fourPiece_consts δ a L hδ ha hL
  have hm := ReconstructedFourPiece.minimum_value
  have he : ReconstructedFourPiece.optimizer = ![-1, 5] := rfl
  rw [he] at hm
  exact ⟨ReconstructedFourPiece.coordinate_optimizer, hm,
    fun z => by rw [hm]; exact ReconstructedFourPiece.lower_bound z,
    fun z hz => ReconstructedFourPiece.unique_optimizer hz⟩

/-- Item `C/04_R/disp/035` (`companion/chapters/04_R.tex:256-258`): "At this optimizer the first
three branches have values $-1$, $-1$, $-1-a\delta=-29/4$." The branches of display `disp/034` at
$(u,v)=(-1,5)$. -/
theorem fourPiece_branch_values (δ a : ℝ) (L : Mat 2)
    (hδ : δ = SeedOrbit.seedC - 16 * SeedOrbit.seedD - 1)
    (ha : a = 25 / (4 * δ)) (hL : L = !![1, 0; 0, 16 / 5]) :
    a * (-1) + a - 1 = -1 ∧ a * (-(-1) - 2 * 5 / 5) + a - 1 = -1 ∧
      a * (SeedOrbit.seedC * (-1) + 16 * SeedOrbit.seedD * 5 / 5) + a - 1 = -1 - a * δ ∧
      -1 - a * δ = -29 / 4 := by
  obtain ⟨rfl, rfl, rfl⟩ := fourPiece_consts δ a L hδ ha hL
  have hm := ReconstructedFourPiece.valueScale_mul_gap
  refine ⟨by ring, by ring, ?_, by linarith⟩
  rw [ReconstructedFourPiece.gap]
  ring

/-- An affine minorant that touches a differentiable function at $x$ has the same gradient
there. -/
theorem active_affine_gradient {n : ℕ} {F : Vec n → ℝ} (v : Vec n) (β : ℝ)
    (hle : ∀ z, dot v z + β ≤ F z) {x g : Vec n} (hx : F x = dot v x + β)
    (hg : HasFDerivAt F (gradientFunctional g) x) : g = v := by
  have hd : HasFDerivAt (fun z => F z - (dot v z + β))
      (gradientFunctional g - gradientFunctional v) x :=
    hg.sub (((gradientFunctional v).hasFDerivAt).add_const β |>.congr_of_eventuallyEq
      (Eventually.of_forall (fun z => by simp [gradientFunctional_apply])))
  have hmin : IsLocalMin (fun z => F z - (dot v z + β)) x :=
    Eventually.of_forall (fun z => by simp only; rw [hx]; linarith [hle z])
  have h0 := hmin.hasFDerivAt_eq_zero hd
  have h1 : gradientFunctional (g - v) = 0 := by
    rw [← h0]; ext w; simp [gradientFunctional_apply, dot_sub_left]
  exact sub_eq_zero.mp (Article.Global.eq_zero_of_gradientFunctional_eq_zero h1)

/-- Item `C/04_R/prose/046` (`companion/chapters/04_R.tex:259`): "so their supporting errors
are exactly $0,0,25/4$." For each of the first three branches $\ell_i$ of display `disp/034`,
$F_*-\ell_i(x_*)=0,0,25/4$ at $x_*=(-1,5)$; and at every differentiable point $x$ where the branch
is active ($F_R(x)=\ell_i(x)$), $b_{F_R}(x)=0,0,25/4$ respectively. -/
theorem fourPiece_branch_errors (δ a : ℝ) (L : Mat 2)
    (hδ : δ = SeedOrbit.seedC - 16 * SeedOrbit.seedD - 1)
    (ha : a = 25 / (4 * δ)) (hL : L = !![1, 0; 0, 16 / 5]) :
    (-1 - (a * (-1) + a - 1) = 0 ∧ -1 - (a * (-(-1) - 2 * 5 / 5) + a - 1) = 0 ∧
      -1 - (a * (SeedOrbit.seedC * (-1) + 16 * SeedOrbit.seedD * 5 / 5) + a - 1) = 25 / 4) ∧
    ∀ x g : Vec 2, HasFDerivAt ReconstructedFourPiece.objective (gradientFunctional g) x →
      (ReconstructedFourPiece.objective x = a * x 0 + a - 1 →
        dot g (x - ![-1, 5]) - (ReconstructedFourPiece.objective x - (-1)) = 0) ∧
      (ReconstructedFourPiece.objective x = a * (-x 0 - 2 * x 1 / 5) + a - 1 →
        dot g (x - ![-1, 5]) - (ReconstructedFourPiece.objective x - (-1)) = 0) ∧
      (ReconstructedFourPiece.objective x =
          a * (SeedOrbit.seedC * x 0 + 16 * SeedOrbit.seedD * x 1 / 5) + a - 1 →
        dot g (x - ![-1, 5]) - (ReconstructedFourPiece.objective x - (-1)) = 25 / 4) := by
  obtain ⟨h0, h1, h2, h3⟩ := fourPiece_branch_values δ a L hδ ha hL
  have hbr := fourPiece_branches δ a L hδ ha hL
  have hdot : ∀ (p q : ℝ) (z : Vec 2), dot ![p, q] z = p * z 0 + q * z 1 := fun p q z => by
    simp [dot, Fin.sum_univ_two]
  refine ⟨⟨by linarith, by linarith, by linarith⟩, fun x g hg => ⟨fun hx => ?_, fun hx => ?_,
    fun hx => ?_⟩⟩
  · have hv := active_affine_gradient ![a, 0] (a - 1) (fun z => by
      rw [hdot, hbr]; exact le_trans (by linarith) (le_max_left _ _ |>.trans
        (le_max_left _ _ |>.trans (le_max_left _ _)))) (by rw [hx, hdot]; ring) hg
    rw [hv, hx, RadialCertificate.dot_sub_right, hdot, hdot]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    ring
  · have hv := active_affine_gradient ![-a, -2 * a / 5] (a - 1) (fun z => by
      rw [hdot, hbr]; exact le_trans (by linarith) (le_max_right _ _ |>.trans
        (le_max_left _ _ |>.trans (le_max_left _ _)))) (by rw [hx, hdot]; ring) hg
    rw [hv, hx, RadialCertificate.dot_sub_right, hdot, hdot]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    ring
  · have hv := active_affine_gradient ![a * SeedOrbit.seedC, 16 * a * SeedOrbit.seedD / 5] (a - 1)
      (fun z => by
        rw [hdot, hbr]; exact le_trans (by linarith) (le_max_right _ _ |>.trans (le_max_left _ _)))
      (by rw [hx, hdot]; ring) hg
    rw [hv, hx, RadialCertificate.dot_sub_right, hdot, hdot]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [hδ] at h3
    linear_combination (-1 : ℝ) * h3


/-- Item `C/04_R/prose/047` (`companion/chapters/04_R.tex:261`): "This objective has an
actual infinite unmodified full-BFGS failure run." For every pair $0<c_1\le1/3$, $c_1<c_2<1$
there is an admissible run on $F_R$ with these constants whose iterates converge to $0$ and whose
values converge to $a-1>-1=\min F_R$; $0$ is not stationary ($0\notin\partial F_R(0)$). -/
theorem fourPiece_failure_run (δ a : ℝ) (L : Mat 2)
    (hδ : δ = SeedOrbit.seedC - 16 * SeedOrbit.seedD - 1)
    (ha : a = 25 / (4 * δ)) (hL : L = !![1, 0; 0, 16 / 5]) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁)
    (hc₁' : c₁ ≤ 1 / 3) (hc : c₁ < c₂) (hc₂ : c₂ < 1) :
    ∃ R : AdmissibleBFGSRun 2 ReconstructedFourPiece.objective, R.c₁ = c₁ ∧ R.c₂ = c₂ ∧
      Tendsto R.x atTop (𝓝 0) ∧
      Tendsto (fun k => ReconstructedFourPiece.objective (R.x k)) atTop (𝓝 (a - 1)) ∧
      -1 < a - 1 ∧
          (0 : Vec 2) ∉ ConvexSubdifferential.subdifferential
          ReconstructedFourPiece.objective 0 := by
  obtain ⟨-, rfl, -⟩ := fourPiece_consts δ a L hδ ha hL
  obtain ⟨-, -, -, -, -, -, -, hns, hrun⟩ := reconstructedFourPieceFailure
  obtain ⟨h1, h2, -, -, -, -, h7, h8, h9, -, -⟩ := hrun c₁ c₂ hc₁ hc₁' hc hc₂
  exact ⟨_, h1, h2, h7, h8, h9, hns⟩

/-- Item `C/04_R/disp/037` (`companion/chapters/04_R.tex:266-273`): with the verified run of
Chapter 12 (wording point W22 applied on 15 October 2026; before "the verified D run")
$x_k,g_k,H_k,\alpha_k$ (`SeedOrbit.coerciveRun`, for the parameters of display `disp/036`), the
transformed data $\widehat x_k=\mathcal L^{-1}x_k$, $\widehat g_k=a\mathcal L^Tg_k$,
$\widehat H_k=a^{-1}\mathcal L^{-1}H_k\mathcal L^{-T}$, $\widehat\alpha_k=\alpha_k$ are those of the
run `ReconstructedFourPiece.run` (which has the same constants $c_1,c_2$). -/
theorem fourPiece_transformed_data (δ a : ℝ) (L : Mat 2)
    (hδ : δ = SeedOrbit.seedC - 16 * SeedOrbit.seedD - 1)
    (ha : a = 25 / (4 * δ)) (hL : L = !![1, 0; 0, 16 / 5]) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁)
    (hc₁' : c₁ ≤ 1 / 3) (hc : c₁ < c₂) (hc₂ : c₂ < 1) :
    let RD := SeedOrbit.coerciveRun c₁ c₂ hc₁ hc₁' hc hc₂
    let Rh := ReconstructedFourPiece.run hc₁ hc₁' hc hc₂
    RD.c₁ = c₁ ∧ RD.c₂ = c₂ ∧ Rh.c₁ = c₁ ∧ Rh.c₂ = c₂ ∧
      ∀ k, Rh.x k = L⁻¹ *ᵥ RD.x k ∧ Rh.g k = a • (Lᵀ *ᵥ RD.g k) ∧
        Rh.H k = a⁻¹ • (L⁻¹ * RD.H k * (L⁻¹)ᵀ) ∧ Rh.α k = RD.α k := by
  obtain ⟨-, rfl, rfl⟩ := fourPiece_consts δ a L hδ ha hL
  exact ⟨rfl, rfl, rfl, rfl, fun k => ⟨rfl, rfl, rfl, rfl⟩⟩

/-- Item `C/04_R/prose/048` (`companion/chapters/04_R.tex:274`): "The gradients are the actual
derivatives of $F_R$ at the accepted points, and $\widehat H_0\succ0$." -/
theorem fourPiece_run_gradients (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1 / 3) (hc : c₁ < c₂)
    (hc₂ : c₂ < 1) :
    let Rh := ReconstructedFourPiece.run hc₁ hc₁' hc hc₂
    (∀ k, HasFDerivAt ReconstructedFourPiece.objective (gradientFunctional (Rh.g k)) (Rh.x k)) ∧
      (Rh.H 0).PosDef :=
  ⟨(ReconstructedFourPiece.run hc₁ hc₁' hc hc₂).hasGradient,
    (ReconstructedFourPiece.run hc₁ hc₁' hc hc₂).initial_posDef⟩

/-- Item `C/04_R/prose/049` (`companion/chapters/04_R.tex:274`): "Direct substitution in the
inverse-BFGS update proves that these are its exact next matrices and steps." The transformed
data satisfy $\widehat x_{k+1}=\widehat x_k+\widehat s_k$ with
$\widehat s_k=-\widehat\alpha_k\widehat H_k\widehat g_k=\mathcal L^{-1}s_k$, and
$\widehat H_{k+1}$ is the inverse-BFGS update of $\widehat H_k$ with $\widehat s_k$ and
$\widehat y_k=\widehat g_{k+1}-\widehat g_k=a\mathcal L^Ty_k$. -/
theorem fourPiece_run_updates (δ a : ℝ) (L : Mat 2)
    (hδ : δ = SeedOrbit.seedC - 16 * SeedOrbit.seedD - 1)
    (ha : a = 25 / (4 * δ)) (hL : L = !![1, 0; 0, 16 / 5]) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁)
    (hc₁' : c₁ ≤ 1 / 3) (hc : c₁ < c₂) (hc₂ : c₂ < 1) :
    let RD := SeedOrbit.coerciveRun c₁ c₂ hc₁ hc₁' hc hc₂
    let Rh := ReconstructedFourPiece.run hc₁ hc₁' hc hc₂
    ∀ k, Rh.x (k + 1) = Rh.x k + bfgsStep (Rh.H k) (Rh.g k) (Rh.α k) ∧
      Rh.H (k + 1) = inverseBFGS (Rh.H k) (bfgsStep (Rh.H k) (Rh.g k) (Rh.α k))
        (Rh.g (k + 1) - Rh.g k) ∧
      bfgsStep (Rh.H k) (Rh.g k) (Rh.α k) = L⁻¹ *ᵥ bfgsStep (RD.H k) (RD.g k) (RD.α k) ∧
      Rh.g (k + 1) - Rh.g k = a • (Lᵀ *ᵥ (RD.g (k + 1) - RD.g k)) := by
  obtain ⟨-, rfl, rfl⟩ := fourPiece_consts δ a L hδ ha hL
  intro RD Rh k
  refine ⟨Rh.step k, Rh.update k, ?_, ?_⟩
  · change bfgsStep (ReconstructedFourPiece.valueScale⁻¹ •
        AffineWhitening.metric ReconstructedFourPiece.coordinate (RD.H k))
      (ReconstructedFourPiece.valueScale •
        AffineWhitening.gradient ReconstructedFourPiece.coordinate (RD.g k)) (RD.α k) = _
    rw [ObjectiveValueScale.step _ ReconstructedFourPiece.valueScale_pos.ne',
      AffineWhitening.step_equiv _ ReconstructedFourPiece.coordinate_det_ne]
    rfl
  · change ReconstructedFourPiece.valueScale •
        AffineWhitening.gradient ReconstructedFourPiece.coordinate (RD.g (k + 1)) -
      ReconstructedFourPiece.valueScale •
        AffineWhitening.gradient ReconstructedFourPiece.coordinate (RD.g k) = _
    rw [← smul_sub]
    simp only [AffineWhitening.gradient, Matrix.mulVec_sub]

/-- Item `C/04_R/prose/050` (`companion/chapters/04_R.tex:274`): "Both the predicted and actual
objective decreases and the secant curvature are multiplied by $a$, so Armijo and weak Wolfe hold
with the same constants." For every $k$:
$F_R(\widehat x_k)-F_R(\widehat x_{k+1})=a(F_D(x_k)-F_D(x_{k+1}))$,
$\widehat g_k^T\widehat s_k=a\,g_k^Ts_k$, $\widehat y_k^T\widehat s_k=a\,y_k^Ts_k$, and the
transformed run satisfies Armijo and weak Wolfe with the constants $c_1,c_2$ of the D run. -/
theorem fourPiece_run_scaling (δ a : ℝ) (L : Mat 2)
    (hδ : δ = SeedOrbit.seedC - 16 * SeedOrbit.seedD - 1)
    (ha : a = 25 / (4 * δ)) (hL : L = !![1, 0; 0, 16 / 5]) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁)
    (hc₁' : c₁ ≤ 1 / 3) (hc : c₁ < c₂) (hc₂ : c₂ < 1) :
    let RD := SeedOrbit.coerciveRun c₁ c₂ hc₁ hc₁' hc hc₂
    let Rh := ReconstructedFourPiece.run hc₁ hc₁' hc hc₂
    ∀ k, ReconstructedFourPiece.objective (Rh.x k) -
        ReconstructedFourPiece.objective (Rh.x (k + 1)) =
        a * (SeedOrbit.coerciveObjective (RD.x k) - SeedOrbit.coerciveObjective (RD.x (k + 1))) ∧
      dot (Rh.g k) (bfgsStep (Rh.H k) (Rh.g k) (Rh.α k)) =
        a * dot (RD.g k) (bfgsStep (RD.H k) (RD.g k) (RD.α k)) ∧
      dot (Rh.g (k + 1) - Rh.g k) (bfgsStep (Rh.H k) (Rh.g k) (Rh.α k)) =
        a * dot (RD.g (k + 1) - RD.g k) (bfgsStep (RD.H k) (RD.g k) (RD.α k)) ∧
      ReconstructedFourPiece.objective (Rh.x (k + 1)) ≤
        ReconstructedFourPiece.objective (Rh.x k) +
            c₁ * dot (Rh.g k) (bfgsStep (Rh.H k) (Rh.g k) (Rh.α k)) ∧
      c₂ * dot (Rh.g k) (bfgsStep (Rh.H k) (Rh.g k) (Rh.α k)) ≤
        dot (Rh.g (k + 1)) (bfgsStep (Rh.H k) (Rh.g k) (Rh.α k)) := by
  have hup := fourPiece_run_updates δ a L hδ ha hL c₁ c₂ hc₁ hc₁' hc hc₂
  obtain ⟨-, rfl, rfl⟩ := fourPiece_consts δ a L hδ ha hL
  intro RD Rh k
  obtain ⟨-, -, hs, hy⟩ := hup k
  have hgk : Rh.g k = ReconstructedFourPiece.valueScale •
      (ReconstructedFourPiece.coordinateᵀ *ᵥ RD.g k) := rfl
  have hdotp : ∀ g s : Vec 2, dot (ReconstructedFourPiece.coordinateᵀ *ᵥ g)
      (ReconstructedFourPiece.coordinate⁻¹ *ᵥ s) = dot g s := fun g s =>
    AffineWhitening.dot_gradient_point _ ReconstructedFourPiece.coordinate_det_ne g s
  refine ⟨?_, ?_, ?_, Rh.armijo k, ?_⟩
  · change ReconstructedFourPiece.objective (ReconstructedFourPiece.point k) -
        ReconstructedFourPiece.objective (ReconstructedFourPiece.point (k + 1)) = _
    rw [ReconstructedFourPiece.point_value, ReconstructedFourPiece.point_value]
    change _ = ReconstructedFourPiece.valueScale *
      (SeedOrbit.coerciveObjective (SeedOrbit.orbitPoint k) -
        SeedOrbit.coerciveObjective (SeedOrbit.orbitPoint (k + 1)))
    ring
  · rw [hs, hgk, PlanarUpdate.dot_scale_left, hdotp]
  · rw [hs, hy, PlanarUpdate.dot_scale_left, hdotp]
  · exact Rh.weak_wolfe k

/-- Item `C/04_R/prose/051` (`companion/chapters/04_R.tex:274`): "This proves a transformed
full-BFGS run, rather than prescribing an unrelated sequence of endpoint pairs." The transformed
data of display `disp/037` form an admissible run on $F_R$ (Definition `art:admissible`) with the
constants $c_1,c_2$. -/
theorem fourPiece_transformed_run (δ a : ℝ) (L : Mat 2)
    (hδ : δ = SeedOrbit.seedC - 16 * SeedOrbit.seedD - 1)
    (ha : a = 25 / (4 * δ)) (hL : L = !![1, 0; 0, 16 / 5]) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁)
    (hc₁' : c₁ ≤ 1 / 3) (hc : c₁ < c₂) (hc₂ : c₂ < 1) :
    ∃ Rh : AdmissibleBFGSRun 2 ReconstructedFourPiece.objective, Rh.c₁ = c₁ ∧ Rh.c₂ = c₂ ∧
      ∀ k, Rh.x k = L⁻¹ *ᵥ SeedOrbit.orbitPoint k ∧
        Rh.g k = a • (Lᵀ *ᵥ SeedOrbit.orbitGradient k) ∧
        Rh.H k = a⁻¹ • (L⁻¹ * SeedOrbit.orbitMetric k * (L⁻¹)ᵀ) ∧
        Rh.α k = SeedOrbit.orbitLength k := by
  obtain ⟨-, rfl, rfl⟩ := fourPiece_consts δ a L hδ ha hL
  exact ⟨ReconstructedFourPiece.run hc₁ hc₁' hc hc₂, rfl, rfl, fun k => ⟨rfl, rfl, rfl, rfl⟩⟩

/-- Item `C/04_R/prose/052` (`companion/chapters/04_R.tex:276`): "The iterates satisfy
$\widehat x_k\to0$, while their strictly decreasing values tend to $a-1>-1$; zero is
nonstationary." -/
theorem fourPiece_run_limits (δ a : ℝ) (L : Mat 2)
    (hδ : δ = SeedOrbit.seedC - 16 * SeedOrbit.seedD - 1)
    (ha : a = 25 / (4 * δ)) (hL : L = !![1, 0; 0, 16 / 5]) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁)
    (hc₁' : c₁ ≤ 1 / 3) (hc : c₁ < c₂) (hc₂ : c₂ < 1) :
    let Rh := ReconstructedFourPiece.run hc₁ hc₁' hc hc₂
    Tendsto Rh.x atTop (𝓝 0) ∧
      (∀ k, ReconstructedFourPiece.objective (Rh.x (k + 1)) <
          ReconstructedFourPiece.objective (Rh.x k)) ∧
      Tendsto (fun k => ReconstructedFourPiece.objective (Rh.x k)) atTop (𝓝 (a - 1)) ∧ -1 < a - 1 ∧
      (0 : Vec 2) ∉ ConvexSubdifferential.subdifferential ReconstructedFourPiece.objective 0 := by
  obtain ⟨-, rfl, -⟩ := fourPiece_consts δ a L hδ ha hL
  obtain ⟨-, -, -, -, -, -, -, hns, hrun⟩ := reconstructedFourPieceFailure
  obtain ⟨-, -, -, -, -, -, h7, h8, h9, -, h11⟩ := hrun c₁ c₂ hc₁ hc₁' hc hc₂
  exact ⟨h7, h11, h8, h9, hns⟩

/-- Item `C/04_R/prose/053` (`companion/chapters/04_R.tex:276`): "In every three phases the
actual supporting errors repeat $0,0,25/4$." $b_{F_R}(\widehat x_{3m+j})=0,0,25/4$ for
$j=0,1,2$, with the run's gradients and $x_*=(-1,5)$. -/
theorem fourPiece_phase_errors (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1 / 3) (hc : c₁ < c₂)
    (hc₂ : c₂ < 1) :
    let Rh := ReconstructedFourPiece.run hc₁ hc₁' hc hc₂
    ∀ (m : ℕ) (j : Fin 3),
      dot (Rh.g (3 * m + j.val)) (Rh.x (3 * m + j.val) - ![-1, 5]) -
        (ReconstructedFourPiece.objective (Rh.x (3 * m + j.val)) -
          ReconstructedFourPiece.objective ![-1, 5]) = (![0, 0, 25 / 4] : Vec 3) j :=
  fun m j => ReconstructedFourPiece.point_phase_intercepts m j

/-- Item `C/04_R/prose/054` (`companion/chapters/04_R.tex:276`): "The actual positive secant
curvatures are $a$ times those of the run of Chapter~\ref{comp:D} and tend to zero." (Wording
point W22 applied on 15 October 2026; before "those of D".) -/
theorem fourPiece_curvatures (δ a : ℝ) (L : Mat 2)
    (hδ : δ = SeedOrbit.seedC - 16 * SeedOrbit.seedD - 1)
    (ha : a = 25 / (4 * δ)) (hL : L = !![1, 0; 0, 16 / 5]) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁)
    (hc₁' : c₁ ≤ 1 / 3) (hc : c₁ < c₂) (hc₂ : c₂ < 1) :
    let RD := SeedOrbit.coerciveRun c₁ c₂ hc₁ hc₁' hc hc₂
    let Rh := ReconstructedFourPiece.run hc₁ hc₁' hc hc₂
    (∀ k, dot (Rh.g (k + 1) - Rh.g k) (Rh.x (k + 1) - Rh.x k) =
        a * dot (RD.g (k + 1) - RD.g k) (RD.x (k + 1) - RD.x k) ∧
      0 < dot (Rh.g (k + 1) - Rh.g k) (Rh.x (k + 1) - Rh.x k)) ∧
      Tendsto (fun k => dot (Rh.g (k + 1) - Rh.g k) (Rh.x (k + 1) - Rh.x k)) atTop (𝓝 0) := by
  obtain ⟨-, rfl, -⟩ := fourPiece_consts δ a L hδ ha hL
  exact ⟨fun k => ⟨ReconstructedFourPiece.secant_scale k, ReconstructedFourPiece.secant_pos k⟩,
    ReconstructedFourPiece.secant_tendsto_zero⟩

/-- Item `C/04_R/disp/038` (`companion/chapters/04_R.tex:277-280`): "On the fixed band
$K=\{F_R\le F_R(\widehat x_0)\}$, $F_R\ge-1+a$, all these accepted points remain above the band
threshold." Every iterate lies in $K$ with $F_R(\widehat x_k)>-1+a$ (the band $\eta=a$ above
$F_*=-1$). -/
theorem fourPiece_band (δ a : ℝ) (L : Mat 2) (hδ : δ = SeedOrbit.seedC - 16 * SeedOrbit.seedD - 1)
    (ha : a = 25 / (4 * δ)) (hL : L = !![1, 0; 0, 16 / 5]) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁)
    (hc₁' : c₁ ≤ 1 / 3) (hc : c₁ < c₂) (hc₂ : c₂ < 1) :
    let Rh := ReconstructedFourPiece.run hc₁ hc₁' hc hc₂
    ∀ k, Rh.x k ∈
        {z | ReconstructedFourPiece.objective z ≤ ReconstructedFourPiece.objective (Rh.x 0)} ∧
      -1 + a < ReconstructedFourPiece.objective (Rh.x k) := by
  obtain ⟨-, rfl, -⟩ := fourPiece_consts δ a L hδ ha hL
  intro Rh k
  refine ⟨Rh.objective_le_initial k, ?_⟩
  have := ReconstructedFourPiece.point_value_above_limit k
  change _ < ReconstructedFourPiece.objective (ReconstructedFourPiece.point k)
  linarith

/-- Item `C/04_R/prose/055` (`companion/chapters/04_R.tex:281`): "Applying (SP) to successive
points with indices $3m+1$ and $3m+2$ would give $(25/4)^2\le C'T_k$ for every cycle". For every
constant $C'$ of (SP) on the band $\eta=a$ of $K$, $(25/4)^2\le C'T_{3m+1}$ for every $m$, with
$T_k=(\widehat g_{k+1}-\widehat g_k)^T(\widehat x_{k+1}-\widehat x_k)$. -/
theorem fourPiece_SP_instance (δ a : ℝ) (L : Mat 2)
    (hδ : δ = SeedOrbit.seedC - 16 * SeedOrbit.seedD - 1)
    (ha : a = 25 / (4 * δ)) (hL : L = !![1, 0; 0, 16 / 5]) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁)
    (hc₁' : c₁ ≤ 1 / 3) (hc : c₁ < c₂) (hc₂ : c₂ < 1) :
    let Rh := ReconstructedFourPiece.run hc₁ hc₁' hc hc₂
    ∀ C' : ℝ, (∀ x z g h : Vec 2,
        x ∈ {z | ReconstructedFourPiece.objective z ≤ ReconstructedFourPiece.objective (Rh.x 0)} →
        z ∈ {z | ReconstructedFourPiece.objective z ≤ ReconstructedFourPiece.objective (Rh.x 0)} →
        HasFDerivAt ReconstructedFourPiece.objective (gradientFunctional g) x →
        HasFDerivAt ReconstructedFourPiece.objective (gradientFunctional h) z →
        ReconstructedFourPiece.objective ![-1, 5] + a ≤ ReconstructedFourPiece.objective z →
        ReconstructedFourPiece.objective z ≤ ReconstructedFourPiece.objective x →
        0 < dot (h - g) (z - x) →
        |(dot h (z - ![-1, 5]) - (ReconstructedFourPiece.objective z -
            ReconstructedFourPiece.objective ![-1, 5])) -
          (dot g (x - ![-1, 5]) - (ReconstructedFourPiece.objective x -
            ReconstructedFourPiece.objective ![-1, 5]))| ^ 2 ≤ C' * dot (h - g) (z - x)) →
      ∀ m : ℕ, (25 / 4 : ℝ) ^ 2 ≤
        C' * dot (Rh.g (3 * m + 1 + 1) - Rh.g (3 * m + 1))
            (Rh.x (3 * m + 1 + 1) - Rh.x (3 * m + 1)) := by
  have hband := fourPiece_band δ a L hδ ha hL c₁ c₂ hc₁ hc₁' hc hc₂
  obtain ⟨-, rfl, -⟩ := fourPiece_consts δ a L hδ ha hL
  intro Rh C' hC m
  have hmin : ReconstructedFourPiece.objective ![-1, 5] = -1 := ReconstructedFourPiece.minimum_value
  have hb := hC (Rh.x (3 * m + 1)) (Rh.x (3 * m + 1 + 1)) (Rh.g (3 * m + 1)) (Rh.g (3 * m + 1 + 1))
    (hband _).1 (hband _).1 (Rh.hasGradient _) (Rh.hasGradient _)
    (by rw [hmin]; linarith [(hband (3 * m + 1 + 1)).2]) (Rh.objective_strict_decrease _).le
    (ReconstructedFourPiece.secant_pos _)
  have hi := fourPiece_phase_errors c₁ c₂ hc₁ hc₁' hc hc₂ m 1
  have hj := fourPiece_phase_errors c₁ c₂ hc₁ hc₁' hc hc₂ m 2
  simp only [Fin.val_one, Fin.val_two] at hi hj
  rw [show 3 * m + 2 = 3 * m + 1 + 1 by ring] at hj
  change _ = (25 / 4 : ℝ) at hj
  change _ = (0 : ℝ) at hi
  rw [hi, hj, sub_zero, abs_of_pos (by norm_num : (0 : ℝ) < 25 / 4)] at hb
  exact hb

/-- Item `C/04_R/prose/056` (`companion/chapters/04_R.tex:281`): "Thus (SP), and by the
compact-domain equivalence also (RS), fail on this actual initial sublevel." On
$K=\{F_R\le F_R(\widehat x_0)\}$ with $x_*=(-1,5)$. -/
theorem fourPiece_SP_RS_fail (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1 / 3) (hc : c₁ < c₂)
    (hc₂ : c₂ < 1) :
    let Rh := ReconstructedFourPiece.run hc₁ hc₁' hc hc₂
    ¬ SP ReconstructedFourPiece.objective ![-1, 5]
        {z | ReconstructedFourPiece.objective z ≤ ReconstructedFourPiece.objective (Rh.x 0)} ∧
      ¬ RS ReconstructedFourPiece.objective ![-1, 5]
        {z | ReconstructedFourPiece.objective z ≤ ReconstructedFourPiece.objective (Rh.x 0)} := by
  intro Rh
  rw [SP_iff_library, RS_iff_library]
  exact ⟨ReconstructedFourPiece.no_intercept_bounds, ReconstructedFourPiece.no_radial_bounds⟩


/-! ### Section 4.5: Theorem `R:thm:plq` (lines 291-309)

Hypotheses of the theorem: $F$ finite convex with unique minimizer $x_*$; a neighborhood $N$ of
$x_*$ (`N ∈ 𝓝 xstar`) covered by the finitely many polyhedra
$P_i=\{x: a_{ij}^Tx\le b_{ij}\}$ (closed; full-dimensional: `_hfull`); functions $f_i$ with
$F=f_i$ on $N\cap P_i$ (display `disp/039`; this makes the values compatible on overlaps); and open
sets $V_i\supset N\cap P_i$ ("an open neighborhood of the relevant part of its cell") on which
$f_i$ is $C^{1,1}$: differentiable with Lipschitz derivative. -/

/-- Item `C/04_R/theorem/R:thm:plq` (`companion/chapters/04_R.tex:292-298`), Theorem `R:thm:plq`
("Finite polyhedral partitions"), with its display `C/04_R/disp/039` (lines 294-296). "Let $F$ be
finite and convex, with a unique minimizer $x_*$. Suppose a neighborhood of $x_*$ is covered by
finitely many closed full-dimensional polyhedra $P_i$, with compatible function values on overlaps,
and $F(x)=f_i(x)$ $(x\in P_i)$ there. Assume each $f_i$ has a $C^{1,1}$ extension to an open
neighborhood of the relevant part of its cell. Then every sufficiently low-starting infinite
admissible full-BFGS run converges to $x_*$, for arbitrary SPD initialization." The threshold
$\varepsilon$ is chosen before the run (and its $H_0$). The proof is the library's
`ConvexCellRadial.finite_polyhedral_basin` (with the open neighborhood `interior N`), which needs
only local $C^{1,1}$ extensions (`plq_theorem_local`) and no full-dimensionality. -/
theorem plq_theorem {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F) (xstar : Vec n)
    (hmin : ∀ x, F xstar ≤ F x) (huniq : ∀ x, F x = F xstar → x = xstar)
    (N : Set (Vec n)) (hN : N ∈ 𝓝 xstar)
    {ι : Type*} [Fintype ι] (m : ι → ℕ) (a : ∀ i, Fin (m i) → Vec n) (b : ∀ i, Fin (m i) → ℝ)
    (P : ι → Set (Vec n)) (hP : ∀ i, P i = {x | ∀ j, dot (a i j) x ≤ b i j})
    (_hfull : ∀ i, (interior (P i)).Nonempty) (hcover : N ⊆ ⋃ i, P i)
    (f : ι → Vec n → ℝ) (hrep : ∀ i, ∀ x ∈ N ∩ P i, F x = f i x)
    (V : ι → Set (Vec n)) (hV : ∀ i, IsOpen (V i)) (hNV : ∀ i, N ∩ P i ⊆ V i)
    (hf : ∀ i, DifferentiableOn ℝ (f i) (V i) ∧
      ∃ L : NNReal, LipschitzOnWith L (fderiv ℝ (f i)) (V i)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ run : AdmissibleBFGSRun n F, F (run.x 0) ≤ F xstar + ε →
      Tendsto run.x atTop (𝓝 xstar) := by
  have hloc : ∀ i, CenteredSmoothSublinear.LocallyC11On (V i) (f i) := fun i => by
    obtain ⟨hd, L, hL⟩ := hf i
    exact ⟨hd, fun x _ => ⟨L, V i, self_mem_nhdsWithin, hL⟩⟩
  have hPe : ∀ i, P i = ConvexCellRadial.polyhedron (a i) (b i) := hP
  obtain ⟨δ, hδ, hbasin⟩ := ConvexCellRadial.finite_polyhedral_basin hF a b V f hV hloc
    isOpen_interior (mem_interior_iff_mem_nhds.mpr hN)
    (fun i x hx => hNV i ⟨interior_subset hx.1, by rw [hPe i]; exact hx.2⟩)
    (fun x hx => by
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover (interior_subset hx))
      exact ⟨i, by rw [← hPe i]; exact hi⟩)
    (fun i x hx hxi => hrep i x ⟨interior_subset hx, by rw [hPe i]; exact hxi⟩) hmin huniq
  exact ⟨δ, hδ, fun run hrun => (hbasin run hrun).2.2⟩

/-- Item `C/04_R/theorem/R:thm:plq` (`companion/chapters/04_R.tex:292-298`), the general form: the
conclusion of Theorem `R:thm:plq` with only locally $C^{1,1}$ extensions
(`LocallyC11On (V i) (f i)`), which `plq_theorem` specializes; the iterates also stay in $N$ and
the values converge. -/
theorem plq_theorem_local {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F) (xstar : Vec n)
    (hmin : ∀ x, F xstar ≤ F x) (huniq : ∀ x, F x = F xstar → x = xstar)
    (N : Set (Vec n)) (hN : N ∈ 𝓝 xstar)
    {ι : Type*} [Fintype ι] (m : ι → ℕ) (a : ∀ i, Fin (m i) → Vec n) (b : ∀ i, Fin (m i) → ℝ)
    (P : ι → Set (Vec n)) (hP : ∀ i, P i = {x | ∀ j, dot (a i j) x ≤ b i j})
    (_hfull : ∀ i, (interior (P i)).Nonempty) (hcover : N ⊆ ⋃ i, P i)
    (f : ι → Vec n → ℝ) (hrep : ∀ i, ∀ x ∈ N ∩ P i, F x = f i x)
    (V : ι → Set (Vec n)) (hV : ∀ i, IsOpen (V i)) (hNV : ∀ i, N ∩ P i ⊆ V i)
    (hf : ∀ i, CenteredSmoothSublinear.LocallyC11On (V i) (f i)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ run : AdmissibleBFGSRun n F, F (run.x 0) ≤ F xstar + ε →
      (∀ k, run.x k ∈ N) ∧ Tendsto (fun k => F (run.x k)) atTop (𝓝 (F xstar)) ∧
        Tendsto run.x atTop (𝓝 xstar) := by
  have hPe : ∀ i, P i = ConvexCellRadial.polyhedron (a i) (b i) := hP
  obtain ⟨δ, hδ, hbasin⟩ := ConvexCellRadial.finite_polyhedral_basin hF a b V f hV hf
    isOpen_interior (mem_interior_iff_mem_nhds.mpr hN)
    (fun i x hx => hNV i ⟨interior_subset hx.1, by rw [hPe i]; exact hx.2⟩)
    (fun x hx => by
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover (interior_subset hx))
      exact ⟨i, by rw [← hPe i]; exact hi⟩)
    (fun i x hx hxi => hrep i x ⟨interior_subset hx, by rw [hPe i]; exact hxi⟩) hmin huniq
  exact ⟨δ, hδ, fun run hrun => ⟨fun k => interior_subset ((hbasin run hrun).1 k),
    (hbasin run hrun).2.1, (hbasin run hrun).2.2⟩⟩

/-- Proof of Theorem `R:thm:plq`, undisplayed claim of line 300 (not a register item): "At a
differentiable point of $F$, its gradient agrees with the smooth gradient of each adjacent
full-dimensional cell: approach from the interior of that cell and use differentiability and
convexity of $F$." At a point $x$ of the open set `interior N` lying in the cell $P_i$, where $F$ is
differentiable with gradient $g$ and $f_i$ with gradient $h$: $g=h$ (the library's
`ConvexCellRadial.actual_gradients_eq_on_cell`, which uses full-dimensionality). -/
theorem plq_gradient_agreement {n : ℕ} {F : Vec n → ℝ} (_hF : ConvexOn ℝ univ F) (xstar : Vec n)
    (_hmin : ∀ x, F xstar ≤ F x) (_huniq : ∀ x, F x = F xstar → x = xstar)
    (N : Set (Vec n)) (_hN : N ∈ 𝓝 xstar)
    {ι : Type*} [Fintype ι] (m : ι → ℕ) (a : ∀ i, Fin (m i) → Vec n) (b : ∀ i, Fin (m i) → ℝ)
    (P : ι → Set (Vec n)) (hP : ∀ i, P i = {x | ∀ j, dot (a i j) x ≤ b i j})
    (hfull : ∀ i, (interior (P i)).Nonempty) (_hcover : N ⊆ ⋃ i, P i)
    (f : ι → Vec n → ℝ) (hrep : ∀ i, ∀ x ∈ N ∩ P i, F x = f i x)
    (V : ι → Set (Vec n)) (_hV : ∀ i, IsOpen (V i)) (_hNV : ∀ i, N ∩ P i ⊆ V i)
    (i : ι) (x g h : Vec n) (hx : x ∈ interior N) (hxi : x ∈ P i)
    (hg : HasFDerivAt F (gradientFunctional g) x)
    (hh : HasFDerivAt (f i) (gradientFunctional h) x) :
    g = h := by
  have hPc : Convex ℝ (P i) := by rw [hP i]; exact ConvexCellRadial.polyhedron_convex (a i) (b i)
  exact ConvexCellRadial.actual_gradients_eq_on_cell hPc (hfull i) isOpen_interior hxi hx
    (fun z hz hzP => hrep i z ⟨interior_subset hz, hzP⟩) hg hh

/-- Item `C/04_R/disp/040` (`companion/chapters/04_R.tex:303-306`), in the proof of Theorem
`R:thm:plq`: "Let $L$ bound the Lipschitz constants of the finitely many smooth extensions on a
smaller ball of radius $R$. For $x$ in one such cell, the usual Taylor estimate along the inward
segment gives
\[ 0\le F(x-tr_x)-F(x)+t\nabla F(x)^Tr_x\le\frac L2t^2\|r_x\|^2\le\frac{LR^2}{2}t^2." \]
Standing assumptions: the hypotheses of the theorem; the Euclidean ball $B=B_R(x_*)\subset N$ that
meets only cells containing $x_*$ (`hdisc`, after discarding the others) and lies in their
$V_i$; a common Euclidean Lipschitz bound $L$ of the gradients $\nabla f_i$ of the remaining
extensions on $B$; a differentiability point $x\in B$ of $F$ with gradient $g$ in a cell $P_i$;
$0\le t\le1$. -/
theorem plq_inward_taylor {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F) (xstar : Vec n)
    (hmin : ∀ x, F xstar ≤ F x) (huniq : ∀ x, F x = F xstar → x = xstar)
    (N : Set (Vec n)) (hN : N ∈ 𝓝 xstar)
    {ι : Type*} [Fintype ι] (m : ι → ℕ) (a : ∀ i, Fin (m i) → Vec n) (b : ∀ i, Fin (m i) → ℝ)
    (P : ι → Set (Vec n)) (hP : ∀ i, P i = {x | ∀ j, dot (a i j) x ≤ b i j})
    (_hfull : ∀ i, (interior (P i)).Nonempty) (hcover : N ⊆ ⋃ i, P i)
    (f : ι → Vec n → ℝ) (hrep : ∀ i, ∀ x ∈ N ∩ P i, F x = f i x)
    (V : ι → Set (Vec n)) (hV : ∀ i, IsOpen (V i)) (hNV : ∀ i, N ∩ P i ⊆ V i)
    (hf : ∀ i, DifferentiableOn ℝ (f i) (V i) ∧
      ∃ L : NNReal, LipschitzOnWith L (fderiv ℝ (f i)) (V i))
    (R : ℝ) (hR : 0 < R) (B : Set (Vec n)) (hB : B = {x | ‖euclideanVector (x - xstar)‖ < R})
    (hBN : B ⊆ N) (hBV : ∀ i, xstar ∈ P i → B ⊆ V i)
    (hdisc : ∀ i, (B ∩ P i).Nonempty → xstar ∈ P i) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ i, xstar ∈ P i → ∀ y ∈ B, ∀ y' ∈ B,
      ‖euclideanVector (coordinateGradient (f i) y - coordinateGradient (f i) y')‖ ≤
        L * ‖euclideanVector (y - y')‖)
    (x g : Vec n) (hxB : x ∈ B) (hg : HasFDerivAt F (gradientFunctional g) x) (i : ι)
    (hxi : x ∈ P i) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ F (x - t • (x - xstar)) - F x + t * dot g (x - xstar) ∧
      F (x - t • (x - xstar)) - F x + t * dot g (x - xstar) ≤
        L / 2 * t ^ 2 * ‖euclideanVector (x - xstar)‖ ^ 2 ∧
      L / 2 * t ^ 2 * ‖euclideanVector (x - xstar)‖ ^ 2 ≤ L * R ^ 2 / 2 * t ^ 2 := by
  have hloc : ∀ i, CenteredSmoothSublinear.LocallyC11On (V i) (f i) := fun i => by
    obtain ⟨hd, L, hL⟩ := hf i
    exact ⟨hd, fun x _ => ⟨L, V i, self_mem_nhdsWithin, hL⟩⟩
  have hBo : IsOpen B := hB ▸ (Article.Local.euclid_ball_open_convex xstar R).1
  have hBint : B ⊆ interior N := interior_maximal hBN hBo
  by_cases hn : 1 ≤ n
  · obtain ⟨h1, h2, h3⟩ := Article.Local.polyhedral_inward_taylor hn F hF xstar hmin huniq
      (interior N) isOpen_interior (mem_interior_iff_mem_nhds.mpr hN) m a b P hP _hfull
      (fun x hx => hcover (interior_subset hx)) V hV
      (fun i x hx => hNV i ⟨interior_subset hx.1, hx.2⟩) f hloc
      (fun i x hx => hrep i x ⟨interior_subset hx.1, hx.2⟩) R hR B hB hBint hBV hdisc L hL hLip
      x g hxB hg i hxi t ht0 ht1
    rw [← Article.Global.norm_euclideanVector_sq] at h2 h3
    refine ⟨h1, by linarith, by linarith⟩
  · have hn0 : n = 0 := by omega
    subst hn0
    have hx0 : x - xstar = 0 := Subsingleton.elim _ _
    rw [hx0]
    simp only [smul_zero, sub_zero]
    rw [show euclideanVector (0 : Vec 0) = 0 from rfl, norm_zero]
    refine ⟨by simp [dot], by simp [dot], by simp; positivity⟩


/-- Item `C/04_R/prose/058` (`companion/chapters/04_R.tex:309`): "In particular this covers
every finite convex \emph{piecewise linear-quadratic} objective, and a convex smooth loss plus a
finite convex piecewise linear-quadratic regularizer." First case: a finite convex $F$ with unique
minimizer $x_*$ and a quadratic formula $x^TQ_ix+c_i^Tx+d_i$ on each cell of a finite cover of
$\R^n$ by closed full-dimensional polyhedra has the conclusion of Theorem `R:thm:plq`. The second
case is `plq_covered_loss`. (Derived from the article's Corollary `art:plq`,
`Article.Local.plq`.) -/
theorem plq_covered_objective {n : ℕ} (F : Vec n → ℝ) (hF : ConvexOn ℝ univ F) (xstar : Vec n)
    (hmin : ∀ x, F xstar ≤ F x) (huniq : ∀ x, F x = F xstar → x = xstar)
    {ι : Type*} [Fintype ι] (m : ι → ℕ) (a : ∀ i, Fin (m i) → Vec n) (b : ∀ i, Fin (m i) → ℝ)
    (P : ι → Set (Vec n)) (hP : ∀ i, P i = {x | ∀ j, dot (a i j) x ≤ b i j})
    (hfull : ∀ i, (interior (P i)).Nonempty) (hcover : ∀ x, ∃ i, x ∈ P i)
    (Q : ι → Mat n) (c : ι → Vec n) (d : ι → ℝ)
    (hrep : ∀ i, ∀ x ∈ P i, F x = dot x (Q i *ᵥ x) + dot (c i) x + d i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ run : AdmissibleBFGSRun n F, F (run.x 0) ≤ F xstar + ε →
      Tendsto run.x atTop (𝓝 xstar) := by
  obtain ⟨ε, hε, h⟩ := Article.Local.plq F hF xstar hmin huniq m a b P hP hfull hcover Q c d hrep
    univ isOpen_univ (mem_univ _)
  exact ⟨ε, hε, fun run hrun => (h run hrun).2.2⟩

/-- A $C^2$ function on $\R^n$ is locally $C^{1,1}$ (`CenteredSmoothSublinear.LocallyC11On univ`):
the $C^2$ case of the locally $C^{1,1}$ ("smooth") hypotheses below. -/
theorem locallyC11_of_contDiff_two {n : ℕ} {ψ : Vec n → ℝ} (hψ : ContDiff ℝ 2 ψ) :
    CenteredSmoothSublinear.LocallyC11On univ ψ :=
  ConvexCellRadial.contDiffOn_two_locallyC11 isOpen_univ hψ.contDiffOn

/-- Item `C/04_R/prose/058` (`companion/chapters/04_R.tex:309`), second case: a convex smooth
loss (locally $C^{1,1}$, `CenteredSmoothSublinear.LocallyC11On univ`, as in the article's parallel
Corollary `art:plq`; $C^2$ losses are included by `locallyC11_of_contDiff_two`) plus a finite
convex piecewise linear-quadratic regularizer, the sum having a unique minimizer $x_*$, has the
conclusion of Theorem `R:thm:plq` (the article's `Article.Local.plq_loss_regularizer`). -/
theorem plq_covered_loss {n : ℕ} (loss reg F : Vec n → ℝ) (hloss : ConvexOn ℝ univ loss)
    (hloss11 : CenteredSmoothSublinear.LocallyC11On univ loss) (hreg : ConvexOn ℝ univ reg)
    {ι : Type*} [Fintype ι] (m : ι → ℕ) (a : ∀ i, Fin (m i) → Vec n) (b : ∀ i, Fin (m i) → ℝ)
    (P : ι → Set (Vec n)) (hP : ∀ i, P i = {x | ∀ j, dot (a i j) x ≤ b i j})
    (hfull : ∀ i, (interior (P i)).Nonempty) (hcover : ∀ x, ∃ i, x ∈ P i)
    (Q : ι → Mat n) (c : ι → Vec n) (d : ι → ℝ)
    (hrep : ∀ i, ∀ x ∈ P i, reg x = dot x (Q i *ᵥ x) + dot (c i) x + d i)
    (hFdef : ∀ x, F x = loss x + reg x) (xstar : Vec n) (hmin : ∀ x, F xstar ≤ F x)
    (huniq : ∀ x, F x = F xstar → x = xstar) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ run : AdmissibleBFGSRun n F, F (run.x 0) ≤ F xstar + ε →
      Tendsto run.x atTop (𝓝 xstar) := by
  obtain ⟨ε, hε, h⟩ := Article.Local.plq_loss_regularizer loss reg F hloss hloss11 hreg m a b P
    hP hfull hcover Q c d hrep hFdef xstar hmin huniq univ isOpen_univ (mem_univ _)
  exact ⟨ε, hε, fun run hrun => (h run hrun).2.2⟩

/-- A finite sum of absolute affine residuals is convex. -/
theorem abs_affine_sum_convex {n : ℕ} {ι : Type*} [Fintype ι] (a : ι → Vec n) (b : ι → ℝ) :
    ConvexOn ℝ univ (fun x => ∑ i, |dot (a i) x - b i|) := by
  have h := Article.Local.convexOn_finset_sum Finset.univ
    (fun i x => (AffineKinks.Kink.absolute (a i) (b i)).value x)
    (fun i _ => (AffineKinks.Kink.absolute (a i) (b i)).value_convex)
  simpa only [AffineKinks.Kink.absolute_value] using h

/-- The derivative of a scalar quadratic. -/
theorem hasDerivAt_quad (q c d t : ℝ) :
    HasDerivAt (fun s : ℝ => q * s ^ 2 + c * s + d) (2 * q * t + c) t := by
  have h := (((hasDerivAt_pow 2 t).const_mul q).add
    ((hasDerivAt_id' (x := t)).const_mul c)).add_const d
  convert h using 1
  ring

/-- A function equal to a quadratic $qs^2+cs+d$ on an open set has second derivative $2q$ there. -/
theorem iteratedDeriv_two_of_eqOn_quad {ψ : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (q c d : ℝ)
    (hEq : ∀ s ∈ U, ψ s = q * s ^ 2 + c * s + d) {t : ℝ} (ht : t ∈ U) :
    iteratedDeriv 2 ψ t = 2 * q := by
  have hp' : HasDerivAt (fun s => 2 * q * s + c) (2 * q) t := by
    simpa using ((hasDerivAt_id' (x := t)).const_mul (2 * q)).add_const c
  have h2 : deriv ψ =ᶠ[𝓝 t] fun s => 2 * q * s + c := by
    filter_upwards [hU.mem_nhds ht] with s hs
    rw [(Filter.eventuallyEq_of_mem (hU.mem_nhds hs) (fun y hy => hEq y hy)).deriv_eq]
    exact (hasDerivAt_quad q c d s).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, h2.deriv_eq]
  exact hp'.deriv

/-- The key step of `plq_broader` (Item `C/04_R/prose/059`), on the real line: near $0$,
$t^2+\max\{t,0\}^2$ is not $\psi+\varphi$ with $\psi$ of class $C^2$ and $\varphi$ a finite
maximum of affine functions $\alpha_jt+\beta_j$. Near $0$ only the pieces active at $0$ matter, so
$\varphi$ is affine on each side of $0$; then $\psi''=4$ on the right of $0$ and $\psi''=2$ on
its left, contradicting continuity of $\psi''$. -/
theorem not_smooth_plus_max_affine {k : ℕ} (ψ φ : ℝ → ℝ) (hψ : ContDiff ℝ 2 ψ) (α β : Fin k → ℝ)
    (hφ : ∀ t, IsGreatest (Set.range fun j => α j * t + β j) (φ t))
    (h : ∀ᶠ t in 𝓝 (0 : ℝ), t ^ 2 + max t 0 ^ 2 = ψ t + φ t) : False := by
  classical
  set S := φ 0 with hS
  have hβS : ∀ j, β j ≤ S := fun j => by
    have h' : α j * 0 + β j ≤ φ 0 := (hφ 0).2 ⟨j, rfl⟩
    simpa using h'
  obtain ⟨j0, hj0⟩ := (hφ 0).1
  have hj0S : β j0 = S := by simpa using hj0
  set act := Finset.univ.filter (fun j => β j = S) with hact
  have hactne : act.Nonempty := ⟨j0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj0S⟩⟩
  obtain ⟨kR, hkR, hkRmax⟩ := act.exists_max_image α hactne
  obtain ⟨kL, hkL, hkLmin⟩ := act.exists_min_image α hactne
  have hev : ∀ A : ℝ, ∀ᶠ t in 𝓝 (0 : ℝ), ∀ j, β j ≠ S → α j * t + β j < S + A * t := by
    intro A
    rw [Filter.eventually_all]
    intro j
    by_cases hj : β j = S
    · exact Filter.Eventually.of_forall (fun t h' => absurd hj h')
    · have hlt : β j < S := lt_of_le_of_ne (hβS j) hj
      have h1 : ContinuousAt (fun t : ℝ => α j * t + β j) 0 := by fun_prop
      have h2 : ContinuousAt (fun t : ℝ => S + A * t) 0 := by fun_prop
      have h3 := h1.eventually_lt h2 (by simpa using hlt)
      filter_upwards [h3] with t ht _ using ht
  have hval : ∀ A t : ℝ, (∀ j, β j ≠ S → α j * t + β j < S + A * t) →
      (∀ j ∈ act, α j * t ≤ A * t) → (∃ j ∈ act, α j * t = A * t) → φ t = S + A * t := by
    intro A t hin hle hex
    apply le_antisymm
    · obtain ⟨j, hj⟩ := (hφ t).1
      have hj' : φ t = α j * t + β j := hj.symm
      rw [hj']
      by_cases hjS : β j = S
      · have := hle j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjS⟩)
        linarith
      · exact (hin j hjS).le
    · obtain ⟨j, hj, hjeq⟩ := hex
      have h' : α j * t + β j ≤ φ t := (hφ t).2 ⟨j, rfl⟩
      have hjS : β j = S := (Finset.mem_filter.mp hj).2
      linarith
  have hright : ∀ᶠ t in 𝓝[>] (0 : ℝ), ψ t = 2 * t ^ 2 + (-α kR) * t + (-S) := by
    filter_upwards [nhdsWithin_le_nhds (hev (α kR)), nhdsWithin_le_nhds h, self_mem_nhdsWithin]
      with t ht hteq htpos
    have htpos' : 0 < t := htpos
    have hφt := hval (α kR) t ht
      (fun j hj => mul_le_mul_of_nonneg_right (hkRmax j hj) htpos'.le) ⟨kR, hkR, rfl⟩
    rw [max_eq_left htpos'.le] at hteq
    linarith
  have hleft : ∀ᶠ t in 𝓝[<] (0 : ℝ), ψ t = 1 * t ^ 2 + (-α kL) * t + (-S) := by
    filter_upwards [nhdsWithin_le_nhds (hev (α kL)), nhdsWithin_le_nhds h, self_mem_nhdsWithin]
      with t ht hteq htneg
    have htneg' : t < 0 := htneg
    have hφt := hval (α kL) t ht
      (fun j hj => mul_le_mul_of_nonpos_right (hkLmin j hj) htneg'.le) ⟨kL, hkL, rfl⟩
    rw [max_eq_right htneg'.le] at hteq
    linarith
  obtain ⟨u, hu, hsubR⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hright
  obtain ⟨l, hl, hsubL⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hleft
  have hcont : Continuous (iteratedDeriv 2 ψ) := hψ.continuous_iteratedDeriv 2 le_rfl
  have hR : ∀ t ∈ Ioo 0 u, iteratedDeriv 2 ψ t = 2 * 2 := fun t ht =>
    iteratedDeriv_two_of_eqOn_quad isOpen_Ioo 2 (-α kR) (-S) (fun s hs => hsubR hs) ht
  have hL : ∀ t ∈ Ioo l 0, iteratedDeriv 2 ψ t = 2 * 1 := fun t ht =>
    iteratedDeriv_two_of_eqOn_quad isOpen_Ioo 1 (-α kL) (-S) (fun s hs => hsubL hs) ht
  have h4 : iteratedDeriv 2 ψ 0 = 2 * 2 := by
    have hT : Tendsto (iteratedDeriv 2 ψ) (𝓝[>] 0) (𝓝 (iteratedDeriv 2 ψ 0)) :=
      (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    have hT' : Tendsto (iteratedDeriv 2 ψ) (𝓝[>] 0) (𝓝 (2 * 2)) :=
      tendsto_const_nhds.congr' (by
        filter_upwards [Ioo_mem_nhdsGT hu] with t ht
        exact (hR t ht).symm)
    exact tendsto_nhds_unique hT hT'
  have h2 : iteratedDeriv 2 ψ 0 = 2 * 1 := by
    have hT : Tendsto (iteratedDeriv 2 ψ) (𝓝[<] 0) (𝓝 (iteratedDeriv 2 ψ 0)) :=
      (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    have hT' : Tendsto (iteratedDeriv 2 ψ) (𝓝[<] 0) (𝓝 (2 * 1)) :=
      tendsto_const_nhds.congr' (by
        filter_upwards [Ioo_mem_nhdsLT hl] with t ht
        exact (hL t ht).symm)
    exact tendsto_nhds_unique hT hT'
  linarith

/-- Item `C/04_R/prose/060` (`companion/chapters/04_R.tex:309`), the wording before 15 October
2026 (W23): "different cells can have different quadratic Hessians and different gradient jumps."
The corrected sentence is `plq2d_hessians_and_varying_jump`. Example: $F(x)=x^2+\max\{x,0\}^2+|x-1|$
on $\R$ (`Vec 1`), with the cells $P_0=\{x\le0\}$, $P_1=\{0\le x\le1\}$, $P_2=\{x\ge1\}$ (two
constraints each) and the quadratic formulas $x^2-x+1$, $2x^2-x+1$, $2x^2+x-1$. $F$ is convex
with unique minimizer $x_*=1/4$ ($F_*=7/8$); the cells are full-dimensional and cover $\R$; the
Hessians differ ($Q_0=1\ne Q_1=2=Q_2$); and the gradient jumps across the cell boundaries differ:
the derivatives of $F$ within the two adjacent cells are $-1,-1$ at $x=0$ (jump $0$, where only the
Hessian changes) and $3,5$ at $x=1$ (jump $2$). The conclusion of Theorem `R:thm:plq` holds
(`plq_covered_objective`). -/
theorem plq_hessians_and_jumps (F : Vec 1 → ℝ)
    (hF_def : ∀ x, F x = x 0 ^ 2 + max (x 0) 0 ^ 2 + |x 0 - 1|) :
    ∃ (a : Fin 3 → Fin 2 → Vec 1) (b : Fin 3 → Fin 2 → ℝ) (P : Fin 3 → Set (Vec 1))
      (Q : Fin 3 → Mat 1) (c : Fin 3 → Vec 1) (d : Fin 3 → ℝ),
      ConvexOn ℝ univ F ∧ (∀ x, F (fun _ => 1 / 4) ≤ F x) ∧
      (∀ x, F x = F (fun _ => 1 / 4) → x = fun _ => 1 / 4) ∧
      (∀ i, P i = {x | ∀ j, dot (a i j) x ≤ b i j}) ∧ (∀ i, (interior (P i)).Nonempty) ∧
      (∀ x, ∃ i, x ∈ P i) ∧ (∀ i, ∀ x ∈ P i, F x = dot x (Q i *ᵥ x) + dot (c i) x + d i) ∧
      Q 0 ≠ Q 1 ∧ Q 1 = Q 2 ∧
      HasDerivWithinAt (fun t : ℝ => F (fun _ => t)) (-1) (Iic 0) 0 ∧
      HasDerivWithinAt (fun t : ℝ => F (fun _ => t)) (-1) (Icc 0 1) 0 ∧
      HasDerivWithinAt (fun t : ℝ => F (fun _ => t)) 3 (Icc 0 1) 1 ∧
      HasDerivWithinAt (fun t : ℝ => F (fun _ => t)) 5 (Ici 1) 1 ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ run : AdmissibleBFGSRun 1 F,
        F (run.x 0) ≤ F (fun _ => 1 / 4) + ε → Tendsto run.x atTop (𝓝 (fun _ => 1 / 4)) := by
  have hdot : ∀ (u : ℝ) (x : Vec 1), dot (fun _ : Fin 1 => u) x = u * x 0 := by
    intro u x; simp [dot]
  set s : Fin 3 → Fin 2 → ℝ := ![![1, 1], ![-1, 1], ![-1, -1]] with hs
  set bb : Fin 3 → Fin 2 → ℝ := ![![0, 0], ![0, 1], ![-1, -1]] with hbb
  set a : Fin 3 → Fin 2 → Vec 1 := fun i j => fun _ => s i j with ha
  set P : Fin 3 → Set (Vec 1) := fun i => {x | ∀ j, dot (a i j) x ≤ bb i j} with hP
  set Q : Fin 3 → Mat 1 := ![!![1], !![2], !![2]] with hQ
  set c : Fin 3 → Vec 1 := ![fun _ => -1, fun _ => -1, fun _ => 1] with hc
  set d : Fin 3 → ℝ := ![1, 1, -1] with hd
  have hl : ConvexOn ℝ univ (fun x : Vec 1 => x 0) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).toLinearMap.convexOn
      convex_univ
  have hconv : ConvexOn ℝ univ F := by
    have h1 : ConvexOn ℝ univ (fun x : Vec 1 => x 0 ^ 2) :=
      Article.Local.sqNorm_convex.congr (fun x _ => by simp [sqNorm])
    have h2 : ConvexOn ℝ univ (fun x : Vec 1 => max (x 0) 0 ^ 2) :=
      Article.Local.convexOn_sq_of_nonneg (hl.sup (convexOn_const 0 convex_univ))
        (fun x => le_max_right _ _)
    have h3 : ConvexOn ℝ univ (fun x : Vec 1 => |x 0 - 1|) :=
      (abs_affine_sum_convex (ι := Unit) (fun _ => fun _ => (1 : ℝ)) (fun _ => 1)).congr
        (fun x _ => by simp [hdot])
    exact ((h1.add h2).add h3).congr (fun x _ => (hF_def x).symm)
  have hline : ∀ t : ℝ, F (fun _ => t) = t ^ 2 + max t 0 ^ 2 + |t - 1| := fun t => hF_def _
  have hval : ∀ x : Vec 1, 7 / 8 ≤ F x ∧ (F x = 7 / 8 → x 0 = 1 / 4) := by
    intro x
    rw [hF_def]
    rcases le_or_lt (x 0) 0 with h0 | h0
    · rw [max_eq_right h0, abs_of_nonpos (by linarith)]
      exact ⟨by nlinarith, fun h => by nlinarith⟩
    · rcases le_or_lt (x 0) 1 with h1 | h1
      · rw [max_eq_left h0.le, abs_of_nonpos (by linarith)]
        refine ⟨by nlinarith [sq_nonneg (x 0 - 1 / 4)], fun h => ?_⟩
        have h' : (x 0 - 1 / 4) ^ 2 = 0 := by nlinarith
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h'
        linarith
      · rw [max_eq_left h0.le, abs_of_pos (by linarith)]
        exact ⟨by nlinarith, fun h => by nlinarith⟩
  have hstar : F (fun _ => 1 / 4) = 7 / 8 := by
    rw [hline, max_eq_left (by norm_num : (0 : ℝ) ≤ 1 / 4),
      abs_of_neg (by norm_num : (1 / 4 : ℝ) - 1 < 0)]
    norm_num
  have hmin : ∀ x, F (fun _ => 1 / 4) ≤ F x := fun x => hstar ▸ (hval x).1
  have huniq : ∀ x, F x = F (fun _ => 1 / 4) → x = fun _ => 1 / 4 := by
    intro x hx
    have h0 := (hval x).2 (hx.trans hstar)
    funext i
    fin_cases i
    exact h0
  have hint : ∀ i, (interior (P i)).Nonempty := by
    intro i
    have hopen : IsOpen {x : Vec 1 | ∀ j, s i j * x 0 < bb i j} := by
      rw [setOf_forall]
      exact isOpen_iInter_of_finite fun j =>
        isOpen_lt (continuous_const.mul (continuous_apply 0)) continuous_const
    have hsub : {x : Vec 1 | ∀ j, s i j * x 0 < bb i j} ⊆ P i := fun x hx j => by
      show dot (fun _ => s i j) x ≤ bb i j
      rw [hdot]
      exact (hx j).le
    have pt : ∃ t : ℝ, ∀ j, s i j * t < bb i j := by
      fin_cases i
      · exact ⟨-1, fun j => by fin_cases j <;> norm_num [hs, hbb]⟩
      · exact ⟨1 / 2, fun j => by fin_cases j <;> norm_num [hs, hbb]⟩
      · exact ⟨2, fun j => by fin_cases j <;> norm_num [hs, hbb]⟩
    obtain ⟨t, ht⟩ := pt
    exact ⟨fun _ => t, interior_maximal hsub hopen ht⟩
  have hmemP : ∀ i x, x ∈ P i ↔ ∀ j, s i j * x 0 ≤ bb i j := by
    intro i x
    exact forall_congr' fun j => by rw [show dot (a i j) x = s i j * x 0 from hdot _ _]
  have hcov : ∀ x, ∃ i, x ∈ P i := by
    intro x
    rcases le_or_lt (x 0) 0 with h0 | h0
    · exact ⟨0, (hmemP 0 x).mpr fun j => by fin_cases j <;> simp [hs, hbb] <;> linarith⟩
    · rcases le_or_lt (x 0) 1 with h1 | h1
      · exact ⟨1, (hmemP 1 x).mpr fun j => by fin_cases j <;> simp [hs, hbb] <;> linarith⟩
      · exact ⟨2, (hmemP 2 x).mpr fun j => by fin_cases j <;> simp [hs, hbb] <;> linarith⟩
  have hrep : ∀ i, ∀ x ∈ P i, F x = dot x (Q i *ᵥ x) + dot (c i) x + d i := by
    intro i x hx
    have h0 := (hmemP i x).mp hx 0
    have h1 := (hmemP i x).mp hx 1
    rw [hF_def]
    fin_cases i
    · have h' : x 0 ≤ 0 := by simpa [hs, hbb] using h0
      simp [hQ, hc, hd, dot, Matrix.mulVec, dotProduct, max_eq_right h',
        abs_of_nonpos (by linarith : x 0 - 1 ≤ 0)]
      ring
    · have h' : 0 ≤ x 0 := by simp [hs, hbb] at h0; linarith
      have h'' : x 0 ≤ 1 := by simpa [hs, hbb] using h1
      simp [hQ, hc, hd, dot, Matrix.mulVec, dotProduct, max_eq_left h',
        abs_of_nonpos (by linarith : x 0 - 1 ≤ 0)]
      ring
    · have h' : 1 ≤ x 0 := by simp [hs, hbb] at h0; linarith
      simp [hQ, hc, hd, dot, Matrix.mulVec, dotProduct,
        max_eq_left (by linarith : (0 : ℝ) ≤ x 0), abs_of_nonneg (by linarith : 0 ≤ x 0 - 1)]
      ring
  have hderiv : ∀ (q c' d' t0 : ℝ) (I : Set ℝ),
      (∀ y ∈ I, F (fun _ => y) = q * y ^ 2 + c' * y + d') → t0 ∈ I →
      HasDerivWithinAt (fun t : ℝ => F (fun _ => t)) (2 * q * t0 + c') I t0 :=
    fun q c' d' t0 I hI ht0 => (hasDerivAt_quad q c' d' t0).hasDerivWithinAt.congr_of_mem hI ht0
  obtain ⟨ε, hε, hconvg⟩ := plq_covered_objective F hconv (fun _ => 1 / 4) hmin huniq
    (fun _ => 2) a bb P (fun _ => rfl) hint hcov Q c d hrep
  refine ⟨a, bb, P, Q, c, d, hconv, hmin, huniq, fun _ => rfl, hint, hcov, hrep, ?_, ?_, ?_, ?_,
    ?_, ?_, ⟨ε, hε, hconvg⟩⟩
  · intro h
    have := congrFun (congrFun h 0) 0
    norm_num [hQ] at this
  · simp [hQ]
  · have := hderiv 1 (-1) 1 0 (Iic 0) (fun y hy => by
      rw [hline, max_eq_right (mem_Iic.mp hy), abs_of_nonpos (by linarith [mem_Iic.mp hy])]
      ring) right_mem_Iic
    simpa using this
  · have := hderiv 2 (-1) 1 0 (Icc 0 1) (fun y hy => by
      rw [hline, max_eq_left hy.1, abs_of_nonpos (by linarith [hy.2])]
      ring) (left_mem_Icc.mpr zero_le_one)
    simpa using this
  · have := hderiv 2 (-1) 1 1 (Icc 0 1) (fun y hy => by
      rw [hline, max_eq_left hy.1, abs_of_nonpos (by linarith [hy.2])]
      ring) (right_mem_Icc.mpr zero_le_one)
    norm_num at this
    exact this
  · have := hderiv 2 1 (-1) 1 (Ici 1) (fun y hy => by
      rw [hline, max_eq_left (by linarith [mem_Ici.mp hy]),
        abs_of_nonneg (by linarith [mem_Ici.mp hy])]
      ring) left_mem_Ici
    norm_num at this
    exact this

/-- Item `C/04_R/prose/059` (`companion/chapters/04_R.tex:309`), first part: "This is broader
than merely having affine pieces plus one common smooth summand". The narrower class is covered:
a convex locally $C^{1,1}$ function $\psi$ ("one common smooth summand"; $C^2$ is included by
`locallyC11_of_contDiff_two`) plus a finite maximum $\varphi$ of affine functions ("affine
pieces"), with a unique minimizer $x_*$, has the conclusion of Theorem
`R:thm:plq` (the article's `Article.Local.loss_plus_polyhedral_penalty`, which treats it as a
convex smooth loss plus a polyhedral, hence piecewise linear-quadratic, regularizer).
Strictness: `plq_broader_2d` (every differentiable summand, hence the $C^{1,1}$ reading of
"smooth") and `plq_broader` (the $C^2$ reading, already in dimension one). -/
theorem smooth_plus_polyhedral_covered {n k : ℕ} (ψ φ G : Vec n → ℝ) (hψ : ConvexOn ℝ univ ψ)
    (hψ11 : CenteredSmoothSublinear.LocallyC11On univ ψ) (p : Fin k → Vec n) (q : Fin k → ℝ)
    (hφ : ∀ x, IsGreatest (Set.range fun j => dot (p j) x + q j) (φ x))
    (hG : ∀ x, G x = ψ x + φ x) (xstar : Vec n) (hmin : ∀ x, G xstar ≤ G x)
    (huniq : ∀ x, G x = G xstar → x = xstar) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ run : AdmissibleBFGSRun n G, G (run.x 0) ≤ G xstar + ε →
      Tendsto run.x atTop (𝓝 xstar) := by
  obtain ⟨ε, hε, h⟩ := Article.Local.loss_plus_polyhedral_penalty ψ φ G hψ hψ11 p q hφ hG xstar
    hmin huniq univ isOpen_univ (mem_univ _)
  exact ⟨ε, hε, fun run hrun => (h run hrun).2.2⟩

/-- Item `C/04_R/prose/059` (`companion/chapters/04_R.tex:309`), strictness: the piecewise
quadratic objective $F(x)=x^2+\max\{x,0\}^2+|x-1|$ of `plq_hessians_and_jumps` is covered (the
conclusion of Theorem `R:thm:plq`), but it is not $\psi+\varphi$ with $\psi:\R^1\to\R$ of class
$C^2$ and $\varphi$ a finite maximum of affine functions: near $0$, $F-\varphi$ would be a $C^2$
function equal to $t^2+\max\{t,0\}^2$ minus affine functions on each side of $0$
(`not_smooth_plus_max_affine`). This settles the $C^2$ reading of "smooth" (with a common $C^2$
summand all cells carry its Hessian, the reason the sentence gives). Under the locally $C^{1,1}$
reading this example is representable ($\psi=x^2+\max\{x,0\}^2$, $\varphi=|x-1|$); that reading
is settled by the two-dimensional witness of `plq_broader_2d`. -/
theorem plq_broader (F : Vec 1 → ℝ)
    (hF_def : ∀ x, F x = x 0 ^ 2 + max (x 0) 0 ^ 2 + |x 0 - 1|) :
    (∃ ε : ℝ, 0 < ε ∧ ∀ run : AdmissibleBFGSRun 1 F,
        F (run.x 0) ≤ F (fun _ => 1 / 4) + ε → Tendsto run.x atTop (𝓝 (fun _ => 1 / 4))) ∧
      ¬ ∃ (ψ φ : Vec 1 → ℝ) (k : ℕ) (p : Fin k → Vec 1) (q : Fin k → ℝ), ContDiff ℝ 2 ψ ∧
        (∀ x, IsGreatest (Set.range fun j => dot (p j) x + q j) (φ x)) ∧
        ∀ x, F x = ψ x + φ x := by
  obtain ⟨_a, _b, _P, _Q, _c, _d, -, -, -, -, -, -, -, -, -, -, -, -, -, hcov⟩ :=
    plq_hessians_and_jumps F hF_def
  refine ⟨hcov, ?_⟩
  rintro ⟨ψ, φ, k, p, q, hψ, hφ, h⟩
  have he : ContDiff ℝ 2 (fun t : ℝ => (fun _ : Fin 1 => t)) :=
    contDiff_pi.mpr fun _ => contDiff_id
  refine not_smooth_plus_max_affine (fun t => ψ (fun _ => t) + (t - 1)) (fun t => φ (fun _ => t))
    ((hψ.comp he).add (contDiff_id.sub contDiff_const)) (fun j => p j 0) q (fun t => ?_) ?_
  · have hfun : (fun j => dot (p j) (fun _ : Fin 1 => t) + q j) = fun j => p j 0 * t + q j :=
      funext fun j => by simp [dot]
    rw [← hfun]
    exact hφ _
  · filter_upwards [Iio_mem_nhds (zero_lt_one : (0 : ℝ) < 1)] with t ht
    have h' := h (fun _ => t)
    rw [hF_def] at h'
    rw [abs_of_neg (by linarith [mem_Iio.mp ht] : t - 1 < 0)] at h'
    linarith


/-! #### A two-dimensional witness for `prose/059` (the reviewer's construction)

$F(u,v)=u^2+v^2+(2+|u|)\,|v|$: a finite convex piecewise linear-quadratic objective (four quadrant
cells with formulas $u^2+v^2\pm uv\pm2v$) with unique minimizer $0$, whose gradient jump across the
cell boundary $v=0$ varies along it, so that it is not a differentiable function plus a finite
maximum of affine functions. -/

/-- A finite maximum of affine functions of one variable is affine on a right and on a left
neighborhood of $0$. -/
theorem max_affine_one_sided {k : ℕ} (φ : ℝ → ℝ) (α β : Fin k → ℝ)
    (hφ : ∀ t, IsGreatest (Set.range fun j => α j * t + β j) (φ t)) :
    ∃ jR jL : Fin k, (∀ᶠ t in 𝓝[>] (0 : ℝ), φ t = φ 0 + α jR * t) ∧
      (∀ᶠ t in 𝓝[<] (0 : ℝ), φ t = φ 0 + α jL * t) := by
  classical
  set S := φ 0 with hS
  have hβS : ∀ j, β j ≤ S := fun j => by
    have h' : α j * 0 + β j ≤ φ 0 := (hφ 0).2 ⟨j, rfl⟩
    simpa using h'
  obtain ⟨j0, hj0⟩ := (hφ 0).1
  have hj0S : β j0 = S := by simpa using hj0
  set act := Finset.univ.filter (fun j => β j = S) with hact
  have hactne : act.Nonempty := ⟨j0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj0S⟩⟩
  obtain ⟨kR, hkR, hkRmax⟩ := act.exists_max_image α hactne
  obtain ⟨kL, hkL, hkLmin⟩ := act.exists_min_image α hactne
  have hev : ∀ A : ℝ, ∀ᶠ t in 𝓝 (0 : ℝ), ∀ j, β j ≠ S → α j * t + β j < S + A * t := by
    intro A
    rw [Filter.eventually_all]
    intro j
    by_cases hj : β j = S
    · exact Filter.Eventually.of_forall (fun t h' => absurd hj h')
    · have hlt : β j < S := lt_of_le_of_ne (hβS j) hj
      have h1 : ContinuousAt (fun t : ℝ => α j * t + β j) 0 := by fun_prop
      have h2 : ContinuousAt (fun t : ℝ => S + A * t) 0 := by fun_prop
      have h3 := h1.eventually_lt h2 (by simpa using hlt)
      filter_upwards [h3] with t ht _ using ht
  have hval : ∀ A t : ℝ, (∀ j, β j ≠ S → α j * t + β j < S + A * t) →
      (∀ j ∈ act, α j * t ≤ A * t) → (∃ j ∈ act, α j * t = A * t) → φ t = S + A * t := by
    intro A t hin hle hex
    apply le_antisymm
    · obtain ⟨j, hj⟩ := (hφ t).1
      have hj' : φ t = α j * t + β j := hj.symm
      rw [hj']
      by_cases hjS : β j = S
      · have := hle j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjS⟩)
        linarith
      · exact (hin j hjS).le
    · obtain ⟨j, hj, hjeq⟩ := hex
      have h' : α j * t + β j ≤ φ t := (hφ t).2 ⟨j, rfl⟩
      have hjS : β j = S := (Finset.mem_filter.mp hj).2
      linarith
  refine ⟨kR, kL, ?_, ?_⟩
  · filter_upwards [nhdsWithin_le_nhds (hev (α kR)), self_mem_nhdsWithin] with t ht htpos
    have htpos' : 0 < t := htpos
    exact hval (α kR) t ht
      (fun j hj => mul_le_mul_of_nonneg_right (hkRmax j hj) htpos'.le) ⟨kR, hkR, rfl⟩
  · filter_upwards [nhdsWithin_le_nhds (hev (α kL)), self_mem_nhdsWithin] with t ht htneg
    have htneg' : t < 0 := htneg
    exact hval (α kL) t ht
      (fun j hj => mul_le_mul_of_nonpos_right (hkLmin j hj) htneg'.le) ⟨kL, hkL, rfl⟩

/-- A function differentiable at $0$ that equals $c+b_1t+t^2$ for small $t>0$ and
$c+b_2t+t^2$ for small $t<0$ has $b_1=b_2$. -/
theorem one_sided_slopes_eq {g : ℝ → ℝ} (hg : DifferentiableAt ℝ g 0) (c b₁ b₂ : ℝ)
    (h0 : g 0 = c)
    (hR : ∀ᶠ t in 𝓝[>] (0 : ℝ), g t = c + b₁ * t + t ^ 2)
    (hL : ∀ᶠ t in 𝓝[<] (0 : ℝ), g t = c + b₂ * t + t ^ 2) : b₁ = b₂ := by
  have hD := hg.hasDerivAt
  have hq : ∀ b : ℝ, HasDerivAt (fun t : ℝ => c + b * t + t ^ 2) b 0 := by
    intro b
    have h1 := (((hasDerivAt_id (0 : ℝ)).const_mul b).const_add c).add (hasDerivAt_pow 2 (0 : ℝ))
    convert h1 using 1
    simp
  have hc : (fun t : ℝ => c + b₁ * t + t ^ 2) 0 = g 0 := by simp [h0]
  have hc' : (fun t : ℝ => c + b₂ * t + t ^ 2) 0 = g 0 := by simp [h0]
  have e1 := (uniqueDiffWithinAt_Ioi (0 : ℝ)).eq_deriv _
    (hD.hasDerivWithinAt.congr_of_eventuallyEq (hR.mono fun t ht => ht.symm) hc)
    (hq b₁).hasDerivWithinAt
  have e2 := (uniqueDiffWithinAt_Iio (0 : ℝ)).eq_deriv _
    (hD.hasDerivWithinAt.congr_of_eventuallyEq (hL.mono fun t ht => ht.symm) hc')
    (hq b₂).hasDerivWithinAt
  rw [← e1, ← e2]

/-- Item `C/04_R/prose/059` (`companion/chapters/04_R.tex:309`), the key step of
`plq_broader_2d`: $F(u,v)=u^2+v^2+(2+|u|)|v|$ is not $\psi+\varphi$ with $\psi$ differentiable
everywhere (so neither $C^1$, $C^{1,1}$, $C^2$ nor $C^\infty$) and $\varphi$ a finite maximum of
affine functions. At $(u,0)$, $0<u<1$, the jump of $\partial_vF$ across $v=0$ is $2(2+u)$; a
differentiable $\psi$ has no jump, so it would be a jump $p_{i,1}-p_{j,1}$ of $\varphi$, of
which there are finitely many. -/
theorem plq2d_not_smooth_plus_max_affine (F : Vec 2 → ℝ)
    (hF_def : ∀ x, F x = x 0 ^ 2 + x 1 ^ 2 + (2 + |x 0|) * |x 1|) :
    ¬ ∃ (ψ φ : Vec 2 → ℝ) (k : ℕ) (p : Fin k → Vec 2) (q : Fin k → ℝ),
      (∀ x, DifferentiableAt ℝ ψ x) ∧
        (∀ x, IsGreatest (Set.range fun j => dot (p j) x + q j) (φ x)) ∧
        ∀ x, F x = ψ x + φ x := by
  classical
  rintro ⟨ψ, φ, k, p, q, hψ, hφ, h⟩
  set D : Set ℝ := Set.range (fun ij : Fin k × Fin k => p ij.1 1 - p ij.2 1) with hD
  have hDfin : D.Finite := Set.finite_range _
  have hmem : ∀ u ∈ Set.Ioo (0 : ℝ) 1, 2 * (2 + u) ∈ D := by
    intro u hu
    set φ₁ : ℝ → ℝ := fun s => φ ![u, s] with hφ₁
    have hφ₁g : ∀ s, IsGreatest (Set.range fun j => p j 1 * s + (p j 0 * u + q j)) (φ₁ s) := by
      intro s
      have hfun : (fun j => dot (p j) ![u, s] + q j) =
          fun j => p j 1 * s + (p j 0 * u + q j) := by
        funext j
        simp [dot, Fin.sum_univ_two]
        ring
      rw [← hfun]
      exact hφ _
    obtain ⟨jR, jL, hR, hL⟩ :=
      max_affine_one_sided φ₁ (fun j => p j 1) (fun j => p j 0 * u + q j) hφ₁g
    have hline : DifferentiableAt ℝ (fun s : ℝ => (![u, s] : Vec 2)) 0 := by
      have he : (fun s : ℝ => (![u, s] : Vec 2)) = fun s => ![u, 0] + s • ![0, 1] := by
        funext s
        ext i
        fin_cases i <;> simp
      rw [he]
      exact (differentiableAt_const _).add (differentiableAt_id.smul_const _)
    have hgd : DifferentiableAt ℝ (fun s : ℝ => ψ ![u, s]) 0 := (hψ _).comp 0 hline
    have hF : ∀ s : ℝ, u ^ 2 + s ^ 2 + (2 + u) * |s| = ψ ![u, s] + φ₁ s := fun s => by
      have := h ![u, s]
      rw [hF_def] at this
      simpa [abs_of_pos hu.1] using this
    have hRg : ∀ᶠ s in 𝓝[>] (0 : ℝ),
        ψ ![u, s] = (u ^ 2 - φ₁ 0) + ((2 + u) - p jR 1) * s + s ^ 2 := by
      filter_upwards [hR, self_mem_nhdsWithin] with s hs hspos
      have hspos' : (0 : ℝ) < s := hspos
      have := hF s
      rw [abs_of_pos hspos', hs] at this
      linarith
    have hLg : ∀ᶠ s in 𝓝[<] (0 : ℝ),
        ψ ![u, s] = (u ^ 2 - φ₁ 0) + (-(2 + u) - p jL 1) * s + s ^ 2 := by
      filter_upwards [hL, self_mem_nhdsWithin] with s hs hsneg
      have hsneg' : s < 0 := hsneg
      have := hF s
      rw [abs_of_neg hsneg', hs] at this
      linarith
    have h0 : (fun s : ℝ => ψ ![u, s]) 0 = u ^ 2 - φ₁ 0 := by
      have := hF 0
      simp only [abs_zero, mul_zero, add_zero] at this
      simp only
      nlinarith
    have hslope := one_sided_slopes_eq hgd _ _ _ h0 hRg hLg
    exact ⟨(jR, jL), by simp only; linarith⟩
  have hinj : InjOn (fun u : ℝ => 2 * (2 + u)) (Set.Ioo (0 : ℝ) 1) := fun a _ b _ hab => by
    simp only at hab
    linarith
  have hinf : ((fun u : ℝ => 2 * (2 + u)) '' Set.Ioo (0 : ℝ) 1).Infinite :=
    Set.Infinite.image hinj (Set.Ioo_infinite (by norm_num : (0 : ℝ) < 1))
  exact hinf (hDfin.subset (by rintro _ ⟨u, hu, rfl⟩; exact hmem u hu))

/-- The quadratics $u^2+v^2+\sigma uv$, $\sigma^2\le1$, are convex. -/
theorem quad_cross_convex (σ : ℝ) (hσ : σ ^ 2 ≤ 1) :
    ConvexOn ℝ univ (fun x : Vec 2 => x 0 ^ 2 + x 1 ^ 2 + σ * (x 0 * x 1)) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hb' : b = 1 - a := by linarith
  subst hb'
  have hpsd : 0 ≤ (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 + σ * ((x 0 - y 0) * (x 1 - y 1)) := by
    nlinarith [sq_nonneg (x 0 - y 0 + σ * (x 1 - y 1) / 2), sq_nonneg (x 1 - y 1),
      mul_nonneg (sub_nonneg.mpr hσ) (sq_nonneg (x 1 - y 1))]
  nlinarith [mul_nonneg (mul_nonneg ha hb) hpsd]

/-- Item `C/04_R/prose/059` (`companion/chapters/04_R.tex:309`), the two-dimensional witness is
covered: $F(u,v)=u^2+v^2+(2+|u|)|v|$ is finite and convex with unique minimizer $0$; it is
piecewise linear-quadratic on the four closed quadrants $P_i$ (full-dimensional, covering $\R^2$),
with formulas $u^2+v^2+\sigma_iuv+2\tau_iv$, $\sigma_i,\tau_i=\pm1$, whose Hessians differ
($Q_0\ne Q_1$); and the conclusion of Theorem `R:thm:plq` holds (`plq_covered_objective`). -/
theorem plq2d_covered (F : Vec 2 → ℝ)
    (hF_def : ∀ x, F x = x 0 ^ 2 + x 1 ^ 2 + (2 + |x 0|) * |x 1|) :
    ConvexOn ℝ univ F ∧ (∀ x, F 0 ≤ F x) ∧ (∀ x, F x = F 0 → x = 0) ∧
      (∃ (a : Fin 4 → Fin 2 → Vec 2) (b : Fin 4 → Fin 2 → ℝ) (P : Fin 4 → Set (Vec 2))
        (Q : Fin 4 → Mat 2) (c : Fin 4 → Vec 2) (d : Fin 4 → ℝ),
        (∀ i, P i = {x | ∀ j, dot (a i j) x ≤ b i j}) ∧ (∀ i, (interior (P i)).Nonempty) ∧
          (∀ x, ∃ i, x ∈ P i) ∧
          (∀ i, ∀ x ∈ P i, F x = dot x (Q i *ᵥ x) + dot (c i) x + d i) ∧ Q 0 ≠ Q 1) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ run : AdmissibleBFGSRun 2 F, F (run.x 0) ≤ F 0 + ε →
        Tendsto run.x atTop (𝓝 0) := by
  have hF0 : F 0 = 0 := by simp [hF_def]
  have hc1 : ConvexOn ℝ univ (fun x : Vec 2 => x 1) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).toLinearMap.convexOn
      convex_univ
  have hc2 : ConvexOn ℝ univ (fun x : Vec 2 => -x 1) :=
    (-(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1)).toLinearMap.convexOn
      convex_univ
  have habs : ConvexOn ℝ univ (fun x : Vec 2 => 2 * |x 1|) := by
    have := (hc1.sup hc2).smul (show (0 : ℝ) ≤ 2 by norm_num)
    refine this.congr (fun x _ => ?_)
    simp only [Pi.smul_apply, Pi.sup_apply, smul_eq_mul]
    rw [max_def]
    split_ifs with h
    · rw [abs_of_nonpos (by linarith)]
    · rw [abs_of_pos (by linarith)]
  have hq := (quad_cross_convex 1 (by norm_num)).sup (quad_cross_convex (-1) (by norm_num))
  have hconv : ConvexOn ℝ univ F := by
    refine (hq.add habs).congr (fun x _ => ?_)
    simp only [Pi.add_apply, Pi.sup_apply]
    rw [hF_def]
    have hm : max (x 0 ^ 2 + x 1 ^ 2 + 1 * (x 0 * x 1)) (x 0 ^ 2 + x 1 ^ 2 + -1 * (x 0 * x 1)) =
        x 0 ^ 2 + x 1 ^ 2 + |x 0| * |x 1| := by
      rw [← abs_mul]
      rcases le_total 0 (x 0 * x 1) with h | h
      · rw [abs_of_nonneg h, max_eq_left (by linarith)]; ring
      · rw [abs_of_nonpos h, max_eq_right (by linarith)]; ring
    rw [hm]
    ring
  have hmin : ∀ x, F 0 ≤ F x := fun x => by
    rw [hF0, hF_def]
    positivity
  have huniq : ∀ x, F x = F 0 → x = 0 := by
    intro x hx
    rw [hF0, hF_def] at hx
    have h1 : 0 ≤ (2 + |x 0|) * |x 1| := by positivity
    have h0 : x 0 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
    have h1' : x 1 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
    ext i
    fin_cases i
    · exact h0
    · exact h1'
  -- the four quadrant cells: the sign of `u` is `su i`, the sign of `v` is `sv i`
  set su : Fin 4 → ℝ := ![1, -1, -1, 1] with hsu
  set sv : Fin 4 → ℝ := ![1, 1, -1, -1] with hsv
  have hsu2 : ∀ i, su i * su i = 1 := by intro i; fin_cases i <;> norm_num [hsu]
  have hsv2 : ∀ i, sv i * sv i = 1 := by intro i; fin_cases i <;> norm_num [hsv]
  set a : Fin 4 → Fin 2 → Vec 2 := fun i => ![![-su i, 0], ![0, -sv i]] with ha
  set b : Fin 4 → Fin 2 → ℝ := fun _ _ => 0 with hb
  set P : Fin 4 → Set (Vec 2) := fun i => {x | ∀ j, dot (a i j) x ≤ b i j} with hP
  set Q : Fin 4 → Mat 2 := fun i => !![1, su i * sv i / 2; su i * sv i / 2, 1] with hQ
  set c : Fin 4 → Vec 2 := fun i => ![0, 2 * sv i] with hc
  set d : Fin 4 → ℝ := fun _ => 0 with hd
  have hmemP : ∀ i x, x ∈ P i ↔ 0 ≤ su i * x 0 ∧ 0 ≤ sv i * x 1 := by
    intro i x
    simp only [hP, ha, hb, mem_setOf_eq, Fin.forall_fin_two, dot, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    constructor
    · rintro ⟨h1, h2⟩; constructor <;> linarith
    · rintro ⟨h1, h2⟩; constructor <;> linarith
  have hint : ∀ i, (interior (P i)).Nonempty := by
    intro i
    have hopen : IsOpen {x : Vec 2 | 0 < su i * x 0 ∧ 0 < sv i * x 1} :=
      (isOpen_lt continuous_const (continuous_const.mul (continuous_apply 0))).inter
        (isOpen_lt continuous_const (continuous_const.mul (continuous_apply 1)))
    have hsub : {x : Vec 2 | 0 < su i * x 0 ∧ 0 < sv i * x 1} ⊆ P i := fun x hx =>
      (hmemP i x).mpr ⟨hx.1.le, hx.2.le⟩
    refine ⟨![su i, sv i], interior_maximal hsub hopen ?_⟩
    simp only [mem_setOf_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [hsu2, hsv2]
    norm_num
  have hcov : ∀ x, ∃ i, x ∈ P i := by
    intro x
    rcases le_total 0 (x 0) with h0 | h0 <;> rcases le_total 0 (x 1) with h1 | h1
    · exact ⟨0, (hmemP 0 x).mpr ⟨by simp [hsu]; linarith, by simp [hsv]; linarith⟩⟩
    · exact ⟨3, (hmemP 3 x).mpr ⟨by simp [hsu]; linarith, by simp [hsv]; linarith⟩⟩
    · exact ⟨1, (hmemP 1 x).mpr ⟨by simp [hsu]; linarith, by simp [hsv]; linarith⟩⟩
    · exact ⟨2, (hmemP 2 x).mpr ⟨by simp [hsu]; linarith, by simp [hsv]; linarith⟩⟩
  have hrep : ∀ i, ∀ x ∈ P i, F x = dot x (Q i *ᵥ x) + dot (c i) x + d i := by
    intro i x hx
    obtain ⟨h0, h1⟩ := (hmemP i x).mp hx
    have habs0 : |x 0| = su i * x 0 := by
      have : |su i * x 0| = su i * x 0 := abs_of_nonneg h0
      rw [abs_mul] at this
      have hs : |su i| = 1 := by fin_cases i <;> norm_num [hsu]
      rw [hs, one_mul] at this
      exact this
    have habs1 : |x 1| = sv i * x 1 := by
      have : |sv i * x 1| = sv i * x 1 := abs_of_nonneg h1
      rw [abs_mul] at this
      have hs : |sv i| = 1 := by fin_cases i <;> norm_num [hsv]
      rw [hs, one_mul] at this
      exact this
    rw [hF_def, habs0, habs1]
    simp only [hQ, hc, hd, dot, Fin.sum_univ_two, Matrix.mulVec, dotProduct, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    ring
  have hQ01 : Q 0 ≠ Q 1 := by
    intro h
    have h01 := congrFun (congrFun h 0) 1
    simp only [hQ, hsu, hsv, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one] at h01
    norm_num at h01
  exact ⟨hconv, hmin, huniq, ⟨a, b, P, Q, c, d, fun _ => rfl, hint, hcov, hrep, hQ01⟩,
    plq_covered_objective F hconv 0 hmin huniq (fun _ => 2) a b P (fun _ => rfl) hint hcov Q c d
      hrep⟩

/-- The gradient jump of the two-dimensional witness varies along a cell boundary: for every $u$,
the derivative of $s\mapsto F(u,s)$ at $s=0$ is $2+|u|$ within $v\ge0$ and $-(2+|u|)$ within
$v\le0$, so the jump of $\partial_vF$ across $v=0$ at $(u,0)$ is $2(2+|u|)$. -/
theorem plq2d_jump (F : Vec 2 → ℝ)
    (hF_def : ∀ x, F x = x 0 ^ 2 + x 1 ^ 2 + (2 + |x 0|) * |x 1|) (u : ℝ) :
    HasDerivWithinAt (fun s : ℝ => F ![u, s]) (2 + |u|) (Ici 0) 0 ∧
      HasDerivWithinAt (fun s : ℝ => F ![u, s]) (-(2 + |u|)) (Iic 0) 0 := by
  have hline : ∀ s : ℝ, F ![u, s] = u ^ 2 + s ^ 2 + (2 + |u|) * |s| := fun s => by
    rw [hF_def]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  constructor
  · have h := ((hasDerivAt_quad 1 (2 + |u|) (u ^ 2) 0).hasDerivWithinAt (s := Ici 0)).congr_of_mem
      (f₁ := fun s : ℝ => F ![u, s]) (fun y hy => by
        show F ![u, y] = 1 * y ^ 2 + (2 + |u|) * y + u ^ 2
        rw [hline, abs_of_nonneg (mem_Ici.mp hy)]
        ring) left_mem_Ici
    simpa using h
  · have h := ((hasDerivAt_quad 1 (-(2 + |u|)) (u ^ 2) 0).hasDerivWithinAt
      (s := Iic 0)).congr_of_mem (f₁ := fun s : ℝ => F ![u, s]) (fun y hy => by
        show F ![u, y] = 1 * y ^ 2 + -(2 + |u|) * y + u ^ 2
        rw [hline, abs_of_nonpos (mem_Iic.mp hy)]
        ring) right_mem_Iic
    simpa using h

/-- Item `C/04_R/prose/060` (`companion/chapters/04_R.tex:309`), as corrected on 15 October 2026
(wording point W23; before "different cells can have different quadratic Hessians and different
gradient jumps."): "different cells can have different quadratic Hessians, and the gradient jump
can vary along a cell boundary (for example $u^2+v^2+(2+|u|)|v|$ near the origin)." For
$F(u,v)=u^2+v^2+(2+|u|)|v|$: $F$ is finite and convex with unique minimizer $0$, quadratic on the
four closed quadrants (full-dimensional cells covering $\R^2$) whose Hessians differ
($Q_0\ne Q_1$), and Theorem `R:thm:plq` applies to it (`plq2d_covered`); along the cell boundary
$v=0$ the one-sided derivatives of $s\mapsto F(u,s)$ at $s=0$ are $\pm(2+|u|)$, so the jump of
$\partial_vF$ across $v=0$ at $(u,0)$ is $2(2+|u|)$ (`plq2d_jump`), and it takes different values
at boundary points arbitrarily near the origin. -/
theorem plq2d_hessians_and_varying_jump (F : Vec 2 → ℝ)
    (hF_def : ∀ x, F x = x 0 ^ 2 + x 1 ^ 2 + (2 + |x 0|) * |x 1|) :
    (ConvexOn ℝ univ F ∧ (∀ x, F 0 ≤ F x) ∧ (∀ x, F x = F 0 → x = 0) ∧
      (∃ (a : Fin 4 → Fin 2 → Vec 2) (b : Fin 4 → Fin 2 → ℝ) (P : Fin 4 → Set (Vec 2))
        (Q : Fin 4 → Mat 2) (c : Fin 4 → Vec 2) (d : Fin 4 → ℝ),
        (∀ i, P i = {x | ∀ j, dot (a i j) x ≤ b i j}) ∧ (∀ i, (interior (P i)).Nonempty) ∧
          (∀ x, ∃ i, x ∈ P i) ∧
          (∀ i, ∀ x ∈ P i, F x = dot x (Q i *ᵥ x) + dot (c i) x + d i) ∧ Q 0 ≠ Q 1) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ run : AdmissibleBFGSRun 2 F, F (run.x 0) ≤ F 0 + ε →
        Tendsto run.x atTop (𝓝 0)) ∧
      (∀ u : ℝ, HasDerivWithinAt (fun s : ℝ => F ![u, s]) (2 + |u|) (Ici 0) 0 ∧
        HasDerivWithinAt (fun s : ℝ => F ![u, s]) (-(2 + |u|)) (Iic 0) 0) ∧
      ∀ ε : ℝ, 0 < ε → ∃ u₁ u₂ : ℝ, |u₁| < ε ∧ |u₂| < ε ∧ 2 * (2 + |u₁|) ≠ 2 * (2 + |u₂|) := by
  refine ⟨plq2d_covered F hF_def, plq2d_jump F hF_def, fun ε hε => ⟨0, ε / 2, by simpa using hε,
    ?_, ?_⟩⟩
  · rw [abs_of_pos (half_pos hε)]
    linarith
  · rw [abs_zero, abs_of_pos (half_pos hε)]
    intro h
    linarith

/-- Item `C/04_R/prose/059` (`companion/chapters/04_R.tex:309`), strictness under the locally
$C^{1,1}$ reading of "smooth" (the reading of lines 300-307, whose "smooth extensions" are the
$C^{1,1}$ extensions of Theorem `R:thm:plq`, and of the article's parallel Corollary `art:plq`):
$F(u,v)=u^2+v^2+(2+|u|)|v|$ on $\R^2$ is a finite convex piecewise linear-quadratic objective with
unique minimizer $0$ covered by Theorem `R:thm:plq` (`plq2d_covered`), but it is not $\psi+\varphi$
with $\psi$ locally $C^{1,1}$ ("one common smooth summand") and $\varphi$ a finite maximum of
affine functions ("affine pieces"); no everywhere differentiable $\psi$ works
(`plq2d_not_smooth_plus_max_affine`). The one-dimensional `plq_broader` settles the $C^2$ reading
already in dimension one (under the $C^{1,1}$ reading its example is representable). -/
theorem plq_broader_2d (F : Vec 2 → ℝ)
    (hF_def : ∀ x, F x = x 0 ^ 2 + x 1 ^ 2 + (2 + |x 0|) * |x 1|) :
    (∃ ε : ℝ, 0 < ε ∧ ∀ run : AdmissibleBFGSRun 2 F, F (run.x 0) ≤ F 0 + ε →
        Tendsto run.x atTop (𝓝 0)) ∧
      ¬ ∃ (ψ φ : Vec 2 → ℝ) (k : ℕ) (p : Fin k → Vec 2) (q : Fin k → ℝ),
        CenteredSmoothSublinear.LocallyC11On univ ψ ∧
          (∀ x, IsGreatest (Set.range fun j => dot (p j) x + q j) (φ x)) ∧
          ∀ x, F x = ψ x + φ x := by
  obtain ⟨-, -, -, -, hcov⟩ := plq2d_covered F hF_def
  refine ⟨hcov, fun ⟨ψ, φ, k, p, q, hψ, hφ, h⟩ => plq2d_not_smooth_plus_max_affine F hF_def
    ⟨ψ, φ, k, p, q, fun x => hψ.1.differentiableAt univ_mem, hφ, h⟩⟩


/-! ### Section 4.6.1: norms, gauges and mixed powers (lines 326-342) -/

/-- A finite sublinear function: subadditive and positively homogeneous of degree one. -/
def Sublinear {n : ℕ} (γ : Vec n → ℝ) : Prop :=
  (∀ x y, γ (x + y) ≤ γ x + γ y) ∧ ∀ t : ℝ, 0 ≤ t → ∀ x, γ (t • x) = t * γ x

/-- Finite sublinear functions are exactly the finite convex positively homogeneous functions. -/
theorem sublinear_iff {n : ℕ} (γ : Vec n → ℝ) :
    Sublinear γ ↔ ConvexOn ℝ univ γ ∧ Homogeneous.PositiveDegreeOne γ := by
  constructor
  · rintro ⟨hadd, hhom⟩
    refine ⟨⟨convex_univ, fun x _ y _ a b ha hb _ => ?_⟩, hhom⟩
    calc γ (a • x + b • y) ≤ γ (a • x) + γ (b • y) := hadd _ _
      _ = a • γ x + b • γ y := by rw [hhom a ha, hhom b hb]; rfl
  · rintro ⟨hc, hh⟩
    obtain ⟨h1, h2, -⟩ := Article.Global.homogeneous_sublinear hc hh
    exact ⟨h1, h2⟩

/-- Item `C/04_R/disp/041` (`companion/chapters/04_R.tex:329-331`): "For a finite sublinear
$\gamma$ centered at zero, $\gamma((1-t)z)=(1-t)\gamma(z)$, $0\le t<1$." -/
theorem sublinear_radial {n : ℕ} {γ : Vec n → ℝ} (hγ : Sublinear γ) (z : Vec n) (t : ℝ)
    (_ht0 : 0 ≤ t) (ht1 : t < 1) : γ ((1 - t) • z) = (1 - t) * γ z :=
  hγ.2 (1 - t) (by linarith) z

/-- Item `C/04_R/prose/064` (`companion/chapters/04_R.tex:332`): "There is exactly zero radial
Taylor error, regardless of angular nonsmoothness." For finite sublinear $\gamma$ centered at zero,
at every point $z$ where $\gamma$ is differentiable (whatever its nonsmoothness elsewhere),
$\gamma(z-tz)-\gamma(z)+t\nabla\gamma(z)^Tz=0$ for $0\le t<1$. -/
theorem sublinear_zero_radial_error {n : ℕ} {γ : Vec n → ℝ} (hγ : Sublinear γ) (z p : Vec n)
    (hp : HasFDerivAt γ (gradientFunctional p) z) (t : ℝ) (_ht0 : 0 ≤ t) (ht1 : t < 1) :
    γ (z - t • z) - γ z + t * dot p z = 0 := by
  obtain ⟨hc, hh⟩ := (sublinear_iff γ).mp hγ
  exact Article.Global.homogeneous_inward_remainder_zero hc hh hp t ht1.le

/-- Item `C/04_R/prose/065` (`companion/chapters/04_R.tex:332`): "This includes polyhedral
norms, Euclidean norms, the spectral norm and nuclear norm when centered at zero, and asymmetric
finite gauges." Each of the following is a finite sublinear function: a finite maximum of linear
forms $\max_ia_i^Tx$ (polyhedral norms and gauges), the Euclidean norm, the spectral norm
(Euclidean operator norm, `CenteredSpectral.objective_operator_norm`) and the nuclear norm (sum of
singular values, `RectangularNuclear.objective_singularValues`) of an $m\times n$ matrix in its
coordinates, and the asymmetric gauge $\max(x,-2x)$ on $\R$, for which $F(-1)\ne F(1)$. -/
theorem sublinear_examples :
    (∀ (n m : ℕ) (a : Fin m → Vec n) (F : Vec n → ℝ),
      (∀ x, IsGreatest (Set.range fun i => dot (a i) x) (F x)) → Sublinear F) ∧
    (∀ n : ℕ, Sublinear (fun x : Vec n => ‖euclideanVector x‖)) ∧
    (∀ m n : ℕ, Sublinear (CenteredSpectral.objective (m := m) (n := n))) ∧
    (∀ m n : ℕ, Sublinear (RectangularNuclear.objective (m := m) (n := n))) ∧
    (Sublinear (fun x : Vec 1 => max (x 0) (-2 * x 0)) ∧
      (fun x : Vec 1 => max (x 0) (-2 * x 0)) (-fun _ => 1) ≠
        (fun x : Vec 1 => max (x 0) (-2 * x 0)) (fun _ => 1)) := by
  refine ⟨fun n m a F hF =>
      (sublinear_iff F).mpr (Article.Global.maxLinear_convex_homogeneous a F hF),
    fun n =>
      (sublinear_iff _).mpr ⟨(Article.Global.euclideanSeminorm n).convexOn, fun t ht x => ?_⟩,
    fun m n => (sublinear_iff _).mpr ⟨CenteredSpectral.objective_convex m n,
      CenteredSpectral.objective_homogeneous m n⟩,
    fun m n => (sublinear_iff _).mpr ⟨RectangularNuclear.objective_convex m n,
      RectangularNuclear.objective_homogeneous m n⟩,
    (sublinear_iff _).mpr ⟨Article.Global.maxAsym_convex, fun t ht x => ?_⟩, by norm_num⟩
  · show ‖euclideanVector (t • x)‖ = t * ‖euclideanVector x‖
    rw [Article.Global.norm_euclideanVector_smul, abs_of_nonneg ht]
  · simp only [Pi.smul_apply, smul_eq_mul]
    rw [show -2 * (t * x 0) = t * (-2 * x 0) by ring, mul_max_of_nonneg _ _ ht]

/-- Item `C/04_R/prose/065` (`companion/chapters/04_R.tex:332`), the class of asymmetric finite
gauges: the gauge (Minkowski functional) $\gamma_S(x)=\inf\{t>0:x\in tS\}$ of every convex
absorbent set $S\subset\R^n$, symmetric or not, is a finite sublinear function, and it is
nonnegative (Mathlib's `gauge`, with `gauge_add_le`, `gauge_smul_of_nonneg`, `gauge_nonneg`).
`sublinear_examples` adds an explicit asymmetric example, $\max(x,-2x)$. -/
theorem gauge_sublinear {n : ℕ} (S : Set (Vec n)) (hS : Convex ℝ S) (ha : Absorbent ℝ S) :
    Sublinear (gauge S) ∧ ∀ x, 0 ≤ gauge S x :=
  ⟨⟨gauge_add_le hS ha, fun t ht x => by rw [gauge_smul_of_nonneg ht]; rfl⟩,
    fun _ => gauge_nonneg _⟩

/-- Item `C/04_R/disp/042` (`companion/chapters/04_R.tex:335-337`): "For nonnegative $\gamma$ and
$p\ge1$, $\gamma((1-t)z)^p=(1-t)^p\gamma(z)^p$", for finite sublinear $\gamma$ and $0\le t<1$
(real powers). -/
theorem powered_radial {n : ℕ} {γ : Vec n → ℝ} (hγ : Sublinear γ) (hγ0 : ∀ x, 0 ≤ γ x) (p : ℝ)
    (_hp : 1 ≤ p) (z : Vec n) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    γ ((1 - t) • z) ^ p = (1 - t) ^ p * γ z ^ p := by
  rw [sublinear_radial hγ z t ht0 ht1, Real.mul_rpow (by linarith) (hγ0 z)]

/-- Item `C/04_R/prose/066` (`companion/chapters/04_R.tex:338`): "On $0\le t\le1/2$, the second
derivative in $t$ is bounded uniformly on any bounded set of $z$." For finite sublinear
$\gamma\ge0$ and $p\ge1$ (the library's `RadialPower.powered_radial_second_derivative_bounded`). -/
theorem powered_second_derivative_bounded {n : ℕ} {γ : Vec n → ℝ} (hγ : Sublinear γ)
    (hγ0 : ∀ x, 0 ≤ γ x) {p : ℝ} (hp : 1 ≤ p) {Z : Set (Vec n)} (hZ : Bornology.IsBounded Z) :
    ∃ M : ℝ, 0 < M ∧ ∀ z ∈ Z, ∀ t ∈ Icc (0 : ℝ) (1 / 2),
      |deriv (deriv (fun u : ℝ => γ ((1 - u) • z) ^ p)) t| ≤ M := by
  obtain ⟨hc, hh⟩ := (sublinear_iff γ).mp hγ
  exact RadialPower.powered_radial_second_derivative_bounded hc hh hγ0 hp hZ

/-- Item `C/04_R/prose/067` (`companion/chapters/04_R.tex:338`): "This includes $1<p<2$, without
demanding a Lipschitz full gradient near zero." For $1<p<2$ and $\gamma(x)=|x|$ on $\R$: the bound
of `powered_second_derivative_bounded` holds for $|x|^p$, whose derivative $p\,x^{p-1}$ ($x>0$) is
Lipschitz on no interval $(0,\delta)$. -/
theorem power_without_lipschitz_gradient {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    Sublinear (fun x : Vec 1 => |x 0|) ∧
      (∀ s : ℝ, 0 < s → HasDerivAt (fun t : ℝ => |t| ^ p) (p * s ^ (p - 1)) s) ∧
      ¬ ∃ L δ : ℝ, 0 < δ ∧ ∀ s t : ℝ, 0 < s → s < δ → 0 < t → t < δ →
        |p * s ^ (p - 1) - p * t ^ (p - 1)| ≤ L * |s - t| := by
  refine ⟨(sublinear_iff _).mpr ⟨Article.Global.abs_coord_convex, fun t ht x => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg ht]⟩, fun s hs => ?_, ?_⟩
  · have h := (Real.hasDerivAt_rpow_const (p := p) (Or.inl hs.ne')).congr_of_eventuallyEq
      (show (fun t : ℝ => |t| ^ p) =ᶠ[𝓝 s] fun t => t ^ p from by
        filter_upwards [eventually_gt_nhds hs] with t ht
        rw [abs_of_pos ht])
    exact h
  · rintro ⟨L, δ, hδ, hL⟩
    -- at s and 2s the difference quotient is p (2^(p-1) - 1) s^(p-2), unbounded as s → 0+
    have hc : 0 < p * ((2 : ℝ) ^ (p - 1) - 1) := by
      have h1 : (1 : ℝ) < 2 ^ (p - 1) := Real.one_lt_rpow (by norm_num) (by linarith)
      exact mul_pos (by linarith) (by linarith)
    set s := min (δ / 4) ((p * ((2 : ℝ) ^ (p - 1) - 1) / (|L| + 1)) ^ (1 / (2 - p)) / 2) with hs_def
    have hs0 : 0 < s := lt_min (by positivity) (by positivity)
    have hsδ : 2 * s < δ := by have := min_le_left (δ / 4) ((p * ((2 : ℝ) ^ (p - 1) - 1) /
      (|L| + 1)) ^ (1 / (2 - p)) / 2); linarith
    have h := hL (2 * s) s (by positivity) hsδ hs0 (by linarith)
    have hpow : (2 * s) ^ (p - 1) = 2 ^ (p - 1) * s ^ (p - 1) :=
      Real.mul_rpow (by norm_num) hs0.le
    rw [hpow, show 2 * s - s = s by ring, abs_of_pos hs0] at h
    have hpos : 0 ≤ p * (2 ^ (p - 1) * s ^ (p - 1)) - p * s ^ (p - 1) := by
      have : 0 < s ^ (p - 1) := Real.rpow_pos_of_pos hs0 _
      nlinarith
    rw [abs_of_nonneg hpos] at h
    -- h : p (2^(p-1) - 1) s^(p-1) ≤ L s, so s^(p-2) ≤ L / (p (2^(p-1)-1))
    have hsp : s ^ (p - 1) = s ^ (p - 2) * s := by
      rw [show p - 1 = (p - 2) + 1 by ring, Real.rpow_add hs0, Real.rpow_one]
    have h2 : p * ((2 : ℝ) ^ (p - 1) - 1) * s ^ (p - 2) ≤ |L| := by
      have hL' : L * s ≤ |L| * s := mul_le_mul_of_nonneg_right (le_abs_self L) hs0.le
      rw [hsp] at h
      have h3 : (p * ((2 : ℝ) ^ (p - 1) - 1) * s ^ (p - 2)) * s ≤ |L| * s := by nlinarith
      exact le_of_mul_le_mul_right h3 hs0
    -- but s ≤ (c/(|L|+1))^(1/(2-p)) / 2 gives s^(p-2) ≥ 2^(2-p) (|L|+1)/c > (|L|+1)/c
    set c := p * ((2 : ℝ) ^ (p - 1) - 1) with hc_def
    have hs1 : s ≤ (c / (|L| + 1)) ^ (1 / (2 - p)) / 2 := min_le_right _ _
    have hbase : 0 < c / (|L| + 1) := by positivity
    have hs2 : s < (c / (|L| + 1)) ^ (1 / (2 - p)) := by
      have : 0 < (c / (|L| + 1)) ^ (1 / (2 - p)) := Real.rpow_pos_of_pos hbase _
      linarith
    have hneg : p - 2 < 0 := by linarith
    have hmono : ((c / (|L| + 1)) ^ (1 / (2 - p))) ^ (p - 2) < s ^ (p - 2) :=
      Real.rpow_lt_rpow_of_neg hs0 hs2 hneg
    have h2p : (2 - p) ≠ 0 := by linarith
    rw [← Real.rpow_mul hbase.le, show 1 / (2 - p) * (p - 2) = -1 by
      rw [div_mul_eq_mul_div, one_mul, show p - 2 = -(2 - p) by ring, neg_div, div_self h2p],
      Real.rpow_neg_one, inv_div] at hmono
    have h4 : c * ((|L| + 1) / c) < c * s ^ (p - 2) := mul_lt_mul_of_pos_left hmono hc
    rw [mul_div_cancel₀ _ hc.ne'] at h4
    linarith


/-- Local $C^{1,1}$ regularity on $\R^n$ is invariant under translation. -/
theorem locallyC11_translate {n : ℕ} {ψ : Vec n → ℝ}
    (hψ : CenteredSmoothSublinear.LocallyC11On univ ψ) (c : Vec n) :
    CenteredSmoothSublinear.LocallyC11On univ (fun x => ψ (x - c)) := by
  obtain ⟨hd, hl⟩ := hψ
  refine ⟨fun x _ => ?_, ?_⟩
  · have h : DifferentiableAt ℝ ψ (x - c) := (hd (x - c) (mem_univ _)).differentiableAt univ_mem
    exact ((differentiableAt_comp_sub c).mpr h).differentiableWithinAt
  · have he : fderiv ℝ (fun x => ψ (x - c)) = fun x => fderiv ℝ ψ (x - c) :=
      funext fun x => fderiv_comp_sub c
    rw [he]
    have hl' : LocallyLipschitz (fderiv ℝ ψ) := locallyLipschitzOn_univ.mp hl
    have ht : LocallyLipschitz (fun x : Vec n => x - c) :=
      (LipschitzWith.of_dist_le_mul (K := 1) fun x y => by simp [dist_sub_right]).locallyLipschitz
    exact (hl'.comp ht).locallyLipschitzOn

/-- Item `C/04_R/disp/043` (`companion/chapters/04_R.tex:339-341`): "Therefore finite sums of
differently powered, linearly composed gauges,
\[ F(x_*+z)=\psi(z)+\sum_j\gamma_j(A_jz)^{p_j},\qquad p_j\ge1, \]
are covered when $\psi$ is convex $C^{1,1}$ locally and the full objective has the required
minimizer and compact sublevel." Here $F$ is finite and convex with minimizer $x_*$,
$K=\{F\le b\}$ is compact with $b>F_*$, $\psi$ is convex and locally $C^{1,1}$ on $\R^n$, the
$\gamma_j\ge0$ are finite sublinear (gauges), the $A_j$ are matrices and the representation holds
for every $z$. "Covered": (IR) and (RS) hold on $K$, and every admissible run starting in $K$
converges in value and in distance to $\arg\min F$, and to $x_*$ when the minimizer is unique
(the library's `RadialPower.mixed_powers_inward` and
`AdmissibleBFGSRun.mixed_linear_powers_convergence`; the representation is global, so the
compact sublevel lies in its region). -/
theorem mixed_powers_covered {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F) (xstar : Vec n)
    (hmin : ∀ x, F xstar ≤ F x) (b : ℝ) (hb : F xstar < b) (K : Set (Vec n))
    (hK_def : K = {x | F x ≤ b}) (hK : IsCompact K)
    (ψ : Vec n → ℝ) (_hψ : ConvexOn ℝ univ ψ) (hψ11 : CenteredSmoothSublinear.LocallyC11On univ ψ)
    {ι : Type*} [Fintype ι] (m : ι → ℕ) (γ : ∀ j, Vec (m j) → ℝ) (hγ : ∀ j, Sublinear (γ j))
    (hγ0 : ∀ j x, 0 ≤ γ j x) (A : ∀ j, Matrix (Fin (m j)) (Fin n) ℝ) (p : ι → ℝ)
    (hp : ∀ j, 1 ≤ p j) (hrep : ∀ z, F (xstar + z) = ψ z + ∑ j, γ j (A j *ᵥ z) ^ p j) :
    IR F xstar K ∧ RS F xstar K ∧
      ∀ run : AdmissibleBFGSRun n F, F (run.x 0) ≤ b →
        Tendsto (fun k => F (run.x k)) atTop (𝓝 (F xstar)) ∧
          Tendsto (fun k => euclideanSolutionDistance F (run.x k)) atTop (𝓝 0) ∧
          ((∀ x, F x = F xstar → x = xstar) → Tendsto run.x atTop (𝓝 xstar)) := by
  have hγc : ∀ j, ConvexOn ℝ univ (γ j) := fun j => ((sublinear_iff _).mp (hγ j)).1
  have hγh : ∀ j, Homogeneous.PositiveDegreeOne (γ j) := fun j => ((sublinear_iff _).mp (hγ j)).2
  have hψ' := locallyC11_translate hψ11 xstar
  have hrep' : ∀ x ∈ (univ : Set (Vec n)), F x = (fun x => ψ (x - xstar)) x +
      ∑ j, (γ j ((Matrix.mulVecLin (A j)) (x - xstar))) ^ (p j) := by
    intro x _
    have h := hrep (x - xstar)
    rw [show xstar + (x - xstar) = x by abel] at h
    exact h
  have hIR : IR F xstar K := by
    rw [IR_iff_library]
    exact RadialPower.mixed_powers_inward hF (Γ := fun j => γ j ∘ Matrix.mulVecLin (A j))
      (fun j => RadialPower.composed_gauge_convex (hγc j) _)
      (fun j => RadialPower.composed_gauge_homogeneous (hγh j) _) (fun j x => hγ0 j _) p hp xstar
      isOpen_univ hψ' hK (subset_univ K) hrep'
  refine ⟨hIR, (equiv hF xstar hmin b hb K hK_def hK).1.mpr hIR, fun run hrun => ?_⟩
  have hKi : IsCompact run.initialSublevel := by
    refine hK.of_isClosed_subset (isClosed_le (convex_continuous hF) continuous_const) ?_
    intro x hx
    rw [hK_def]
    exact le_trans hx hrun
  exact run.mixed_linear_powers_convergence γ hγc hγh hγ0 (fun j => Matrix.mulVecLin (A j)) p hp
    xstar hmin isOpen_univ hψ' hKi (subset_univ _) hrep'

/-- A continuous function that is bounded above on a line is not coercive. -/
theorem not_coercive_of_line {n : ℕ} {f : Vec n → ℝ} (hc : Continuous f) (v : Vec n) (hv : v ≠ 0)
    (C : ℝ) (h0 : ∀ t : ℝ, f (t • v) ≤ C) : ¬ Tendsto f (cocompact (Vec n)) atTop := by
  intro ht
  obtain ⟨M, hM⟩ := (Article.Global.sublevels_compact_of_coercive hc ht C).isBounded.exists_norm_le
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have h := hM (((|M| + 1) / ‖v‖) • v) (h0 _)
  rw [norm_smul, Real.norm_of_nonneg (by positivity), div_mul_cancel₀ _ hvpos.ne'] at h
  linarith [le_abs_self M]

/-- Item `C/04_R/prose/068` (`companion/chapters/04_R.tex:342`): "The individual terms need not
be coercive." An instance of all hypotheses of display `disp/043` ($F(u,v)=u^2+|v|$, $x_*=0$,
$\psi(z)=z_0^2$, one gauge $\gamma=|\cdot|$ on $\R^1$, $A=(0\ 1)$, $p=1$; all sublevels compact)
in which neither $\psi$ nor the term $\gamma(Az)^p=|z_1|$ is coercive. -/
theorem terms_need_not_be_coercive :
    ∃ (F ψ : Vec 2 → ℝ) (γ : Fin 1 → Vec 1 → ℝ) (A : Fin 1 → Matrix (Fin 1) (Fin 2) ℝ)
      (p : Fin 1 → ℝ),
      ConvexOn ℝ univ F ∧ (∀ x, F 0 ≤ F x) ∧ (∀ b : ℝ, IsCompact {x | F x ≤ b}) ∧
      ConvexOn ℝ univ ψ ∧ CenteredSmoothSublinear.LocallyC11On univ ψ ∧
      (∀ j, Sublinear (γ j)) ∧ (∀ j x, 0 ≤ γ j x) ∧ (∀ j, 1 ≤ p j) ∧
      (∀ z, F (0 + z) = ψ z + ∑ j, γ j (A j *ᵥ z) ^ p j) ∧
      ¬ Tendsto ψ (cocompact (Vec 2)) atTop ∧
      ¬ Tendsto (fun z => γ 0 (A 0 *ᵥ z) ^ p 0) (cocompact (Vec 2)) atTop := by
  obtain ⟨hconv, hmin, -, hK, hψ, hψ11, -, -, -⟩ :=
    Article.Global.mixed_hypotheses UnexcitedMetric.objective (fun _ => rfl)
  have hA : ∀ z : Vec 2, (!![0, 1] : Matrix (Fin 1) (Fin 2) ℝ) *ᵥ z = fun _ => z 1 := by
    intro z; ext i; fin_cases i; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  refine ⟨UnexcitedMetric.objective, fun z => z 0 ^ 2, fun _ v => |v 0|, fun _ => !![0, 1],
    fun _ => 1, hconv, hmin, hK, hψ, hψ11, fun _ => (sublinear_iff _).mpr
      ⟨Article.Global.abs_coord_convex, fun t ht x => by
        simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg ht]⟩,
    fun _ _ => abs_nonneg _, fun _ => le_rfl, fun z => ?_, ?_, ?_⟩
  · simp only [zero_add, hA, Real.rpow_one, Finset.univ_unique, Finset.sum_singleton]
    rfl
  · refine not_coercive_of_line (by fun_prop) ![0, 1] (fun h => by simpa using congrFun h 1) 0
      (fun t => by simp)
  · refine not_coercive_of_line (by
      simp only [hA, Real.rpow_one]; fun_prop) ![1, 0] (fun h => by simpa using congrFun h 0) 0
      (fun t => by simp [hA])


/-! ### Section 4.6.2: polyhedral losses and penalties at nonzero solutions (line 349)

"Smooth" losses are read as convex and locally $C^{1,1}$ on $\R^n$
(`CenteredSmoothSublinear.LocallyC11On univ ψ`: differentiable with locally Lipschitz derivative),
the form the library and the article take; it includes $C^{1,1}$, $C^2$
(`locallyC11_of_contDiff_two`) and $C^\infty$ losses. "Covered locally under uniqueness": with a
unique minimizer $x_*$ (anywhere, not necessarily $0$), some $\delta>0$ chosen before the run gives
convergence of every admissible run with $F(x_0)\le F_*+\delta$. -/

theorem dot_add_right' {n : ℕ} (a x z : Vec n) : dot a (x + z) = dot a x + dot a z := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- Item `C/04_R/prose/069` (`companion/chapters/04_R.tex:349`): "Locally around any optimizer,
a nonzero scalar affine residual has fixed sign and is smooth; a zero residual becomes a centered
absolute value or hinge." For $r(x)=a^Tx-\beta$ and any point $x_*$: if $r(x_*)\ne0$, then on an
open neighborhood of $x_*$ the sign of $r$ is that of $r(x_*)$ and $|r|$ and $\max\{0,r\}$ equal
the affine functions $\sigma r$ and $\max\{0,\sigma\}r$, $\sigma=\operatorname{sign}r(x_*)$; if
$r(x_*)=0$, then $|r(x_*+z)|=|a^Tz|$ and $\max\{0,r(x_*+z)\}=\max\{0,a^Tz\}$. -/
theorem affine_residual_local {n : ℕ} (a : Vec n) (β : ℝ) (xstar : Vec n) :
    (dot a xstar - β ≠ 0 → ∃ U : Set (Vec n), IsOpen U ∧ xstar ∈ U ∧ ∀ x ∈ U,
      0 < (dot a x - β) * (dot a xstar - β) ∧
      |dot a x - β| = Real.sign (dot a xstar - β) * (dot a x - β) ∧
      max 0 (dot a x - β) = max 0 (Real.sign (dot a xstar - β)) * (dot a x - β)) ∧
    (dot a xstar - β = 0 → ∀ z, |dot a (xstar + z) - β| = |dot a z| ∧
      max 0 (dot a (xstar + z) - β) = max 0 (dot a z)) := by
  refine ⟨fun hne => ?_, fun h0 z => ?_⟩
  · have hc : Continuous (fun x : Vec n => (dot a x - β) * (dot a xstar - β)) := by
      unfold dot; fun_prop
    refine ⟨{x | 0 < (dot a x - β) * (dot a xstar - β)}, isOpen_lt continuous_const hc,
      mul_self_pos.mpr hne, fun x hx => ⟨hx, ?_, ?_⟩⟩ <;>
    · have hx' : 0 < (dot a x - β) * (dot a xstar - β) := hx
      rcases lt_or_gt_of_ne hne with hneg | hpos
      · have hxneg : dot a x - β < 0 := by nlinarith
        rw [Real.sign_of_neg hneg]
        simp [abs_of_neg hxneg, max_eq_left hxneg.le]
      · have hxpos : 0 < dot a x - β := by nlinarith
        rw [Real.sign_of_pos hpos]
        simp [abs_of_pos hxpos, max_eq_right hxpos.le]
  · rw [dot_add_right', show dot a xstar + dot a z - β = dot a z by linarith]
    exact ⟨rfl, rfl⟩

/-- Item `C/04_R/prose/070` (`companion/chapters/04_R.tex:349`): "Hence smooth losses plus
$\ell_1$, fused/generalized $\ell_1$, finite hinge and quantile losses are covered locally under
uniqueness." The $\ell_1$ case $F=\psi+\sum_i|a_i^Tx-b_i|$ (the other cases:
`generalized_l1_covered`, `fused_l1_covered`, `hinge_covered`, `quantile_covered`). -/
theorem l1_covered {n : ℕ} {ι : Type*} [Fintype ι] (ψ : Vec n → ℝ) (hψ : ConvexOn ℝ univ ψ)
    (hψ11 : CenteredSmoothSublinear.LocallyC11On univ ψ) (a : ι → Vec n) (b : ι → ℝ)
    (F : Vec n → ℝ) (hFdef : ∀ x, F x = ψ x + ∑ i, |dot (a i) x - b i|) (xstar : Vec n)
    (hmin : ∀ x, F xstar ≤ F x) (huniq : ∀ x, F x = F xstar → x = xstar) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ run : AdmissibleBFGSRun n F, F (run.x 0) ≤ F xstar + δ →
      Tendsto (fun k => F (run.x k)) atTop (𝓝 (F xstar)) ∧ Tendsto run.x atTop (𝓝 xstar) := by
  have hF : ConvexOn ℝ univ F :=
    (hψ.add (abs_affine_sum_convex a b)).congr (fun x _ => (hFdef x).symm)
  obtain ⟨δ, hδ, h⟩ := AffineKinks.local_absolute_basin hF a b isOpen_univ
    hψ11 (mem_univ xstar)
    (fun x _ => hFdef x) hmin huniq
  exact ⟨δ, hδ, fun run hrun => ⟨(h run hrun).2.1, (h run hrun).2.2⟩⟩

/-- Item `C/04_R/prose/070` (`companion/chapters/04_R.tex:349`), generalized $\ell_1$:
$F=\psi+\|Dx-c\|_1$ for a matrix $D$. -/
theorem generalized_l1_covered {n m : ℕ} (ψ : Vec n → ℝ) (hψ : ConvexOn ℝ univ ψ)
    (hψ11 : CenteredSmoothSublinear.LocallyC11On univ ψ) (D : Matrix (Fin m) (Fin n) ℝ)
    (c : Vec m)
    (F : Vec n → ℝ) (hFdef : ∀ x, F x = ψ x + ∑ i, |(D *ᵥ x - c) i|) (xstar : Vec n)
    (hmin : ∀ x, F xstar ≤ F x) (huniq : ∀ x, F x = F xstar → x = xstar) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ run : AdmissibleBFGSRun n F, F (run.x 0) ≤ F xstar + δ →
      Tendsto (fun k => F (run.x k)) atTop (𝓝 (F xstar)) ∧ Tendsto run.x atTop (𝓝 xstar) := by
  have hrow : ∀ x, ∑ i, |(D *ᵥ x - c) i| = ∑ i, |dot (D i) x - c i| := fun x => by
    simp [Matrix.mulVec, dot, dotProduct]
  have hF : ConvexOn ℝ univ F := (hψ.add (abs_affine_sum_convex (fun i => D i) c)).congr
    (fun x _ => by rw [hFdef, hrow]; rfl)
  obtain ⟨δ, hδ, h⟩ := AffineKinks.local_matrix_l1_basin hF D c isOpen_univ
    hψ11 (mem_univ xstar)
    (fun x _ => hFdef x) hmin huniq
  exact ⟨δ, hδ, fun run hrun => ⟨(h run hrun).2.1, (h run hrun).2.2⟩⟩

/-- Item `C/04_R/prose/070` (`companion/chapters/04_R.tex:349`), fused $\ell_1$:
$F(x)=\psi(x)+w\sum_{i<k}|x_{i+1}-x_i|$ on $\R^{k+1}$, $w\ge0$ (first differences). -/
theorem fused_l1_covered {k : ℕ} (ψ : Vec (k + 1) → ℝ) (hψ : ConvexOn ℝ univ ψ)
    (hψ11 : CenteredSmoothSublinear.LocallyC11On univ ψ) (w : ℝ) (hw : 0 ≤ w)
    (F : Vec (k + 1) → ℝ)
    (hFdef : ∀ x, F x = ψ x + w * ∑ i : Fin k, |x i.succ - x i.castSucc|) (xstar : Vec (k + 1))
    (hmin : ∀ x, F xstar ≤ F x) (huniq : ∀ x, F x = F xstar → x = xstar) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ run : AdmissibleBFGSRun (k + 1) F, F (run.x 0) ≤ F xstar + δ →
      Tendsto (fun k => F (run.x k)) atTop (𝓝 (F xstar)) ∧ Tendsto run.x atTop (𝓝 xstar) := by
  have hFe : F = FirstDifference.objective k w ψ := funext fun x => hFdef x
  subst hFe
  have hrow : ∀ x, FirstDifference.penalty k w x =
      ∑ i, |dot ((w • FirstDifference.differenceMatrix k) i) x - (0 : Vec k) i| := fun x => by
    rw [FirstDifference.penalty_matrix k w hw]
    simp [Matrix.mulVec, dot, dotProduct]
  have hF : ConvexOn ℝ univ (FirstDifference.objective k w ψ) :=
    (hψ.add (abs_affine_sum_convex (fun i => (w • FirstDifference.differenceMatrix k) i) 0)).congr
      (fun x _ => by simp only [FirstDifference.objective, hrow]; rfl)
  obtain ⟨δ, hδ, h⟩ := FirstDifference.local_fullBFGS hw hF isOpen_univ
    hψ11 (mem_univ xstar)
    hmin huniq
  exact ⟨δ, hδ, fun run hrun => ⟨(h run hrun).2.1, (h run hrun).2.2⟩⟩

/-- Item `C/04_R/prose/070` (`companion/chapters/04_R.tex:349`), finite hinge losses:
$F=\psi+\sum_i\max\{0,a_i^Tx-b_i\}$. -/
theorem hinge_covered {n : ℕ} {ι : Type*} [Fintype ι] (ψ : Vec n → ℝ) (hψ : ConvexOn ℝ univ ψ)
    (hψ11 : CenteredSmoothSublinear.LocallyC11On univ ψ) (a : ι → Vec n) (b : ι → ℝ)
    (F : Vec n → ℝ) (hFdef : ∀ x, F x = ψ x + ∑ i, max 0 (dot (a i) x - b i)) (xstar : Vec n)
    (hmin : ∀ x, F xstar ≤ F x) (huniq : ∀ x, F x = F xstar → x = xstar) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ run : AdmissibleBFGSRun n F, F (run.x 0) ≤ F xstar + δ →
      Tendsto (fun k => F (run.x k)) atTop (𝓝 (F xstar)) ∧ Tendsto run.x atTop (𝓝 xstar) := by
  have hs : ConvexOn ℝ univ (fun x => ∑ i, max 0 (dot (a i) x - b i)) := by
    have h := Article.Local.convexOn_finset_sum Finset.univ
      (fun i x => (AffineKinks.Kink.hinge (a i) (b i)).value x)
      (fun i _ => (AffineKinks.Kink.hinge (a i) (b i)).value_convex)
    simpa only [AffineKinks.Kink.hinge_value] using h
  have hF : ConvexOn ℝ univ F := (hψ.add hs).congr (fun x _ => (hFdef x).symm)
  obtain ⟨δ, hδ, h⟩ := AffineKinks.local_hinge_basin hF a b isOpen_univ
    hψ11 (mem_univ xstar)
    (fun x _ => hFdef x) hmin huniq
  exact ⟨δ, hδ, fun run hrun => ⟨(h run hrun).2.1, (h run hrun).2.2⟩⟩

/-- Item `C/04_R/prose/070` (`companion/chapters/04_R.tex:349`), finite quantile losses:
$F=\psi+\sum_i\rho_{\tau_i}(a_i^Tx-b_i)$ with
$\rho_\tau(r)=\tau\max\{r,0\}+(1-\tau)\max\{-r,0\}$, $0<\tau_i<1$. -/
theorem quantile_covered {n : ℕ} {ι : Type*} [Fintype ι] (ψ : Vec n → ℝ) (hψ : ConvexOn ℝ univ ψ)
    (hψ11 : CenteredSmoothSublinear.LocallyC11On univ ψ) (a : ι → Vec n)
    (b τ : ι → ℝ) (_hτ : ∀ i, 0 < τ i ∧ τ i < 1) (F : Vec n → ℝ)
    (hFdef : ∀ x, F x = ψ x + ∑ i, (τ i * max (dot (a i) x - b i) 0 +
      (1 - τ i) * max (-(dot (a i) x - b i)) 0)) (xstar : Vec n)
    (hmin : ∀ x, F xstar ≤ F x) (huniq : ∀ x, F x = F xstar → x = xstar) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ run : AdmissibleBFGSRun n F, F (run.x 0) ≤ F xstar + δ →
      Tendsto (fun k => F (run.x k)) atTop (𝓝 (F xstar)) ∧ Tendsto run.x atTop (𝓝 xstar) := by
  have hs : ConvexOn ℝ univ (fun x => ∑ i, (τ i * max (dot (a i) x - b i) 0 +
      (1 - τ i) * max (-(dot (a i) x - b i)) 0)) := by
    have h := Article.Local.convexOn_finset_sum Finset.univ
      (fun i x => (AffineKinks.Kink.quantile (a i) (b i) (τ i)).value x)
      (fun i _ => (AffineKinks.Kink.quantile (a i) (b i) (τ i)).value_convex)
    simpa only [AffineKinks.Kink.quantile_value] using h
  have hF : ConvexOn ℝ univ F := (hψ.add hs).congr (fun x _ => (hFdef x).symm)
  obtain ⟨δ, hδ, h⟩ := AffineKinks.local_quantile_basin hF a b τ isOpen_univ
    hψ11 (mem_univ xstar)
    (fun x _ => by rw [hFdef]; rfl) hmin huniq
  exact ⟨δ, hδ, fun run hrun => ⟨(h run hrun).2.1, (h run hrun).2.2⟩⟩


/-! ### Section 4.6.3: affine Euclidean group residuals (line 356) -/

/-- Item `C/04_R/prose/074` (`companion/chapters/04_R.tex:356`): "For terms $\|A_jx-b_j\|_2$,
a nonzero optimal residual is locally smooth, while a zero optimal residual becomes $\|A_jz\|_2$,
which is homogeneous." For a matrix $A$, a vector $\beta$ and the optimal point $x_*$: if
$Ax_*\ne\beta$ the term is $C^2$ on a ball around $x_*$; if $Ax_*=\beta$ it equals
$\|A(x-x_*)\|_2$, and $z\mapsto\|Az\|_2$ is finite sublinear (convex and positively
homogeneous). -/
theorem euclidean_residual_local {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (β : Vec m)
    (xstar : Vec n) :
    (A *ᵥ xstar - β ≠ 0 → ∃ ε : ℝ, 0 < ε ∧
      ContDiffOn ℝ 2 (fun x => ‖euclideanVector (A *ᵥ x - β)‖) (Metric.ball xstar ε)) ∧
    (A *ᵥ xstar - β = 0 → ∀ z,
        ‖euclideanVector (A *ᵥ (xstar + z) - β)‖ = ‖euclideanVector (A *ᵥ z)‖) ∧
    Sublinear (fun z => ‖euclideanVector (A *ᵥ z)‖) := by
  have hres : ∀ x, euclideanVector (A *ᵥ x - β) =
      EuclideanResidual.residual (EuclideanResidual.matrixEuclideanCLM A) (euclideanVector β) x :=
    fun x => (EuclideanResidual.matrix_residual A β x).symm
  refine ⟨fun hne => ?_, fun h0 z => ?_, ?_⟩
  · have hcont : Continuous (EuclideanResidual.residual (EuclideanResidual.matrixEuclideanCLM A)
        (euclideanVector β)) := (EuclideanResidual.residual_contDiff _ _ (N := 0)).continuous
    set O := {x : Vec n | EuclideanResidual.residual (EuclideanResidual.matrixEuclideanCLM A)
      (euclideanVector β) x ≠ 0} with hO
    have hOo : IsOpen O := isOpen_compl_singleton.preimage hcont
    have hxO : xstar ∈ O := by
      show _ ≠ 0
      rw [← hres]
      intro h
      apply hne
      simpa [euclideanVector] using congrArg (WithLp.equiv 2 (Vec m)) h
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hOo xstar hxO
    refine ⟨ε, hε, fun x hx => ?_⟩
    have hxO' : x ∈ O := hball hx
    have h1 : ContDiffAt ℝ 2 (fun x => ‖EuclideanResidual.residual
        (EuclideanResidual.matrixEuclideanCLM A) (euclideanVector β) x‖) x :=
      (contDiffAt_norm ℝ hxO').comp x (EuclideanResidual.residual_contDiff _ _).contDiffAt
    simp only [hres]
    exact h1.contDiffWithinAt
  · have hA : A *ᵥ (xstar + z) - β = A *ᵥ z := by
      rw [Matrix.mulVec_add, show A *ᵥ xstar = β from sub_eq_zero.mp h0]; abel
    rw [hA]
  · refine (sublinear_iff _).mpr ⟨?_, fun t ht z => ?_⟩
    · have h := Article.Local.norm_affine_convex A 0
      simpa only [sub_zero] using h
    · show ‖euclideanVector (A *ᵥ (t • z))‖ = t * ‖euclideanVector (A *ᵥ z)‖
      rw [Matrix.mulVec_smul, Article.Global.norm_euclideanVector_smul, abs_of_nonneg ht]

/-- Item `C/04_R/prose/075` (`companion/chapters/04_R.tex:356`): "Thus sums of such terms,
including overlapping Euclidean group penalties and sums of distances, added to a suitable convex
smooth objective, satisfy the local condition when the minimizer is unique." For
$F=\ell+\sum_j\|A_jx-b_j\|_2$ with $\ell$ convex and locally $C^{1,1}$ (`LocallyC11On univ`; $C^2$
is included by `locallyC11_of_contDiff_two`) and arbitrary matrices $A_j$ (coordinate
selections for overlapping groups, $A_j=I$ for distances $\|x-b_j\|$), with unique minimizer
$x_*$: (IR) and (RS) hold on a compact positive sublevel $\{F\le b\}$, $b>F_*$, and the local
convergence conclusion holds (the article's `euclidean_residuals_basin`). -/
theorem euclidean_residuals_local_condition {n : ℕ} {J : Type*} [Fintype J] {m : J → ℕ}
    (loss : Vec n → ℝ) (hloss : ConvexOn ℝ univ loss)
    (hloss11 : CenteredSmoothSublinear.LocallyC11On univ loss)
    (A : ∀ j, Matrix (Fin (m j)) (Fin n) ℝ) (b : ∀ j, Vec (m j)) (F : Vec n → ℝ)
    (hFdef : ∀ x, F x = loss x + ∑ j, ‖euclideanVector (A j *ᵥ x - b j)‖) (xstar : Vec n)
    (hmin : ∀ x, F xstar ≤ F x) (huniq : ∀ x, F x = F xstar → x = xstar) :
    (∃ b' : ℝ, F xstar < b' ∧ IsCompact {x | F x ≤ b'} ∧ IR F xstar {x | F x ≤ b'} ∧
      RS F xstar {x | F x ≤ b'}) ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ run : AdmissibleBFGSRun n F, F (run.x 0) ≤ F xstar + ε →
      Tendsto (fun k => F (run.x k)) atTop (𝓝 (F xstar)) ∧ Tendsto run.x atTop (𝓝 xstar) := by
  classical
  have hloss_s := hloss11
  have hF : ConvexOn ℝ univ F :=
    (hloss.add (Article.Local.convexOn_finset_sum _ _ fun j _ =>
      Article.Local.norm_affine_convex (A j) (b j))).congr (fun x _ => (hFdef x).symm)
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Vec n → ℝ, ψ = fun x => loss x + ∑ j ∈ Finset.univ.filter
      (fun j => A j *ᵥ xstar - b j ≠ 0), ‖euclideanVector (A j *ᵥ x - b j)‖ := ⟨_, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : Vec n → ℝ, γ = fun r => ∑ j ∈ Finset.univ.filter
      (fun j => A j *ᵥ xstar - b j = 0), ‖euclideanVector (A j *ᵥ r)‖ := ⟨_, rfl⟩
  obtain ⟨hdec, -, hγc, hγh, U, hU, -, hxU, hψs⟩ :=
    Article.Local.euclidean_residuals_local_form loss hloss hloss_s A b F hFdef xstar ψ γ
      (fun x => by rw [hψ]) (fun r => by rw [hγ])
  have hγ0 : ∀ r, 0 ≤ γ r := fun r => by
    rw [hγ]; exact Finset.sum_nonneg (fun j _ => norm_nonneg _)
  obtain ⟨δ, hδ, hsub⟩ := Localization.neighborhood_basin hF xstar hmin huniq (hU.mem_nhds hxU)
  have hK : IsCompact {x | F x ≤ F xstar + δ} :=
    Localization.sublevel_compact hF xstar hmin huniq _
  have hIR : IR F xstar {x | F x ≤ F xstar + δ} := by
    rw [IR_iff_library]
    refine RadialPower.mixed_powers_inward hF (Γ := fun _ : Unit => γ) (fun _ => hγc)
      (fun _ => hγh) (fun _ x => hγ0 x) (fun _ => 1) (fun _ => le_rfl) xstar hU hψs hK hsub ?_
    intro x _
    simp only [RadialPower.sumObjective, RadialPower.powered, Real.rpow_one, Finset.univ_unique,
      Finset.sum_singleton]
    exact hdec x
  refine ⟨⟨F xstar + δ, by linarith, hK, hIR,
    (equiv hF xstar hmin _ (by linarith) _ rfl hK).1.mpr hIR⟩, ?_⟩
  obtain ⟨U', -, -, ε, hε, h⟩ := Article.Local.euclidean_residuals_basin loss hloss hloss_s A b F
    hFdef xstar hmin huniq
  exact ⟨ε, hε, fun run hrun => ⟨(h run hrun).2.1, (h run hrun).2.2⟩⟩

/-- Item `C/04_R/prose/076` (`companion/chapters/04_R.tex:356`): "This does not imply that every
spectral penalty is smooth near every nonzero residual." The nuclear norm on symmetric
$2\times2$ matrices (orthonormal coordinates, `NuclearSymmetric2.nuclearCoords`) is not
differentiable at the nonzero matrix $\operatorname{diag}(1,0)$: along
$\operatorname{diag}(1+s,-s)$ it equals $\max\{1,|1+2s|\}$. -/
theorem nuclear_not_smooth :
    NuclearSymmetric2.matrix NuclearSymmetric2.minimizer = !![1, 0; 0, 0] ∧
      NuclearSymmetric2.minimizer ≠ 0 ∧
      ¬ DifferentiableAt ℝ NuclearSymmetric2.nuclearCoords NuclearSymmetric2.minimizer := by
  refine ⟨NuclearSymmetric2.matrix_minimizer, fun h => by
    simpa [NuclearSymmetric2.minimizer] using congrFun h 0, fun hd => ?_⟩
  set v : Vec 3 := ![1, 0, -1] with hv
  have hline : ∀ s : ℝ, -1 / 2 < s →
      NuclearSymmetric2.nuclearCoords (NuclearSymmetric2.minimizer + s • v) = 1 + 2 * max s 0 := by
    intro s hs
    rw [NuclearSymmetric2.nuclearCoords_eq]
    have h1 :
        (NuclearSymmetric2.minimizer + s • v) 0 + (NuclearSymmetric2.minimizer + s • v) 2 = 1 := by
      simp [NuclearSymmetric2.minimizer, hv]
    have h2 : NuclearSymmetric2.discr (NuclearSymmetric2.minimizer + s • v) = (1 + 2 * s) ^ 2 := by
      simp [NuclearSymmetric2.discr, NuclearSymmetric2.minimizer, hv]; ring
    rw [h1, h2, Real.sqrt_sq (by linarith), abs_one]
    rcases le_total s 0 with h | h
    · rw [max_eq_left (by linarith), max_eq_right h]; ring
    · rw [max_eq_right (by linarith), max_eq_left h]
  have hl : DifferentiableAt ℝ (fun s : ℝ => NuclearSymmetric2.minimizer + s • v) 0 :=
    (differentiableAt_const _).add (differentiableAt_id.smul_const _)
  have hd' : DifferentiableAt ℝ NuclearSymmetric2.nuclearCoords
      (NuclearSymmetric2.minimizer + (0 : ℝ) • v) := by simpa using hd
  have hc := hd'.comp (0 : ℝ) hl
  have hev : (fun s : ℝ => 1 + 2 * max s 0) =ᶠ[𝓝 0]
      (NuclearSymmetric2.nuclearCoords ∘ fun s : ℝ => NuclearSymmetric2.minimizer + s • v) := by
    filter_upwards [eventually_gt_nhds (by norm_num : (-1 / 2 : ℝ) < 0)] with s hs
    exact (hline s hs).symm
  have hmaxd : DifferentiableAt ℝ (fun s : ℝ => 1 + 2 * max s 0) 0 := hc.congr_of_eventuallyEq hev
  have habs : DifferentiableAt ℝ (fun s : ℝ => |s|) 0 := by
    have h2 := (hmaxd.sub_const 1).sub differentiableAt_id
    convert h2 using 1
    funext s
    simp only [id]
    rcases le_total s 0 with h | h
    · rw [max_eq_right h, abs_of_nonpos h]; ring
    · rw [max_eq_left h, abs_of_nonneg h]; ring
  exact not_differentiableAt_abs_zero habs


/-! ### Section 4.6.4: finite maxima (lines 362-370)

Locally $F=\max_if_i$: on an open neighborhood $U$ of $x_*$, $F(w)$ is the maximum (`sup'`) of the
values $f_i(w)$ of finitely many branches that are $C^2$ on $U$. The active set at $w$ is
$I(w)=\{i: f_i(w)=F(w)\}$; $\nabla f_i(w)$ is `coordinateGradient (f i) w`. -/

theorem branch_fderiv_eq_dot {n : ℕ} {U : Set (Vec n)} (hU : IsOpen U) {f : Vec n → ℝ}
    (hf : ContDiffOn ℝ 2 f U) {w : Vec n} (hw : w ∈ U) (v : Vec n) :
    fderiv ℝ f w v = dot (coordinateGradient f w) v := by
  have hd : DifferentiableAt ℝ f w := (hf.differentiableOn (by norm_num) w hw).differentiableAt
    (hU.mem_nhds hw)
  rw [(hasFDerivAt_coordinateGradient hd).fderiv, gradientFunctional_apply]

theorem compat_library {n : ℕ} {ι : Type*} [Fintype ι] (hne : (Finset.univ : Finset ι).Nonempty)
    {F : Vec n → ℝ} (xstar : Vec n) (U : Set (Vec n)) (hU : IsOpen U)
    (f : ι → Vec n → ℝ) (hf : ∀ i, ContDiffOn ℝ 2 (f i) U)
    (_hrep : ∀ w ∈ U, F w = Finset.univ.sup' hne fun i => f i w)
    (hcompat : ∀ w ∈ U, ∀ i j, f i w = F w → f j w = F w →
      dot (coordinateGradient (f i) w - coordinateGradient (f j) w) (w - xstar) = 0) :
    ∀ w ∈ U, ∀ i j, f i w = F w → f j w = F w →
      (fderiv ℝ (f i) w) (w - xstar) = (fderiv ℝ (f j) w) (w - xstar) := by
  intro w hw i j hi hj
  have h := hcompat w hw i j hi hj
  rw [dot_sub_left] at h
  rw [branch_fderiv_eq_dot hU (hf i) hw, branch_fderiv_eq_dot hU (hf j) hw]
  linarith

/-- Item `C/04_R/disp/044` (`companion/chapters/04_R.tex:364-367`): "If locally $F=\max_if_i$ with
finitely many convex $C^2$ branches, it suffices that
\[ (\nabla f_i(w)-\nabla f_j(w))^T(w-x_*)=0\quad(i,j\in I(w)) \]
at every active tie near $x_*$." For finite convex $F$ with unique minimizer $x_*$: the condition
gives (IR) on every subset of a ball around $x_*$ ("This proves (IR) directly", line 368), (RS) on
its compact subsets, and the local convergence of every sufficiently low-starting admissible run
(the library's `local_finite_max_inward`, `local_finite_max_radial`, `local_finite_max_basin`;
convexity of the branches is not needed). -/
theorem finite_max_branch_test {n : ℕ} {ι : Type*} [Fintype ι]
    (hne : (Finset.univ : Finset ι).Nonempty)
    {F : Vec n → ℝ} (xstar : Vec n) (U : Set (Vec n)) (hU : IsOpen U)
    (f : ι → Vec n → ℝ) (hf : ∀ i, ContDiffOn ℝ 2 (f i) U)
    (hrep : ∀ w ∈ U, F w = Finset.univ.sup' hne fun i => f i w)
    (hF : ConvexOn ℝ univ F) (hmin : ∀ x, F xstar ≤ F x) (huniq : ∀ x, F x = F xstar → x = xstar)
    (hxU : xstar ∈ U) (_hfc : ∀ i, ConvexOn ℝ U (f i))
    (hcompat : ∀ w ∈ U, ∀ i j, f i w = F w → f j w = F w →
      dot (coordinateGradient (f i) w - coordinateGradient (f j) w) (w - xstar) = 0) :
    (∃ r : ℝ, 0 < r ∧ ∀ K ⊆ Metric.ball xstar r, IR F xstar K) ∧
      (∃ r : ℝ, 0 < r ∧ ∀ K : Set (Vec n), IsCompact K → K ⊆ Metric.ball xstar r →
        RS F xstar K) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ run : AdmissibleBFGSRun n F, F (run.x 0) ≤ F xstar + δ →
        (∀ k, run.x k ∈ U) ∧ Tendsto (fun k => F (run.x k)) atTop (𝓝 (F xstar)) ∧
          Tendsto run.x atTop (𝓝 xstar) := by
  have hc := compat_library hne xstar U hU f hf hrep hcompat
  obtain ⟨r1, hr1, h1⟩ := FiniteMaxRadial.local_finite_max_inward hne hF f hU hf hxU hrep hc
  obtain ⟨r2, hr2, h2⟩ := FiniteMaxRadial.local_finite_max_radial hne hF f hU hf hxU hrep hc
  refine ⟨⟨r1, hr1, fun K hK => (IR_iff_library F xstar K).mpr (h1 K hK)⟩,
    ⟨r2, hr2, fun K hK hKB => (RS_iff_library F xstar K).mpr (h2 K hK hKB)⟩, ?_⟩
  exact FiniteMaxRadial.local_finite_max_basin hne hF f hU hf hxU hrep hc hmin huniq

/-- Item `C/04_R/prose/077` (`companion/chapters/04_R.tex:368`): "Along a fixed ray, active
branches then agree in the scalar first derivative." Under the condition of display `disp/044`:
on the ray $t\mapsto x-t(x-x_*)$, at every parameter $u\ne1$ whose point $w$ lies in $U$, all
active branches have the same scalar derivative $\nabla f_i(w)^T(-(x-x_*))$, and it is the
derivative of $t\mapsto F(x-t(x-x_*))$ at $u$. -/
theorem ray_active_agreement {n : ℕ} {ι : Type*} [Fintype ι]
    (hne : (Finset.univ : Finset ι).Nonempty)
    {F : Vec n → ℝ} (xstar : Vec n) (U : Set (Vec n)) (hU : IsOpen U)
    (f : ι → Vec n → ℝ) (hf : ∀ i, ContDiffOn ℝ 2 (f i) U)
    (hrep : ∀ w ∈ U, F w = Finset.univ.sup' hne fun i => f i w)
    (hcompat : ∀ w ∈ U, ∀ i j, f i w = F w → f j w = F w →
      dot (coordinateGradient (f i) w - coordinateGradient (f j) w) (w - xstar) = 0)
    (x : Vec n) (u : ℝ) (hu : u ≠ 1) (huU : x - u • (x - xstar) ∈ U) :
    (∀ i j, f i (x - u • (x - xstar)) = F (x - u • (x - xstar)) →
      f j (x - u • (x - xstar)) = F (x - u • (x - xstar)) →
      fderiv ℝ (f i) (x - u • (x - xstar)) (-(x - xstar)) =
        fderiv ℝ (f j) (x - u • (x - xstar)) (-(x - xstar))) ∧
    ∀ i, f i (x - u • (x - xstar)) = F (x - u • (x - xstar)) →
      HasDerivAt (fun t => F (x - t • (x - xstar)))
        (fderiv ℝ (f i) (x - u • (x - xstar)) (-(x - xstar))) u := by
  have hc := compat_library hne xstar U hU f hf hrep hcompat
  set w := x - u • (x - xstar) with hw
  have hagree : ∀ i j, f i w = F w → f j w = F w →
      fderiv ℝ (f i) w (-(x - xstar)) = fderiv ℝ (f j) w (-(x - xstar)) := by
    intro i j hi hj
    have he := hc w huU i j hi hj
    have hr : w - xstar = (1 - u) • (x - xstar) := by rw [hw]; module
    rw [hr, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at he
    have hne' : 1 - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
    rw [map_neg, map_neg, mul_left_cancel₀ hne' he]
  refine ⟨hagree, fun i hi => ?_⟩
  have hcurve := FiniteMaxRadial.inward_curve_hasDerivAt xstar x u
  have hdiff : ∀ j, DifferentiableAt ℝ (f j) w := fun j =>
    ((hf j).differentiableOn (by norm_num) w huU).differentiableAt (hU.mem_nhds huU)
  have hd : ∀ j ∈ (Finset.univ : Finset ι), HasDerivAt (fun t => f j (x - t • (x - xstar)))
      (fderiv ℝ (f j) w (-(x - xstar))) u := fun j _ =>
    (hdiff j).hasFDerivAt.comp_hasDerivAt u hcurve
  have hQ : HasDerivAt (FiniteMaxRadial.maximum Finset.univ hne
      (fun j t => f j (x - t • (x - xstar)))) (fderiv ℝ (f i) w (-(x - xstar))) u := by
    apply FiniteMaxRadial.maximum_hasDerivAt_of_active_agreement hne hd
    intro j _ hj
    have hFw : F w = FiniteMaxRadial.maximum Finset.univ hne
        (fun j t => f j (x - t • (x - xstar))) u := hrep w huU
    exact hagree j i (hj.trans hFw.symm) hi
  apply hQ.congr_of_eventuallyEq
  have hcont : ContinuousAt (fun t : ℝ => x - t • (x - xstar)) u := hcurve.continuousAt
  filter_upwards [hcont.eventually (hU.mem_nhds huU)] with t ht
  exact hrep _ ht

/-- Item `C/04_R/prose/078` (`companion/chapters/04_R.tex:368`): "That derivative is a
continuous selection of finitely many Lipschitz branch derivatives, and has their common Lipschitz
bound on compact intervals." Under the condition of display `disp/044`: there are $M\ge0$ and a
ball $B_\rho(x_*)\subset U$ such that for every $x$ in $B_{\rho/4}(x_*)$, on the parameter interval
$I=(-1/2,3/4)\supset[0,1/2]$ of the ray $t\mapsto x-t(x-x_*)$, the branch derivatives
$d_i(t)=\nabla f_i(x-tr_x)^T(-r_x)$ have the common Lipschitz constant $M\|r_x\|^2$; the derivative
of the maximum $Q$ of the branch values along the ray is, at each $t\in I$, the derivative $d_i(t)$
of every active branch, continuous on $I$ and Lipschitz with the same constant; and it is the
derivative of $t\mapsto F(x-tr_x)$. -/
theorem ray_derivative_selection {n : ℕ} {ι : Type*} [Fintype ι]
    (hne : (Finset.univ : Finset ι).Nonempty)
    {F : Vec n → ℝ} (xstar : Vec n) (U : Set (Vec n)) (hU : IsOpen U)
    (f : ι → Vec n → ℝ) (hf : ∀ i, ContDiffOn ℝ 2 (f i) U)
    (hrep : ∀ w ∈ U, F w = Finset.univ.sup' hne fun i => f i w)
    (hcompat : ∀ w ∈ U, ∀ i j, f i w = F w → f j w = F w →
      dot (coordinateGradient (f i) w - coordinateGradient (f j) w) (w - xstar) = 0)
    (hxU : xstar ∈ U) :
    ∃ M : NNReal, ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball xstar ρ ⊆ U ∧
      ∀ x ∈ Metric.ball xstar (ρ / 4),
        (∀ i, LipschitzOnWith (M * ‖x - xstar‖₊ * ‖x - xstar‖₊)
          (fun t : ℝ => fderiv ℝ (f i) (x - t • (x - xstar)) (-(x - xstar)))
          (Ioo (-1 / 2 : ℝ) (3 / 4))) ∧
        (∀ t ∈ Ioo (-1 / 2 : ℝ) (3 / 4), ∀ i, f i (x - t • (x - xstar)) = F (x - t • (x - xstar)) →
          deriv (FiniteMaxRadial.maximum Finset.univ hne (fun j t => f j (x - t • (x - xstar)))) t =
            fderiv ℝ (f i) (x - t • (x - xstar)) (-(x - xstar))) ∧
        ContinuousOn (deriv (FiniteMaxRadial.maximum Finset.univ hne
          (fun j t => f j (x - t • (x - xstar))))) (Ioo (-1 / 2 : ℝ) (3 / 4)) ∧
        LipschitzOnWith (M * ‖x - xstar‖₊ * ‖x - xstar‖₊)
          (deriv (FiniteMaxRadial.maximum Finset.univ hne (fun j t => f j (x - t • (x - xstar)))))
          (Ioo (-1 / 2 : ℝ) (3 / 4)) ∧
        ∀ t ∈ Ioo (-1 / 2 : ℝ) (3 / 4), HasDerivAt (fun t => F (x - t • (x - xstar)))
          (deriv (FiniteMaxRadial.maximum Finset.univ hne
              (fun j t => f j (x - t • (x - xstar)))) t) t := by
  have hc := compat_library hne xstar U hU f hf hrep hcompat
  obtain ⟨M, ρ, hρ, hBU, hM⟩ := FiniteMaxRadial.finite_branch_neighborhood hne f hU hxU hf
  refine ⟨M, ρ, hρ, hBU, fun x hx => ?_⟩
  set I := Ioo (-1 / 2 : ℝ) (3 / 4) with hI
  have hIB : ∀ t ∈ I, x - t • (x - xstar) ∈ Metric.ball xstar ρ := fun t ht =>
    FiniteMaxRadial.inward_curve_mem_ball hρ hx ht
  have hLip : ∀ i, LipschitzOnWith (M * ‖x - xstar‖₊ * ‖x - xstar‖₊)
      (fun t => fderiv ℝ (f i) (x - t • (x - xstar)) (-(x - xstar))) I := fun i =>
    FiniteMaxRadial.radial_branch_derivative_lipschitz (hM i) xstar x hIB
  have hne1 : ∀ t ∈ I, t ≠ 1 := fun t ht => by
    have := ht.2
    intro h
    rw [h] at this
    norm_num at this
  have hd : ∀ i ∈ (Finset.univ : Finset ι), ∀ t ∈ I, HasDerivAt (fun t => f i (x - t • (x - xstar)))
      (fderiv ℝ (f i) (x - t • (x - xstar)) (-(x - xstar))) t := fun i _ t ht =>
    (((hf i).differentiableOn (by norm_num) _ (hBU (hIB t ht))).differentiableAt
      (hU.mem_nhds (hBU (hIB t ht)))).hasFDerivAt.comp_hasDerivAt t
      (FiniteMaxRadial.inward_curve_hasDerivAt xstar x t)
  have ha : ∀ t ∈ I, ∀ i ∈ (Finset.univ : Finset ι), ∀ j ∈ (Finset.univ : Finset ι),
      f i (x - t • (x - xstar)) = FiniteMaxRadial.maximum Finset.univ hne
        (fun j t => f j (x - t • (x - xstar))) t →
      f j (x - t • (x - xstar)) = FiniteMaxRadial.maximum Finset.univ hne
        (fun j t => f j (x - t • (x - xstar))) t →
      fderiv ℝ (f i) (x - t • (x - xstar)) (-(x - xstar)) =
        fderiv ℝ (f j) (x - t • (x - xstar)) (-(x - xstar)) := by
    intro t ht i _ j _ hi hj
    have hFw := hrep _ (hBU (hIB t ht))
    exact (ray_active_agreement hne xstar U hU f hf hrep hcompat x t (hne1 t ht) (hBU (hIB t ht))).1
      i j (hi.trans hFw.symm) (hj.trans hFw.symm)
  have hcont := FiniteMaxRadial.maximum_deriv_continuousOn hne isOpen_Ioo hd ha
    (fun i _ => hLip i)
  have hLQ := FiniteMaxRadial.maximum_deriv_lipschitzOn hne isOpen_Ioo (convex_Ioo _ _) hd ha
    (fun i _ => hLip i)
  have hsel : ∀ t ∈ I, ∀ i, f i (x - t • (x - xstar)) = F (x - t • (x - xstar)) →
      HasDerivAt (FiniteMaxRadial.maximum Finset.univ hne (fun j t => f j (x - t • (x - xstar))))
        (fderiv ℝ (f i) (x - t • (x - xstar)) (-(x - xstar))) t := by
    intro t ht i hi
    have hFw := hrep _ (hBU (hIB t ht))
    exact FiniteMaxRadial.maximum_hasDerivAt_of_active_agreement hne (fun j hj => hd j hj t ht)
      (fun j hj hja => ha t ht j hj i (Finset.mem_univ i) hja (hi.trans hFw))
  refine ⟨hLip, fun t ht i hi => (hsel t ht i hi).deriv, hcont, hLQ, fun t ht => ?_⟩
  obtain ⟨i, -, he⟩ := Finset.exists_mem_eq_sup' hne (fun i => f i (x - t • (x - xstar)))
  have hFw := hrep _ (hBU (hIB t ht))
  have hia : f i (x - t • (x - xstar)) = F (x - t • (x - xstar)) := by rw [hFw]; exact he.symm
  have hQ := hsel t ht i hia
  rw [hQ.deriv]
  have hcurve := FiniteMaxRadial.inward_curve_hasDerivAt xstar x t
  apply hQ.congr_of_eventuallyEq
  filter_upwards [hcurve.continuousAt.eventually (hU.mem_nhds (hBU (hIB t ht)))] with s hs
  exact hrep _ hs


theorem central_eq {n : ℕ} (F : Vec n → ℝ) (xstar w : Vec n) :
    (fun t : ℝ => F (w + t • (w - xstar)) + F (w - t • (w - xstar)) - 2 * F w) =
      RadialCertificate.centralDifference F xstar w := by
  funext t
  unfold RadialCertificate.centralDifference RadialCertificate.outwardPoint
    RadialCertificate.inwardPoint
  rw [neg_smul, sub_neg_eq_add]

/-- Item `C/04_R/prose/080` (`companion/chapters/04_R.tex:370`): "The necessity for (RS) is
also clear on genuine active ties: if the active radial derivatives differ by
$J>0$, the one-dimensional central second difference at the tie is $J|t|+O(t^2)$, not $O(t^2)$."
(Wording point W21 applied on 15 October 2026; before "the old radial condition".) At $w\in U$,
with $J$ the spread (maximum minus minimum) of the active radial derivatives
$\nabla f_i(w)^T(w-x_*)$, $i\in I(w)$ (`activeRadialJump`): the central second difference along the
ray, $F(w+t(w-x_*))+F(w-t(w-x_*))-2F(w)$, is $J|t|+O(t^2)$, and is not $O(t^2)$ if $J>0$. For
convex branches, a strict gap between two active radial derivatives at a tie $w$ with
$F_*<F(w)<b$ excludes (RS) on $\{F\le b\}$ (the library's `active_gap_forbids_radial`). -/
theorem finite_max_necessity {n : ℕ} {ι : Type*} [Fintype ι]
    (hne : (Finset.univ : Finset ι).Nonempty)
    {F : Vec n → ℝ} (xstar : Vec n) (U : Set (Vec n)) (hU : IsOpen U)
    (f : ι → Vec n → ℝ) (hf : ∀ i, ContDiffOn ℝ 2 (f i) U)
    (hrep : ∀ w ∈ U, F w = Finset.univ.sup' hne fun i => f i w) (w : Vec n) (hw : w ∈ U) :
    ((fun t : ℝ => (F (w + t • (w - xstar)) + F (w - t • (w - xstar)) - 2 * F w) -
        FiniteMaxRadial.activeRadialJump hne f w (w - xstar) * |t|) =O[𝓝 0] fun t => t ^ 2) ∧
      (0 < FiniteMaxRadial.activeRadialJump hne f w (w - xstar) →
        ¬ (fun t : ℝ => F (w + t • (w - xstar)) + F (w - t • (w - xstar)) - 2 * F w) =O[𝓝 0]
          fun t => t ^ 2) ∧
      (ConvexOn ℝ univ F → (∀ i, ConvexOn ℝ U (f i)) → (∀ x, F xstar ≤ F x) →
        ∀ i j, f i w = F w → f j w = F w →
          dot (coordinateGradient (f j) w) (w - xstar) <
              dot (coordinateGradient (f i) w) (w - xstar) →
          F xstar < F w → ∀ b : ℝ, F w < b → ¬ RS F xstar {x | F x ≤ b}) := by
  refine ⟨?_, fun hJ => ?_, fun hF hfc hmin i j hi hj hlt hlo b hb => ?_⟩
  · have hpt : ∀ t : ℝ, F (w + t • (w - xstar)) + F (w - t • (w - xstar)) - 2 * F w =
        RadialCertificate.centralDifference F xstar w t :=
      fun t => congrFun (central_eq F xstar w) t
    simp only [hpt]
    exact FiniteMaxRadial.finite_max_central_isBigO (star := xstar) hne f hU hw hf hrep
  · rw [central_eq]
    exact FiniteMaxRadial.finite_max_central_not_isBigO (star := xstar) hne f hU hw hf hrep hJ
  · have hle : ∀ k, ∀ x ∈ U, f k x ≤ F x := fun k x hx => by
      rw [hrep x hx]; exact Finset.le_sup' (fun i => f i x) (Finset.mem_univ k)
    have hdi : DifferentiableAt ℝ (f i) w :=
      ((hf i).differentiableOn (by norm_num) w hw).differentiableAt (hU.mem_nhds hw)
    have hdj : DifferentiableAt ℝ (f j) w :=
      ((hf j).differentiableOn (by norm_num) w hw).differentiableAt (hU.mem_nhds hw)
    rw [RS_iff_library]
    refine FiniteMaxRadial.active_gap_forbids_radial hF hU (hfc i) (hfc j) (hle i) (hle j) hw hi hj
      hdi.hasFDerivAt hdj.hasFDerivAt ?_ hmin hlo hb
    rw [branch_fderiv_eq_dot hU (hf i) hw, branch_fderiv_eq_dot hU (hf j) hw]
    exact hlt

/-- Item `C/04_R/prose/081` (`companion/chapters/04_R.tex:370`): "Thus radial compatibility
describes the exact no-jump part of the criterion for this finite smooth-branch class." At every
$w\in U$: the central second difference along the ray is $O(t^2)$ exactly when all active branches
satisfy the compatibility condition $(\nabla f_i(w)-\nabla f_j(w))^T(w-x_*)=0$ of display
`disp/044`. -/
theorem finite_max_quadratic_iff {n : ℕ} {ι : Type*} [Fintype ι]
    (hne : (Finset.univ : Finset ι).Nonempty)
    {F : Vec n → ℝ} (xstar : Vec n) (U : Set (Vec n)) (hU : IsOpen U)
    (f : ι → Vec n → ℝ) (hf : ∀ i, ContDiffOn ℝ 2 (f i) U)
    (hrep : ∀ w ∈ U, F w = Finset.univ.sup' hne fun i => f i w) (w : Vec n) (hw : w ∈ U) :
    ((fun t : ℝ => F (w + t • (w - xstar)) + F (w - t • (w - xstar)) - 2 * F w) =O[𝓝 0]
        fun t => t ^ 2) ↔
      ∀ i j, f i w = F w → f j w = F w →
        dot (coordinateGradient (f i) w - coordinateGradient (f j) w) (w - xstar) = 0 := by
  rw [central_eq,
    FiniteMaxRadial.finite_max_central_quadratic_iff (star := xstar) hne f hU hw hf hrep]
  constructor
  · intro h i j hi hj
    have := h i hi j hj
    rw [branch_fderiv_eq_dot hU (hf i) hw, branch_fderiv_eq_dot hU (hf j) hw] at this
    rw [dot_sub_left]; linarith
  · intro h i hi j hj
    have := h i j hi hj
    rw [dot_sub_left] at this
    rw [branch_fderiv_eq_dot hU (hf i) hw, branch_fderiv_eq_dot hU (hf j) hw]
    linarith


/-! ### Section 4.7.1: the parabolic ridge (lines 386-400)

$F(u,v)=\max\{u^2+v,2u^2-v\}$ is the library's `ParabolicRadialBoundary.objective`
(`objective_eq_max`); $(u,v)$ is `x : Vec 2` with $u=x_0$, $v=x_1$. -/

theorem parabolic_eq (F : Vec 2 → ℝ)
    (hF_def : ∀ x, F x = max ((x 0) ^ 2 + x 1) (2 * (x 0) ^ 2 - x 1)) : F =
    ParabolicRadialBoundary.objective :=
  funext fun x => (hF_def x).trans (ParabolicRadialBoundary.objective_eq_max x).symm

/-- Item `C/04_R/disp/045` (`companion/chapters/04_R.tex:387-389`): "For
$F(u,v)=\max\{u^2+v,2u^2-v\}$, $x_*=0$": $F$ is finite and convex, $F(0)=0$, $0$ is its unique
minimizer, and all sublevels are compact. -/
theorem parabolic_objective (F : Vec 2 → ℝ)
    (hF_def : ∀ x, F x = max ((x 0) ^ 2 + x 1) (2 * (x 0) ^ 2 - x 1)) :
    ConvexOn ℝ univ F ∧ F 0 = 0 ∧ (∀ x, F 0 ≤ F x) ∧ (∀ x, F x = F 0 → x = 0) ∧
      ∀ b : ℝ, IsCompact {x | F x ≤ b} := by
  obtain rfl := parabolic_eq F hF_def
  have h0 := ParabolicRadialBoundary.objective_zero
  refine ⟨ParabolicRadialBoundary.objective_convex, h0, fun x => by
    rw [h0]; exact ParabolicRadialBoundary.unique_minimizer.1 x, fun x hx => by
    rw [h0] at hx; exact ParabolicRadialBoundary.unique_minimizer.2 x hx,
    ParabolicRadialBoundary.sublevel_compact⟩

/-- Item `C/04_R/prose/083` (`companion/chapters/04_R.tex:390`): "the switching curve is
$v=u^2/2$": the two branches are equal exactly on $v=u^2/2$. -/
theorem parabolic_switching (u v : ℝ) : u ^ 2 + v = 2 * u ^ 2 - v ↔ v = u ^ 2 / 2 := by
  constructor <;> intro h <;> linarith

/-- Item `C/04_R/prose/084` (`companion/chapters/04_R.tex:390`): "At $w=(u,u^2/2)$, $u\ne0$, the
active gradient difference is $(-2u,2)$ and its radial inner product is $-u^2\ne0$." Both
branches are active at $w$, their gradients are $(2u,1)$ and $(4u,-1)$, and
$((2u,1)-(4u,-1))^T(w-0)=-u^2\ne0$. -/
theorem parabolic_tie (F : Vec 2 → ℝ)
    (hF_def : ∀ x, F x = max ((x 0) ^ 2 + x 1) (2 * (x 0) ^ 2 - x 1)) (u : ℝ) (hu : u ≠ 0) :
    u ^ 2 + u ^ 2 / 2 = F ![u, u ^ 2 / 2] ∧ 2 * u ^ 2 - u ^ 2 / 2 = F ![u, u ^ 2 / 2] ∧
      HasFDerivAt (fun x : Vec 2 => (x 0) ^ 2 + x 1)
          (gradientFunctional ![2 * u, 1]) ![u, u ^ 2 / 2] ∧
      HasFDerivAt (fun x : Vec 2 => 2 * (x 0) ^ 2 - x 1) (gradientFunctional ![4 * u, -1])
        ![u, u ^ 2 / 2] ∧
      (![2 * u, 1] - ![4 * u, -1] : Vec 2) = ![-2 * u, 2] ∧
      dot (![-2 * u, 2] : Vec 2) (![u, u ^ 2 / 2] - 0) = -u ^ 2 ∧ -u ^ 2 ≠ 0 := by
  have h1 := ParabolicRadialBoundary.family.branch_hasGradient 0 ![u, u ^ 2 / 2]
  have h2 := ParabolicRadialBoundary.family.branch_hasGradient 1 ![u, u ^ 2 / 2]
  have e1 : ParabolicRadialBoundary.family.branch 0 = fun x : Vec 2 => (x 0) ^ 2 + x 1 := by
    funext x; simp [Parabolic.Family.branch, ParabolicRadialBoundary.family]
  have e2 : ParabolicRadialBoundary.family.branch 1 = fun x : Vec 2 => 2 * (x 0) ^ 2 - x 1 := by
    funext x; simp [Parabolic.Family.branch, ParabolicRadialBoundary.family]; ring
  rw [e1] at h1
  rw [e2] at h2
  have g1 : ParabolicRadialBoundary.family.branchGradient 0 ![u, u ^ 2 / 2] = ![2 * u, 1] := by
    ext i; fin_cases i <;> simp [Parabolic.Family.branchGradient, ParabolicRadialBoundary.family]
  have g2 : ParabolicRadialBoundary.family.branchGradient 1 ![u, u ^ 2 / 2] = ![4 * u, -1] := by
    ext i; fin_cases i <;> simp [Parabolic.Family.branchGradient, ParabolicRadialBoundary.family]
    norm_num
  rw [g1] at h1
  rw [g2] at h2
  have hv : F ![u, u ^ 2 / 2] = 3 * u ^ 2 / 2 := by
    rw [hF_def]; simp; rw [max_eq_left (by linarith)]; ring
  refine ⟨by rw [hv]; ring, by rw [hv]; ring, h1, h2, ?_, ?_, by
    simpa using pow_ne_zero 2 hu⟩
  · ext i; fin_cases i <;> simp <;> ring
  · simp [dot, Fin.sum_univ_two]; ring

/-- Item `C/04_R/prose/085` (`companion/chapters/04_R.tex:390`): "A ray crosses a genuine
one-dimensional kink there." For $u\ne0$ the restriction $s\mapsto F(sw)$ of $F$ to the ray
through $w=(u,u^2/2)$ is not differentiable at $s=1$ (one-sided derivatives $5u^2/2$ and
$7u^2/2$). -/
theorem parabolic_ray_kink (F : Vec 2 → ℝ)
    (hF_def : ∀ x, F x = max ((x 0) ^ 2 + x 1) (2 * (x 0) ^ 2 - x 1)) (u : ℝ) (hu : u ≠ 0) :
    ¬ DifferentiableAt ℝ (fun s : ℝ => F (s • ![u, u ^ 2 / 2])) 1 := by
  intro hd
  have hφ : ∀ s : ℝ, F (s • ![u, u ^ 2 / 2]) =
      max (s ^ 2 * u ^ 2 + s * (u ^ 2 / 2)) (2 * (s ^ 2 * u ^ 2) - s * (u ^ 2 / 2)) := by
    intro s; rw [hF_def]; simp; ring_nf
  have hu2 : 0 < u ^ 2 := by positivity
  set p1 : ℝ → ℝ := fun s => s ^ 2 * u ^ 2 + s * (u ^ 2 / 2) with hp1
  set p2 : ℝ → ℝ := fun s => 2 * (s ^ 2 * u ^ 2) - s * (u ^ 2 / 2) with hp2
  have hd1 : HasDerivAt p1 (2 * u ^ 2 + u ^ 2 / 2) 1 := by
    have := ((hasDerivAt_pow 2 (1 : ℝ)).mul_const (u ^ 2)).add
      ((hasDerivAt_id (1 : ℝ)).mul_const (u ^ 2 / 2))
    exact this.congr_deriv (by norm_num)
  have hd2 : HasDerivAt p2 (4 * u ^ 2 - u ^ 2 / 2) 1 := by
    have := (((hasDerivAt_pow 2 (1 : ℝ)).mul_const (u ^ 2)).const_mul 2).sub
      ((hasDerivAt_id (1 : ℝ)).mul_const (u ^ 2 / 2))
    exact this.congr_deriv (by norm_num; ring)
  have hD := hd.hasDerivAt
  have hleft : (fun s : ℝ => F (s • ![u, u ^ 2 / 2])) =ᶠ[𝓝[<] 1] p1 := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with s hs
    rw [hφ, max_eq_left]
    nlinarith [mul_nonneg (mul_nonneg hs.1.le hu2.le) (sub_nonneg.mpr hs.2.le)]
  have hright : (fun s : ℝ => F (s • ![u, u ^ 2 / 2])) =ᶠ[𝓝[>] 1] p2 := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : (1 : ℝ) < s := hs
    rw [hφ, max_eq_right]
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ s) hu2.le) (sub_nonneg.mpr hs'.le)]
  have h1val : (fun s : ℝ => F (s • ![u, u ^ 2 / 2])) 1 = p1 1 := by
    simp only [hφ, hp1]; rw [max_eq_left (by nlinarith)]
  have h2val : (fun s : ℝ => F (s • ![u, u ^ 2 / 2])) 1 = p2 1 := by
    simp only [hφ, hp2]; rw [max_eq_right (by nlinarith)]
  have e1 := (uniqueDiffWithinAt_Iio (1 : ℝ)).eq_deriv _
    (hD.hasDerivWithinAt.congr_of_eventuallyEq hleft.symm h1val.symm) hd1.hasDerivWithinAt
  have e2 := (uniqueDiffWithinAt_Ioi (1 : ℝ)).eq_deriv _
    (hD.hasDerivWithinAt.congr_of_eventuallyEq hright.symm h2val.symm) hd2.hasDerivWithinAt
  rw [e1] at e2
  linarith

/-- Item `C/04_R/disp/046` (`companion/chapters/04_R.tex:391-394`): "For the descending pair
$x_\epsilon=(u,u^2/2-\epsilon)$, $z_\epsilon=(u,u^2/2+\epsilon/2)$": for $\epsilon>0$ both points
are differentiable, with gradients $g=(4u,-1)$ and $h=(2u,1)$, and $F(z_\epsilon)=3u^2/2+\epsilon/2<
F(x_\epsilon)=3u^2/2+\epsilon$. -/
theorem parabolic_pair (F : Vec 2 → ℝ)
    (hF_def : ∀ x, F x = max ((x 0) ^ 2 + x 1) (2 * (x 0) ^ 2 - x 1)) (u ε : ℝ) (hε : 0 < ε) :
    HasFDerivAt F (gradientFunctional ![4 * u, -1]) ![u, u ^ 2 / 2 - ε] ∧
      HasFDerivAt F (gradientFunctional ![2 * u, 1]) ![u, u ^ 2 / 2 + ε / 2] ∧
      F ![u, u ^ 2 / 2 - ε] = 3 * u ^ 2 / 2 + ε ∧
          F ![u, u ^ 2 / 2 + ε / 2] = 3 * u ^ 2 / 2 + ε / 2 ∧
      F ![u, u ^ 2 / 2 + ε / 2] < F ![u, u ^ 2 / 2 - ε] := by
  obtain rfl := parabolic_eq F hF_def
  obtain ⟨hv1, hv2⟩ := ParabolicRadialBoundary.pair_values (u := u) hε
  obtain ⟨hg1, hg2⟩ := ParabolicRadialBoundary.pair_gradients (u := u) hε
  refine ⟨hg1, hg2, hv1, hv2, ?_⟩
  change ParabolicRadialBoundary.objective (ParabolicRadialBoundary.newPoint u ε) <
    ParabolicRadialBoundary.objective (ParabolicRadialBoundary.oldPoint u ε)
  rw [hv1, hv2]
  linarith

/-- Item `C/04_R/disp/047` (`companion/chapters/04_R.tex:396-399`): "the ratio is exactly
\[ \frac{(y^Tz_\epsilon)^2}{y^T(z_\epsilon-x_\epsilon)}
  =\frac{(u^2-\epsilon)^2}{3\epsilon}\to\infty", \]
with $y=h-g$, for $\epsilon>0$; the limit is as $\epsilon\to0^+$, for $u\ne0$. -/
theorem parabolic_ratio (u : ℝ) :
    (∀ ε : ℝ, (dot (![2 * u, 1] - ![4 * u, -1]) ![u, u ^ 2 / 2 + ε / 2]) ^ 2 /
      dot (![2 * u, 1] - ![4 * u, -1]) (![u, u ^ 2 / 2 + ε / 2] - ![u, u ^ 2 / 2 - ε]) =
        (u ^ 2 - ε) ^ 2 / (3 * ε)) ∧
    (u ≠ 0 → Tendsto (fun ε => (dot (![2 * u, 1] - ![4 * u, -1]) ![u, u ^ 2 / 2 + ε / 2]) ^ 2 /
      dot (![2 * u, 1] - ![4 * u, -1]) (![u, u ^ 2 / 2 + ε / 2] - ![u, u ^ 2 / 2 - ε]))
      (𝓝[>] 0) atTop) := by
  have he : ∀ ε : ℝ, (dot (![2 * u, 1] - ![4 * u, -1]) ![u, u ^ 2 / 2 + ε / 2]) ^ 2 /
      dot (![2 * u, 1] - ![4 * u, -1]) (![u, u ^ 2 / 2 + ε / 2] - ![u, u ^ 2 / 2 - ε]) =
      (RadialCertificate.radialNumerator 0 (ParabolicRadialBoundary.newPoint u ε)
        (ParabolicRadialBoundary.oldGradient u) (ParabolicRadialBoundary.newGradient u)) ^ 2 /
      TransportedCertificate.pairCurvature (ParabolicRadialBoundary.oldPoint u ε)
        (ParabolicRadialBoundary.newPoint u ε) (ParabolicRadialBoundary.oldGradient u)
        (ParabolicRadialBoundary.newGradient u) := by
    intro ε
    simp only [RadialCertificate.radialNumerator, TransportedCertificate.pairCurvature,
      TransportedCertificate.pairStep, sub_zero, ParabolicRadialBoundary.newPoint,
      ParabolicRadialBoundary.oldPoint, ParabolicRadialBoundary.newGradient,
      ParabolicRadialBoundary.oldGradient]
  refine ⟨fun ε => by rw [he]; exact ParabolicRadialBoundary.radial_quotient u ε, fun hu => ?_⟩
  simp only [he]
  exact ParabolicRadialBoundary.radial_quotient_tendsto hu

/-- Item `C/04_R/prose/086` (`companion/chapters/04_R.tex:400`): "This fails (RS) on a positive
objective band in every neighborhood of zero." For every neighborhood $N$ of $0$ there is a band
$\eta>0$ on which no constant works: (RS) fails on $N$. -/
theorem parabolic_RS_fails (F : Vec 2 → ℝ)
    (hF_def : ∀ x, F x = max ((x 0) ^ 2 + x 1) (2 * (x 0) ^ 2 - x 1)) (N : Set (Vec 2))
    (hN : N ∈ 𝓝 (0 : Vec 2)) :
    ¬ RS F 0 N := by
  obtain rfl := parabolic_eq F hF_def
  rw [RS_iff_library]
  exact ParabolicRadialBoundary.not_radial_secant_on_neighborhood hN


/-! ### Section 4.7.2: a spectral regularizer (lines 406-429)

Symmetric $2\times2$ matrices are written in orthonormal coordinates `x : Vec 3`,
$X=\begin{pmatrix}x_0&x_1/\sqrt2\\x_1/\sqrt2&x_2\end{pmatrix}$ (`NuclearSymmetric2.matrix x`), in
which the Frobenius inner product is `dot` (`NuclearSymmetric2.frobenius_matrix`); $F$ is
`NuclearSymmetric2.objective`, $C$ is `center`, $X_*$ is `minimizer`. For an angle $\theta$, the
library's `trigRotation θ` has $c=\cos\theta$, $s=\sin\theta$, $v$, $u$, $W$, $U$, the pair
$X_\epsilon$ = `oldPoint ε`, $Z_\epsilon$ = `newPoint ε` and their gradients. -/

/-- Item `C/04_R/disp/048` (`companion/chapters/04_R.tex:409-412`): "Work in symmetric $2\times2$
matrices with the Frobenius inner product. Let $F(X)=\frac12\|X-C\|_F^2+\|X\|_*$,
$C=\operatorname{diag}(2,0)$, $X_*=\operatorname{diag}(1,0)$." The library's objective is this
function on every symmetric matrix (the nuclear norm of a symmetric matrix being the sum of the
absolute values of its eigenvalues), in Frobenius-orthonormal coordinates. -/
theorem spectral_objective :
    (∀ (A : Mat 2) (hA : A.IsHermitian),
      NuclearSymmetric2.objective (NuclearSymmetric2.coordinates A) =
        NuclearSymmetric2.frobenius (A - !![2, 0; 0, 0]) (A - !![2, 0; 0, 0]) / 2 +
          NuclearSymmetric2.nuclear A hA ∧
        NuclearSymmetric2.nuclear A hA = ∑ i, |hA.eigenvalues i| ∧
        NuclearSymmetric2.matrix (NuclearSymmetric2.coordinates A) = A) ∧
    NuclearSymmetric2.matrix NuclearSymmetric2.center = !![2, 0; 0, 0] ∧
    NuclearSymmetric2.matrix NuclearSymmetric2.minimizer = !![1, 0; 0, 0] ∧
    ∀ x z : Vec 3, NuclearSymmetric2.frobenius (NuclearSymmetric2.matrix x)
      (NuclearSymmetric2.matrix z) = dot x z := by
  refine ⟨fun A hA => ⟨?_, rfl, NuclearSymmetric2.matrix_coordinates A hA⟩,
    NuclearSymmetric2.matrix_center, NuclearSymmetric2.matrix_minimizer,
    NuclearSymmetric2.frobenius_matrix⟩
  rw [NuclearSymmetric2.objective_on_symmetric A hA, NuclearSymmetric2.matrix_center]

/-- Item `C/04_R/prose/088` (`companion/chapters/04_R.tex:413`): "This is strongly convex and
uniquely minimized at $X_*$. Indeed $X_*-C=\operatorname{diag}(-1,0)$ is canceled by a nuclear-norm
subgradient $\operatorname{diag}(1,0)$ there." Strong convexity with modulus one in the Frobenius
norm; $X_*$ is the unique minimizer; $X_*-C=\operatorname{diag}(-1,0)$;
$\operatorname{diag}(1,0)$ is a subgradient of the nuclear norm at $X_*$, and
$(X_*-C)+\operatorname{diag}(1,0)=0$. -/
theorem spectral_minimizer :
    (∀ x z : Vec 3, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      NuclearSymmetric2.objective (a • x + b • z) ≤
        a * NuclearSymmetric2.objective x + b * NuclearSymmetric2.objective z -
          a * b / 2 *
              NuclearSymmetric2.frobenius (NuclearSymmetric2.matrix z - NuclearSymmetric2.matrix x)
            (NuclearSymmetric2.matrix z - NuclearSymmetric2.matrix x)) ∧
    (∀ x, NuclearSymmetric2.objective NuclearSymmetric2.minimizer ≤ NuclearSymmetric2.objective x) ∧
    (∀ x, NuclearSymmetric2.objective x = NuclearSymmetric2.objective NuclearSymmetric2.minimizer →
      x = NuclearSymmetric2.minimizer) ∧
    NuclearSymmetric2.matrix NuclearSymmetric2.minimizer -
        NuclearSymmetric2.matrix NuclearSymmetric2.center =
      !![-1, 0; 0, 0] ∧
    (∀ z, NuclearSymmetric2.nuclearCoords NuclearSymmetric2.minimizer +
      dot NuclearSymmetric2.minimizer (z - NuclearSymmetric2.minimizer) ≤
          NuclearSymmetric2.nuclearCoords z) ∧
    NuclearSymmetric2.matrix NuclearSymmetric2.minimizer = !![1, 0; 0, 0] ∧
    NuclearSymmetric2.minimizer - NuclearSymmetric2.center + NuclearSymmetric2.minimizer = 0 := by
  refine ⟨fun x z a b ha hb hab => NuclearSymmetric2.objective_frobenius_strong x z ha hb hab,
    NuclearSymmetric2.objective_minimum, NuclearSymmetric2.objective_unique, ?_, fun z => ?_,
    NuclearSymmetric2.matrix_minimizer, NuclearSymmetric2.minimizer_gradient_cancellation⟩
  · rw [NuclearSymmetric2.matrix_minimizer, NuclearSymmetric2.matrix_center]
    ext i j; fin_cases i <;> fin_cases j <;> norm_num
  · have := NuclearSymmetric2.nuclear_minimizer_support z
    linarith

/-- Item `C/04_R/disp/049` (`companion/chapters/04_R.tex:416-418`): "Take orthonormal vectors
$v=(\cos\theta,\sin\theta)$, $u=(-\sin\theta,\cos\theta)$." -/
theorem spectral_vectors (θ : ℝ) :
    (NuclearSymmetric2.trigRotation θ).v = ![Real.cos θ, Real.sin θ] ∧
      (NuclearSymmetric2.trigRotation θ).u = ![-Real.sin θ, Real.cos θ] ∧
      dot ![Real.cos θ, Real.sin θ] ![Real.cos θ, Real.sin θ] = 1 ∧
      dot ![-Real.sin θ, Real.cos θ] ![-Real.sin θ, Real.cos θ] = 1 ∧
      dot ![Real.cos θ, Real.sin θ] ![-Real.sin θ, Real.cos θ] = 0 :=
  ⟨rfl, rfl, (NuclearSymmetric2.trigRotation θ).vectors_orthonormal⟩

/-- Item `C/04_R/prose/089` (`companion/chapters/04_R.tex:419`): the definitions $W=vv^T$,
$U=uu^T$, $a=\sin^2\theta$; $a>0$ exactly when $\sin\theta\ne0$, the hypothesis of the statements
below. In coordinates, `W` and `U` are the library's `Rotation.W`, `Rotation.U`. -/
theorem spectral_W_U (θ : ℝ) :
    NuclearSymmetric2.matrix (NuclearSymmetric2.trigRotation θ).W =
        outer (NuclearSymmetric2.trigRotation θ).v (NuclearSymmetric2.trigRotation θ).v ∧
      NuclearSymmetric2.matrix (NuclearSymmetric2.trigRotation θ).U =
        outer (NuclearSymmetric2.trigRotation θ).u (NuclearSymmetric2.trigRotation θ).u ∧
      (0 < Real.sin θ ^ 2 ↔ Real.sin θ ≠ 0) :=
  ⟨(NuclearSymmetric2.trigRotation θ).matrix_W, (NuclearSymmetric2.trigRotation θ).matrix_U,
    ⟨fun h h0 => by rw [h0] at h; simp at h, fun h => by positivity⟩⟩

/-- Item `C/04_R/disp/050` (`companion/chapters/04_R.tex:420-422`): "For
$X_\epsilon=W-\epsilon U$, $Z_\epsilon=W+\epsilon U$": the matrices of the pair. -/
theorem spectral_pair_form (θ ε : ℝ) :
    NuclearSymmetric2.matrix ((NuclearSymmetric2.trigRotation θ).oldPoint ε) =
        outer (NuclearSymmetric2.trigRotation θ).v (NuclearSymmetric2.trigRotation θ).v -
          ε • outer (NuclearSymmetric2.trigRotation θ).u (NuclearSymmetric2.trigRotation θ).u ∧
      NuclearSymmetric2.matrix ((NuclearSymmetric2.trigRotation θ).newPoint ε) =
        outer (NuclearSymmetric2.trigRotation θ).v (NuclearSymmetric2.trigRotation θ).v +
          ε • outer (NuclearSymmetric2.trigRotation θ).u (NuclearSymmetric2.trigRotation θ).u :=
  (NuclearSymmetric2.trigRotation θ).pair_matrix_form ε

/-- Item `C/04_R/prose/090` (`companion/chapters/04_R.tex:423`): "both nuclear norms are
differentiable, since the matrices have nonzero eigenvalues." For $\epsilon>0$ (determinants
$\mp\epsilon$). -/
theorem spectral_pair_differentiable (θ ε : ℝ) (hε : 0 < ε) :
    (∀ i, (NuclearSymmetric2.matrix_hermitian
        ((NuclearSymmetric2.trigRotation θ).oldPoint ε)).eigenvalues i ≠ 0) ∧
      (∀ i, (NuclearSymmetric2.matrix_hermitian
          ((NuclearSymmetric2.trigRotation θ).newPoint ε)).eigenvalues i ≠ 0) ∧
      DifferentiableAt ℝ NuclearSymmetric2.nuclearCoords
          ((NuclearSymmetric2.trigRotation θ).oldPoint ε) ∧
      DifferentiableAt ℝ NuclearSymmetric2.nuclearCoords
          ((NuclearSymmetric2.trigRotation θ).newPoint ε) :=
  ⟨((NuclearSymmetric2.trigRotation θ).pair_eigenvalues_nonzero hε).1,
    ((NuclearSymmetric2.trigRotation θ).pair_eigenvalues_nonzero hε).2,
    ((NuclearSymmetric2.trigRotation θ).old_nuclear_hasGradient hε).differentiableAt,
    (NuclearSymmetric2.nuclearCoords_hasGradient_pos
      ((NuclearSymmetric2.trigRotation θ).positive_branch_new hε)).differentiableAt⟩

/-- Item `C/04_R/prose/091` (`companion/chapters/04_R.tex:423`): "The pair is descending:
$F(Z_\epsilon)-F(X_\epsilon)=-4a\epsilon<0$", for $\epsilon>0$ and $a=\sin^2\theta>0$. -/
theorem spectral_descent (θ ε : ℝ) (hε : 0 < ε) (hθ : Real.sin θ ≠ 0) :
    NuclearSymmetric2.objective ((NuclearSymmetric2.trigRotation θ).newPoint ε) -
        NuclearSymmetric2.objective ((NuclearSymmetric2.trigRotation θ).oldPoint ε) =
      -4 * Real.sin θ ^ 2 * ε ∧ -4 * Real.sin θ ^ 2 * ε < 0 := by
  refine ⟨(NuclearSymmetric2.trigRotation θ).pair_descent ε hε, ?_⟩
  have : 0 < Real.sin θ ^ 2 := by positivity
  nlinarith

/-- Item `C/04_R/prose/092` (`companion/chapters/04_R.tex:423`): "Its gradient difference is
$y=2(1+\epsilon)U$": for $\epsilon>0$ the gradients of $F$ at $X_\epsilon$, $Z_\epsilon$ are
`oldGradient ε`, `newGradient ε`, and their difference is $2(1+\epsilon)U$. -/
theorem spectral_gradient_difference (θ ε : ℝ) (hε : 0 < ε) :
    HasFDerivAt NuclearSymmetric2.objective
        (gradientFunctional ((NuclearSymmetric2.trigRotation θ).oldGradient ε))
        ((NuclearSymmetric2.trigRotation θ).oldPoint ε) ∧
      HasFDerivAt NuclearSymmetric2.objective
        (gradientFunctional ((NuclearSymmetric2.trigRotation θ).newGradient ε))
        ((NuclearSymmetric2.trigRotation θ).newPoint ε) ∧
      (NuclearSymmetric2.trigRotation θ).newGradient ε -
          (NuclearSymmetric2.trigRotation θ).oldGradient ε =
        (2 * (1 + ε)) • (NuclearSymmetric2.trigRotation θ).U :=
  ⟨((NuclearSymmetric2.trigRotation θ).pair_gradients hε).1,
    ((NuclearSymmetric2.trigRotation θ).pair_gradients hε).2,
    (NuclearSymmetric2.trigRotation θ).gradient_difference ε⟩

/-- Item `C/04_R/disp/051` (`companion/chapters/04_R.tex:424-428`): "so
$T=4\epsilon(1+\epsilon)$, $N=2(1+\epsilon)(\epsilon-a)$,
$\frac{N^2}{T}=\frac{(1+\epsilon)(\epsilon-a)^2}{\epsilon}\to\infty$", with $y$ the gradient
difference, $T=y^T(Z_\epsilon-X_\epsilon)$, $N=y^T(Z_\epsilon-X_*)$, $a=\sin^2\theta$; the ratio for
$\epsilon>0$, the limit as $\epsilon\to0^+$ when $\sin\theta\ne0$. -/
theorem spectral_ratio (θ : ℝ) :
    let P := NuclearSymmetric2.trigRotation θ
    (∀ ε : ℝ,
        dot (P.newGradient ε - P.oldGradient ε) (P.newPoint ε - P.oldPoint ε) = 4 * ε * (1 + ε)) ∧
      (∀ ε : ℝ,
          dot (P.newGradient ε - P.oldGradient ε) (P.newPoint ε - NuclearSymmetric2.minimizer) =
        2 * (1 + ε) * (ε - Real.sin θ ^ 2)) ∧
      (∀ ε : ℝ, 0 < ε →
        (dot (P.newGradient ε - P.oldGradient ε) (P.newPoint ε - NuclearSymmetric2.minimizer)) ^ 2 /
          dot (P.newGradient ε - P.oldGradient ε) (P.newPoint ε - P.oldPoint ε) =
            (1 + ε) * (ε - Real.sin θ ^ 2) ^ 2 / ε) ∧
      (Real.sin θ ≠ 0 → Tendsto (fun ε =>
        (dot (P.newGradient ε - P.oldGradient ε) (P.newPoint ε - NuclearSymmetric2.minimizer)) ^ 2 /
          dot (P.newGradient ε - P.oldGradient ε) (P.newPoint ε - P.oldPoint ε)) (𝓝[>] 0) atTop) :=
  ⟨(NuclearSymmetric2.trigRotation θ).pair_curvature,
    (NuclearSymmetric2.trigRotation θ).radial_numerator,
    fun _ hε => (NuclearSymmetric2.trigRotation θ).radial_quotient hε,
    fun h => (NuclearSymmetric2.trigRotation θ).radial_quotient_tendsto h⟩

/-- Item `C/04_R/prose/093` (`companion/chapters/04_R.tex:429`): "Also $F(W)-F(X_*)=2a>0$", for
$a=\sin^2\theta>0$. -/
theorem spectral_base_gap (θ : ℝ) (hθ : Real.sin θ ≠ 0) :
    NuclearSymmetric2.objective (NuclearSymmetric2.trigRotation θ).W -
        NuclearSymmetric2.objective NuclearSymmetric2.minimizer = 2 * Real.sin θ ^ 2 ∧
      0 < 2 * Real.sin θ ^ 2 :=
  ⟨(NuclearSymmetric2.trigRotation θ).base_value, by positivity⟩

/-- Item `C/04_R/prose/094` (`companion/chapters/04_R.tex:429`): "Choosing small $\theta$ puts
such points arbitrarily close to $X_*$." $W\to X_*$ as $\theta\to0$ and $X_\epsilon,Z_\epsilon\to W$
as $\epsilon\to0^+$; hence every neighborhood of $X_*$ contains, for some $0<\theta<\pi$ (so
$\sin\theta\ne0$), the pairs with all small $\epsilon>0$. -/
theorem spectral_small_theta :
    Tendsto (fun θ => (NuclearSymmetric2.trigRotation θ).W) (𝓝 0) (𝓝 NuclearSymmetric2.minimizer) ∧
      ∀ N ∈ 𝓝 NuclearSymmetric2.minimizer, ∃ θ : ℝ, 0 < θ ∧ θ < Real.pi ∧
        ∀ᶠ ε in 𝓝[>] (0 : ℝ), (NuclearSymmetric2.trigRotation θ).oldPoint ε ∈ N ∧
          (NuclearSymmetric2.trigRotation θ).newPoint ε ∈ N := by
  refine ⟨?_, fun N hN => ?_⟩
  · rw [← NuclearSymmetric2.trigRotation_base_zero]
    exact NuclearSymmetric2.trigRotation_base_continuous.tendsto 0
  · obtain ⟨θ, hθ, hπ, hNθ⟩ := NuclearSymmetric2.exists_rotated_base hN
    exact ⟨θ, hθ, hπ, ((NuclearSymmetric2.trigRotation θ).pair_points_tendsto.1.eventually hNθ).and
      ((NuclearSymmetric2.trigRotation θ).pair_points_tendsto.2.eventually hNθ)⟩

/-- Item `C/04_R/prose/095` (`companion/chapters/04_R.tex:429`): "Thus this familiar
smooth-plus-nuclear-norm problem need not satisfy (RS) on any neighborhood of a nonzero
rank-deficient minimizer." (Wording point W21 applied on 15 October 2026; before "the original
local radial criterion at a nonzero rank-deficient minimizer".) (RS) fails on every neighborhood
of $X_*$, and $X_*\ne0$ has rank $1<2$. -/
theorem spectral_RS_fails :
    (∀ N ∈ 𝓝 NuclearSymmetric2.minimizer,
      ¬ RS NuclearSymmetric2.objective NuclearSymmetric2.minimizer N) ∧
      NuclearSymmetric2.minimizer ≠ 0 ∧
          (NuclearSymmetric2.matrix NuclearSymmetric2.minimizer).rank = 1 :=
  ⟨fun N hN => by
    rw [RS_iff_library]; exact NuclearSymmetric2.not_radial_secant_on_neighborhood hN,
    fun h => by simpa [NuclearSymmetric2.minimizer] using congrFun h 0,
    NuclearSymmetric2.minimizer_matrix_rank⟩

/-- Item `C/04_R/prose/096` (`companion/chapters/04_R.tex:429`): "The nuclear norm centered at
zero \emph{is} covered." The nuclear norm of symmetric $2\times2$ matrices has zero inward
remainder toward $0$, so (IR) holds on every set and (RS) on every compact set, and every
admissible run converges: $\|X_k\|_*\to0$, $X_k\to0$. -/
theorem centered_nuclear_covered :
    (∀ K : Set (Vec 3), IR NuclearSymmetric2.nuclearCoords 0 K) ∧
      (∀ K : Set (Vec 3), IsCompact K → RS NuclearSymmetric2.nuclearCoords 0 K) ∧
      ∀ run : AdmissibleBFGSRun 3 NuclearSymmetric2.nuclearCoords,
        Tendsto (fun k => NuclearSymmetric2.nuclearCoords (run.x k)) atTop (𝓝 0) ∧
          Tendsto run.x atTop (𝓝 0) :=
  ⟨fun K => (IR_iff_library _ _ K).mpr (NuclearSymmetric2.centered_nuclear_inward K),
    fun K hK => (RS_iff_library _ _ K).mpr (NuclearSymmetric2.centered_nuclear_radial hK),
    NuclearSymmetric2.centered_nuclear_convergence⟩

/-- Item `C/04_R/prose/096` (`companion/chapters/04_R.tex:429`), smooth plus nuclear norm with
minimizer zero: "The nuclear norm centered at zero \emph{is} covered", read against the preceding
sentence (a smooth-plus-nuclear-norm problem at a nonzero minimizer) and line 332 ("nuclear norm
when centered at zero"). For $F=\psi+\|\cdot\|_*$ on symmetric $2\times2$ matrices (coordinates
`NuclearSymmetric2.nuclearCoords`), $\psi$ convex and locally $C^{1,1}$, $0$ a minimizer of $F$
and $K=\{F\le b\}$ compact with $b>F(0)$: (IR) and (RS) hold on $K$, and every admissible run
starting in $K$ converges in value and in distance to $\arg\min F$, and to $0$ when $0$ is the
unique minimizer. This is display `disp/043` with $\gamma=\|\cdot\|_*$, $A=I$, $p=1$
(`mixed_powers_covered`); $\psi=0$ is `centered_nuclear_covered`. -/
theorem centered_nuclear_smooth_covered {F ψ : Vec 3 → ℝ} (hψ : ConvexOn ℝ univ ψ)
    (hψ11 : CenteredSmoothSublinear.LocallyC11On univ ψ)
    (hrep : ∀ x, F x = ψ x + NuclearSymmetric2.nuclearCoords x) (hmin : ∀ x, F 0 ≤ F x)
    (b : ℝ) (hb : F 0 < b) (K : Set (Vec 3)) (hK_def : K = {x | F x ≤ b}) (hK : IsCompact K) :
    IR F 0 K ∧ RS F 0 K ∧
      ∀ run : AdmissibleBFGSRun 3 F, F (run.x 0) ≤ b →
        Tendsto (fun k => F (run.x k)) atTop (𝓝 (F 0)) ∧
          Tendsto (fun k => euclideanSolutionDistance F (run.x k)) atTop (𝓝 0) ∧
          ((∀ x, F x = F 0 → x = 0) → Tendsto run.x atTop (𝓝 0)) := by
  have hN : Sublinear NuclearSymmetric2.nuclearCoords := (sublinear_iff _).mpr
    ⟨NuclearSymmetric2.nuclearCoords_convex, NuclearSymmetric2.nuclearCoords_homogeneous⟩
  have hN0 : ∀ x, 0 ≤ NuclearSymmetric2.nuclearCoords x := fun x =>
    NuclearSymmetric2.nuclearCoords_zero ▸ NuclearSymmetric2.nuclearCoords_minimum x
  have hF : ConvexOn ℝ univ F :=
    (hψ.add NuclearSymmetric2.nuclearCoords_convex).congr (fun x _ => (hrep x).symm)
  refine mixed_powers_covered hF 0 hmin b hb K hK_def hK ψ hψ hψ11 (ι := Unit) (fun _ => 3)
    (fun _ => NuclearSymmetric2.nuclearCoords) (fun _ => hN) (fun _ x => hN0 x)
    (fun _ => (1 : Matrix (Fin 3) (Fin 3) ℝ)) (fun _ => 1) (fun _ => le_rfl) (fun z => ?_)
  rw [zero_add, hrep]
  simp [Real.rpow_one]

/-! ### Relation to earlier work (lines 436-443) -/

/-- Item `C/04_R/prose/104` (`companion/chapters/04_R.tex:441`): "The Euclidean-norm theorem is
a known case recovered here." The Euclidean norm on $\R^n$, $n\ge1$, is finite sublinear
(`sublinear_examples`), so it satisfies (IR) toward $0$ on every sublevel (zero radial error), and
the radial argument (Corollary `art:radial-convergence`, `Article.Global.radial_convergence`) gives
$\|x_k\|\to0$ and $x_k\to0$ for every admissible run. -/
theorem euclidean_norm_recovered {n : ℕ} (hn : 1 ≤ n) :
    (∀ b : ℝ, IR (fun x : Vec n => ‖euclideanVector x‖) 0 {x | ‖euclideanVector x‖ ≤ b}) ∧
      ∀ run : AdmissibleBFGSRun n (fun x : Vec n => ‖euclideanVector x‖),
        Tendsto (fun k => ‖euclideanVector (run.x k)‖) atTop (𝓝 0) ∧ Tendsto run.x atTop (𝓝 0) := by
  have hsub := sublinear_examples.2.1 n
  obtain ⟨hc, hh⟩ := (sublinear_iff _).mp hsub
  have hIR : ∀ b : ℝ, IR (fun x : Vec n => ‖euclideanVector x‖) 0 {x | ‖euclideanVector x‖ ≤ b} :=
    fun b => (IR_iff_article _ _ _).mpr (Article.Global.homogeneous_inward_condition hc hh b).2
  refine ⟨hIR, fun run => ?_⟩
  obtain ⟨⟨hmin, huniq⟩, -⟩ := Article.Global.euclidean_norm_case hn
    (fun x : Vec n => ‖euclideanVector x‖) (fun x => Article.Global.norm_euclideanVector x)
  have h0 : ‖euclideanVector (0 : Vec n)‖ = 0 := by
    rw [show euclideanVector (0 : Vec n) = 0 from rfl, norm_zero]
  have hK := Article.Global.sublevels_compact_of_coercive (convex_continuous hc)
    (Article.Global.coercive_of_positive hn hc hh (fun x hx => by
      have := huniq x
      rcases (norm_nonneg (euclideanVector x)).lt_or_eq with h | h
      · exact h
      · exact absurd (this (fun y => by rw [← h]; exact norm_nonneg _)) hx))
    ‖euclideanVector (run.x 0)‖
  obtain ⟨hv, -, hi⟩ := Article.Global.radial_convergence hc 0 hmin _
    (Article.Global.initial_value_gt run 0 hmin) _ rfl hK
    (Or.inr ((IR_iff_article _ _ _).mp (hIR _))) run
    (show ‖euclideanVector (run.x 0)‖ ≤ ‖euclideanVector (run.x 0)‖ from le_rfl)
  rw [h0] at hv
  exact ⟨hv, hi huniq⟩

/-- Item `C/04_R/prose/106` (`companion/chapters/04_R.tex:443`): "The optimizer in this example
is a specialization of singular-value thresholding." For $C=\operatorname{diag}(2,0)$ (singular
values $2,0$) and threshold $1$, soft-thresholding the singular values gives
$\operatorname{diag}(\max\{2-1,0\},\max\{0-1,0\})=\operatorname{diag}(1,0)=X_*$, the unique
minimizer of $\frac12\|X-C\|_F^2+\|X\|_*$. (The general theorem [CCS10, Theorem 2.1] is cited, not
used; only this specialization is checked.) -/
theorem svt_specialization :
    NuclearSymmetric2.matrix NuclearSymmetric2.minimizer =
        !![max (2 - 1) 0, 0; 0, max (0 - 1) 0] ∧
      NuclearSymmetric2.matrix NuclearSymmetric2.center = !![2, 0; 0, 0] ∧
      (∀ x, NuclearSymmetric2.objective NuclearSymmetric2.minimizer ≤
          NuclearSymmetric2.objective x) ∧
      ∀ x, NuclearSymmetric2.objective x = NuclearSymmetric2.objective NuclearSymmetric2.minimizer →
        x = NuclearSymmetric2.minimizer := by
  refine ⟨?_, NuclearSymmetric2.matrix_center, NuclearSymmetric2.objective_minimum,
    NuclearSymmetric2.objective_unique⟩
  rw [NuclearSymmetric2.matrix_minimizer]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num


/-! ### Non-vacuity -/

/-- Tails of a run whose values tend to $F_*$ start below $F_*+\varepsilon$, for every
$\varepsilon>0$ (`AdmissibleBFGSRun.shift`). -/
theorem exists_low_run {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) {Fstar : ℝ}
    (hR : Tendsto (fun k => F (R.x k)) atTop (𝓝 Fstar)) (ε : ℝ) (hε : 0 < ε) :
    ∃ R' : AdmissibleBFGSRun n F, F (R'.x 0) ≤ Fstar + ε := by
  obtain ⟨J, hJ⟩ := (hR.eventually (eventually_lt_nhds (lt_add_of_pos_right Fstar hε))).exists
  exact ⟨R.shift J, hJ.le⟩

/-- The values of the run `Article.Global.absRun` on $|x|$ ($x_k=(-1/2)^k$) tend to $0$. -/
theorem absRun_values {F : Vec 1 → ℝ} (hF : ∀ x, F x = |x 0|) :
    Tendsto (fun k => F ((Article.Global.absRun F hF).x k)) atTop (𝓝 0) := by
  have h : ∀ k, F ((Article.Global.absRun F hF).x k) = (1 / 2) ^ k := by
    intro k
    rw [hF]
    show |OneDimensional.embed ((-1) ^ k * (1 / 2) ^ k) 0| = (1 / 2) ^ k
    rw [OneDimensional.embed_apply, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_pos (by positivity)]
  simp only [h]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- Facts on the benchmark $F(u,v)=u^2+|v|$ (`UnexcitedMetric.objective`): convex, minimized only
at $0$ with value $0$, compact sublevels; the values of every admissible run on it tend to $0$
(`Article.Global.mixed_benchmark`). -/
theorem bench_facts :
    ConvexOn ℝ univ UnexcitedMetric.objective ∧
      (∀ x, UnexcitedMetric.objective 0 ≤ UnexcitedMetric.objective x) ∧
      (∀ x, UnexcitedMetric.objective x = UnexcitedMetric.objective 0 → x = 0) ∧
      (∀ b : ℝ, IsCompact {x | UnexcitedMetric.objective x ≤ b}) ∧
      UnexcitedMetric.objective 0 = 0 ∧ (∀ x, UnexcitedMetric.objective x = x 0 ^ 2 + |x 1|) ∧
      ∀ R : AdmissibleBFGSRun 2 UnexcitedMetric.objective,
        Tendsto (fun k => UnexcitedMetric.objective (R.x k)) atTop (𝓝 0) := by
  obtain ⟨hconv, hmin, huniq, hK, -⟩ :=
    Article.Global.mixed_hypotheses UnexcitedMetric.objective (fun _ => rfl)
  refine ⟨hconv, hmin, fun x hx => huniq x (fun z => by rw [hx]; exact hmin z), hK,
    by simp [UnexcitedMetric.objective], fun _ => rfl,
    fun R => (Article.Global.mixed_benchmark UnexcitedMetric.objective (fun _ => rfl) R).1⟩

/-- One admissible run on the benchmark: the library's `UnexcitedMetric.run` with $c_1=1/4$,
$c_2=1/2$. -/
def benchRun : AdmissibleBFGSRun 2 UnexcitedMetric.objective :=
  UnexcitedMetric.run 1 1 (1 / 4) (1 / 4) (1 / 2) one_pos one_pos (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- The setting (lines 30-37), Theorem `R:thm:equiv` and the displays `disp/008`-`disp/013` of its
proof can have all their assumptions at once: $F(u,v)=u^2+|v|$, $x_*=0$, $b=4$, the bounds $R,G$
of `bounds_exist`, $\eta=1/8$ with constants $M,\theta$ of (IR), and two differentiable pairs on
that band with $T>0$, one with $N\ge0$ ($x=(0,1)$, $z=(0,-1)$) and one with $N<0$ ($x=(1,1)$,
$z=(1/2,1)$). -/
example : ∃ (F : Vec 2 → ℝ) (xstar : Vec 2) (b : ℝ) (K : Set (Vec 2)) (R G η M θ : ℝ),
    ConvexOn ℝ univ F ∧ (∀ x, F xstar ≤ F x) ∧ F xstar < b ∧ K = {x | F x ≤ b} ∧
      IsCompact K ∧ 0 < R ∧ 0 < G ∧ (∀ x ∈ K, ‖euclideanVector (x - xstar)‖ ≤ R) ∧
      (∀ x ∈ K, ∀ v : Vec 2, (∀ y, F x + dot v (y - x) ≤ F y) → ‖euclideanVector v‖ ≤ G) ∧
      IR F xstar K ∧ RS F xstar K ∧ 0 < η ∧ 0 < θ ∧ θ ≤ 1 / 2 ∧
      (∀ x g : Vec 2, x ∈ K → HasFDerivAt F (gradientFunctional g) x → F xstar + η ≤ F x →
        ∀ t : ℝ, 0 ≤ t → t ≤ θ →
          0 ≤ F (x - t • (x - xstar)) - F x + t * dot g (x - xstar) ∧
            F (x - t • (x - xstar)) - F x + t * dot g (x - xstar) ≤ M / 2 * t ^ 2) ∧
      (∃ x z g h : Vec 2, x ∈ K ∧ z ∈ K ∧ HasFDerivAt F (gradientFunctional g) x ∧
        HasFDerivAt F (gradientFunctional h) z ∧ F xstar + η ≤ F z ∧ F z ≤ F x ∧
        0 < dot (h - g) (z - x) ∧ 0 ≤ dot (h - g) (z - xstar)) ∧
      (∃ x z g h : Vec 2, x ∈ K ∧ z ∈ K ∧ HasFDerivAt F (gradientFunctional g) x ∧
        HasFDerivAt F (gradientFunctional h) z ∧ F xstar + η ≤ F z ∧ F z ≤ F x ∧
        0 < dot (h - g) (z - x) ∧ dot (h - g) (z - xstar) < 0) := by
  obtain ⟨hconv, hmin, -, hK, hF0, -, -⟩ := bench_facts
  have hinw := ((Article.Global.mixed_inward_condition UnexcitedMetric.objective
    (fun _ => rfl)).2.2 4 (by norm_num)).2
  have hb : UnexcitedMetric.objective 0 < 4 := by rw [hF0]; norm_num
  obtain ⟨R, G, hR, hG, hRK, hGK⟩ := bounds_exist hconv 0 hmin 4 hb _ rfl (hK 4)
  have hIR : IR UnexcitedMetric.objective 0 {x | UnexcitedMetric.objective x ≤ 4} :=
    (IR_iff_article _ _ _).mpr hinw
  have hRS := (equiv hconv 0 hmin 4 hb _ rfl (hK 4)).1.mpr hIR
  obtain ⟨M, θ, hθ, hθ', hband⟩ := hIR (1 / 8) (by norm_num)
  have hF : ∀ u v : ℝ, UnexcitedMetric.objective ![u, v] = u ^ 2 + |v| := fun u v => rfl
  have hgrad := fun (u v : ℝ) (hv : v ≠ 0) => ArticleGeometry.mixed_ridge_gradient (u := u) hv
  refine ⟨UnexcitedMetric.objective, 0, 4, _, R, G, 1 / 8, M, θ, hconv, hmin, hb, rfl, hK 4, hR,
    hG, hRK, hGK, hIR, hRS, by norm_num, hθ, hθ', hband, ?_, ?_⟩
  · refine ⟨![0, 1], ![0, -1], _, _, ?_, ?_, hgrad 0 1 one_ne_zero,
      hgrad 0 (-1) (by norm_num), ?_, ?_, ?_, ?_⟩
    · show UnexcitedMetric.objective ![0, 1] ≤ 4
      rw [hF]; norm_num
    · show UnexcitedMetric.objective ![0, -1] ≤ 4
      rw [hF]; norm_num
    · rw [hF0, hF]; norm_num
    · rw [hF, hF]; norm_num
    · simp [dot, Fin.sum_univ_two, Real.sign_neg, Real.sign_one]
      norm_num
    · simp [dot, Fin.sum_univ_two, Real.sign_neg, Real.sign_one]
  · refine ⟨![1, 1], ![1 / 2, 1], _, _, ?_, ?_, hgrad 1 1 one_ne_zero,
      hgrad (1 / 2) 1 one_ne_zero, ?_, ?_, ?_, ?_⟩
    · show UnexcitedMetric.objective ![1, 1] ≤ 4
      rw [hF]; norm_num
    · show UnexcitedMetric.objective ![1 / 2, 1] ≤ 4
      rw [hF]; norm_num
    · rw [hF0, hF]; norm_num
    · rw [hF, hF]; norm_num
    · simp [dot, Fin.sum_univ_two, Real.sign_one]
      norm_num
    · simp [dot, Fin.sum_univ_two, Real.sign_one]
      norm_num

/-- The displays `disp/014`-`disp/019` of the proof that (RS) implies (IR) can have all their
assumptions at once, in both cases $a>0$ and $a=0$: $F(u,v)=u^2+|v|$, $x_*=0$, $b=4$, the bounds
$R,G$ of `bounds_exist`, $\eta=1$, $\theta_\eta$ by its defining equation, $t=\theta_\eta$, a
constant $C$ of (RS) on the $\eta/2$-band, and the points $x=(1,1)$ ($a=2\theta_\eta>0$) and
$x=(0,1)$ ($a=0$) with $z=x-tr_x$. -/
example : ∃ (F : Vec 2 → ℝ) (xstar : Vec 2) (b : ℝ) (K : Set (Vec 2)) (R G η θ C : ℝ),
    ConvexOn ℝ univ F ∧ (∀ x, F xstar ≤ F x) ∧ F xstar < b ∧ K = {x | F x ≤ b} ∧
      IsCompact K ∧ 0 < R ∧ 0 < G ∧ (∀ x ∈ K, ‖euclideanVector (x - xstar)‖ ≤ R) ∧
      (∀ x ∈ K, ∀ v : Vec 2, (∀ y, F x + dot v (y - x) ≤ F y) → ‖euclideanVector v‖ ≤ G) ∧
      RS F xstar K ∧ 0 < η ∧ θ = min (1 / 2) (η / (4 * G * R)) ∧
      (∀ x z g h : Vec 2, x ∈ K → z ∈ K →
        HasFDerivAt F (gradientFunctional g) x → HasFDerivAt F (gradientFunctional h) z →
        F xstar + η / 2 ≤ F z → F z ≤ F x → 0 < dot (h - g) (z - x) →
        (dot (h - g) (z - xstar)) ^ 2 ≤ C * dot (h - g) (z - x)) ∧
      (∃ (t : ℝ) (x z g h : Vec 2), x ∈ K ∧ F xstar + η ≤ F x ∧ 0 ≤ t ∧ t ≤ θ ∧
        z = x - t • (x - xstar) ∧ HasFDerivAt F (gradientFunctional g) x ∧
        HasFDerivAt F (gradientFunctional h) z ∧ 0 < dot (g - h) (x - xstar)) ∧
      (∃ (t : ℝ) (x z g h : Vec 2), x ∈ K ∧ F xstar + η ≤ F x ∧ 0 ≤ t ∧ t ≤ θ ∧
        z = x - t • (x - xstar) ∧ HasFDerivAt F (gradientFunctional g) x ∧
        HasFDerivAt F (gradientFunctional h) z ∧ dot (g - h) (x - xstar) = 0) := by
  obtain ⟨hconv, hmin, -, hK, hF0, -, -⟩ := bench_facts
  have hinw := ((Article.Global.mixed_inward_condition UnexcitedMetric.objective
    (fun _ => rfl)).2.2 4 (by norm_num)).2
  have hb : UnexcitedMetric.objective 0 < 4 := by rw [hF0]; norm_num
  obtain ⟨R, G, hR, hG, hRK, hGK⟩ := bounds_exist hconv 0 hmin 4 hb _ rfl (hK 4)
  have hRS := (equiv hconv 0 hmin 4 hb _ rfl (hK 4)).1.mpr ((IR_iff_article _ _ _).mpr hinw)
  obtain ⟨C, hC⟩ := hRS (1 / 2) (by norm_num)
  set θ := min (1 / 2) (1 / (4 * G * R)) with hθ
  have hθ0 : 0 < θ := lt_min (by norm_num) (by positivity)
  have hθ1 : θ ≤ 1 / 2 := min_le_left _ _
  have h1θ : 0 < 1 - θ := by linarith
  have hF : ∀ u v : ℝ, UnexcitedMetric.objective ![u, v] = u ^ 2 + |v| := fun u v => rfl
  have hgrad := fun (u v : ℝ) (hv : v ≠ 0) => ArticleGeometry.mixed_ridge_gradient (u := u) hv
  refine ⟨UnexcitedMetric.objective, 0, 4, _, R, G, 1, θ, C, hconv, hmin, hb, rfl, hK 4, hR, hG,
    hRK, hGK, hRS, one_pos, rfl, hC,
    ⟨θ, ![1, 1], ![1 - θ, 1 - θ], _, _, ?_, ?_, hθ0.le, le_rfl, ?_, hgrad 1 1 one_ne_zero,
      hgrad (1 - θ) (1 - θ) h1θ.ne', ?_⟩,
    ⟨θ, ![0, 1], ![0, 1 - θ], _, _, ?_, ?_, hθ0.le, le_rfl, ?_, hgrad 0 1 one_ne_zero,
      hgrad 0 (1 - θ) h1θ.ne', ?_⟩⟩
  · show UnexcitedMetric.objective ![1, 1] ≤ 4
    rw [hF]; norm_num
  · rw [hF0, hF]; norm_num
  · ext i; fin_cases i <;> simp
  · simp [dot, Fin.sum_univ_two, Real.sign_one, Real.sign_of_pos h1θ]
    linarith
  · show UnexcitedMetric.objective ![0, 1] ≤ 4
    rw [hF]; norm_num
  · rw [hF0, hF]; norm_num
  · ext i; fin_cases i <;> simp
  · simp [dot, Fin.sum_univ_two, Real.sign_one, Real.sign_of_pos h1θ]

/-- Display `disp/023` can have all its assumptions at once: $F(u,v)=u^2+|v|$, $x_*=0$, $b=4$,
$\eta=1$ with a constant $C$ of (RS), $r=(1,1)$ and $t=1/4$ (outer point $(5/4,5/4)$ in $K$, inner
point $(3/4,3/4)$ on the band, all three points differentiable). -/
example : ∃ (F : Vec 2 → ℝ) (xstar : Vec 2) (b : ℝ) (K : Set (Vec 2)) (η C : ℝ) (r : Vec 2)
    (t : ℝ) (go gm gi : Vec 2),
    ConvexOn ℝ univ F ∧ (∀ x, F xstar ≤ F x) ∧ F xstar < b ∧ K = {x | F x ≤ b} ∧
      IsCompact K ∧ RS F xstar K ∧ 0 < η ∧
      (∀ x z g h : Vec 2, x ∈ K → z ∈ K →
        HasFDerivAt F (gradientFunctional g) x → HasFDerivAt F (gradientFunctional h) z →
        F xstar + η ≤ F z → F z ≤ F x → 0 < dot (h - g) (z - x) →
        (dot (h - g) (z - xstar)) ^ 2 ≤ C * dot (h - g) (z - x)) ∧
      0 ≤ t ∧ t ≤ 1 / 2 ∧ F (xstar + (1 + t) • r) ≤ b ∧ F xstar + η ≤ F (xstar + (1 - t) • r) ∧
      HasFDerivAt F (gradientFunctional go) (xstar + (1 + t) • r) ∧
      HasFDerivAt F (gradientFunctional gm) (xstar + r) ∧
      HasFDerivAt F (gradientFunctional gi) (xstar + (1 - t) • r) := by
  obtain ⟨hconv, hmin, -, hK, hF0, -, -⟩ := bench_facts
  have hinw := ((Article.Global.mixed_inward_condition UnexcitedMetric.objective
    (fun _ => rfl)).2.2 4 (by norm_num)).2
  have hb : UnexcitedMetric.objective 0 < 4 := by rw [hF0]; norm_num
  have hRS := (equiv hconv 0 hmin 4 hb _ rfl (hK 4)).1.mpr ((IR_iff_article _ _ _).mpr hinw)
  obtain ⟨C, hC⟩ := hRS 1 one_pos
  have hF : ∀ u v : ℝ, UnexcitedMetric.objective ![u, v] = u ^ 2 + |v| := fun u v => rfl
  have hgrad := fun (u v : ℝ) (hv : v ≠ 0) => ArticleGeometry.mixed_ridge_gradient (u := u) hv
  have e1 : (0 : Vec 2) + (1 + 1 / 4 : ℝ) • ![1, 1] = ![5 / 4, 5 / 4] := by
    ext i; fin_cases i <;> norm_num
  have e2 : (0 : Vec 2) + ![1, 1] = ![1, 1] := zero_add _
  have e3 : (0 : Vec 2) + (1 - 1 / 4 : ℝ) • ![1, 1] = ![3 / 4, 3 / 4] := by
    ext i; fin_cases i <;> norm_num
  refine ⟨UnexcitedMetric.objective, 0, 4, _, 1, C, ![1, 1], 1 / 4,
    ![2 * (5 / 4), Real.sign (5 / 4)], ![2 * 1, Real.sign 1], ![2 * (3 / 4), Real.sign (3 / 4)],
    hconv, hmin, hb, rfl, hK 4, hRS,
    one_pos, hC, by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e1, hF, abs_of_pos (by norm_num : (0 : ℝ) < 5 / 4)]; norm_num
  · rw [e3, hF, hF0, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 4)]; norm_num
  · rw [e1]; exact hgrad (5 / 4) (5 / 4) (by norm_num)
  · rw [e2]; exact hgrad 1 1 one_ne_zero
  · rw [e3]; exact hgrad (3 / 4) (3 / 4) (by norm_num)

/-- Theorem `R:thm:plq`, `plq_gradient_agreement` and display `disp/040` can have all their
assumptions at once, and low-starting admissible runs exist, so the conclusion of the theorem is
not vacuous: $F(x)=|x|$ on $\R$, $x_*=0$, $N=\R$, the cells $\{x\le0\}$, $\{x\ge0\}$ with the
linear extensions $-x$, $x$ ($V_i=\R$), $R=1$, $B=B_1(0)$, $L=0$, the differentiable point
$x=-1/2$ (gradient $-1$) of the first cell, and for every $\varepsilon>0$ a tail of
`Article.Global.absRun` starting below $\varepsilon$. -/
example : ∃ (F : Vec 1 → ℝ) (xstar : Vec 1) (N : Set (Vec 1)) (a : Fin 2 → Fin 1 → Vec 1)
    (b : Fin 2 → Fin 1 → ℝ) (P V : Fin 2 → Set (Vec 1)) (f : Fin 2 → Vec 1 → ℝ) (R : ℝ)
    (B : Set (Vec 1)) (L : ℝ) (x g : Vec 1),
    ConvexOn ℝ univ F ∧ (∀ x, F xstar ≤ F x) ∧ (∀ x, F x = F xstar → x = xstar) ∧
      N ∈ 𝓝 xstar ∧ (∀ i, P i = {x | ∀ j, dot (a i j) x ≤ b i j}) ∧
      (∀ i, (interior (P i)).Nonempty) ∧ N ⊆ ⋃ i, P i ∧
      (∀ i, ∀ x ∈ N ∩ P i, F x = f i x) ∧ (∀ i, IsOpen (V i)) ∧ (∀ i, N ∩ P i ⊆ V i) ∧
      (∀ i, DifferentiableOn ℝ (f i) (V i) ∧
        ∃ L : NNReal, LipschitzOnWith L (fderiv ℝ (f i)) (V i)) ∧
      0 < R ∧ B = {x | ‖euclideanVector (x - xstar)‖ < R} ∧ B ⊆ N ∧
      (∀ i, xstar ∈ P i → B ⊆ V i) ∧ (∀ i, (B ∩ P i).Nonempty → xstar ∈ P i) ∧ 0 ≤ L ∧
      (∀ i, xstar ∈ P i → ∀ y ∈ B, ∀ y' ∈ B,
        ‖euclideanVector (coordinateGradient (f i) y - coordinateGradient (f i) y')‖ ≤
          L * ‖euclideanVector (y - y')‖) ∧
      x ∈ B ∧ HasFDerivAt F (gradientFunctional g) x ∧ x ∈ P 0 ∧ x ∈ interior N ∧
      ∀ ε : ℝ, 0 < ε → ∃ run : AdmissibleBFGSRun 1 F, F (run.x 0) ≤ F xstar + ε := by
  set sg : Fin 2 → ℝ := ![1, -1] with hsg
  have hdot : ∀ (u : ℝ) (x : Vec 1), dot (fun _ : Fin 1 => u) x = u * x 0 := by
    intro u x; simp [dot]
  have h0P : ∀ i, (0 : Vec 1) ∈ {x : Vec 1 | ∀ j : Fin 1,
      dot ((fun i _ => fun _ => sg i : Fin 2 → Fin 1 → Vec 1) i j) x ≤ 0} := by
    intro i j
    simp [dot]
  have hlin : ∀ i, (fun x : Vec 1 => dot (fun _ : Fin 1 => -sg i) x) =
      ⇑(gradientFunctional (fun _ : Fin 1 => -sg i)) :=
    fun i => funext fun x => (gradientFunctional_apply _ x).symm
  have hx : HasFDerivAt (fun x : Vec 1 => |x 0|) (gradientFunctional (OneDimensional.embed (-1)))
      (OneDimensional.embed (-1 / 2)) :=
    ScalarCounterexamples.coordinate_hasGradient (f := fun t => |t|)
      (hasDerivAt_abs_neg (by norm_num))
  refine ⟨fun x => |x 0|, 0, univ, fun i _ => fun _ => sg i, fun _ _ => 0,
    fun i => {x | ∀ j : Fin 1, dot ((fun i _ => fun _ => sg i : Fin 2 → Fin 1 → Vec 1) i j) x ≤ 0},
    fun _ => univ, fun i x => dot (fun _ => -sg i) x, 1, {x | ‖euclideanVector (x - 0)‖ < 1}, 0,
    OneDimensional.embed (-1 / 2), OneDimensional.embed (-1), Article.Global.abs_coord_convex,
    fun x => by simp, fun x hx => ?_, univ_mem, fun _ => rfl, fun i => ?_, fun x _ => ?_,
    fun i x hx => ?_, fun _ => isOpen_univ, fun _ _ _ => mem_univ _, fun i => ?_, one_pos, rfl,
    subset_univ _, fun _ _ _ _ => mem_univ _, fun i _ => h0P i, le_rfl, ?_, ?_, hx, ?_,
    by simp, fun ε hε => ?_⟩
  · ext i; fin_cases i; simpa using hx
  · have hopen : IsOpen {x : Vec 1 | sg i * x 0 < 0} :=
      isOpen_lt (continuous_const.mul (continuous_apply 0)) continuous_const
    refine ⟨fun _ => -sg i, ?_⟩
    rw [mem_interior]
    refine ⟨{x : Vec 1 | sg i * x 0 < 0}, ?_, hopen, ?_⟩
    · intro x hx j
      show dot (fun _ => sg i) x ≤ 0
      rw [hdot]
      exact (mem_setOf_eq ▸ hx).le
    · show sg i * -sg i < 0
      fin_cases i <;> norm_num [hsg]
  · rcases le_or_lt (x 0) 0 with h | h
    · refine mem_iUnion.mpr ⟨0, fun j => ?_⟩
      show dot (fun _ => sg 0) x ≤ 0
      rw [hdot]
      simp [hsg, h]
    · refine mem_iUnion.mpr ⟨1, fun j => ?_⟩
      show dot (fun _ => sg 1) x ≤ 0
      rw [hdot]
      simp [hsg]
      linarith
  · have h : dot (fun _ => sg i) x ≤ 0 := hx.2 0
    rw [hdot] at h
    show |x 0| = dot (fun _ => -sg i) x
    rw [hdot]
    fin_cases i
    · have h' : x 0 ≤ 0 := by simpa [hsg] using h
      simp [hsg, abs_of_nonpos h']
    · have h' : 0 ≤ x 0 := by simp [hsg] at h; linarith
      simp [hsg, abs_of_nonneg h']
  · show DifferentiableOn ℝ (fun x => dot (fun _ : Fin 1 => -sg i) x) univ ∧
      ∃ L : NNReal, LipschitzOnWith L (fderiv ℝ (fun x => dot (fun _ : Fin 1 => -sg i) x)) univ
    rw [hlin i]
    refine ⟨(gradientFunctional (fun _ : Fin 1 => -sg i)).differentiable.differentiableOn, 0, ?_⟩
    rw [show fderiv ℝ ⇑(gradientFunctional (fun _ : Fin 1 => -sg i)) =
      fun _ => gradientFunctional (fun _ : Fin 1 => -sg i) from
        funext fun _ => (gradientFunctional (fun _ : Fin 1 => -sg i)).hasFDerivAt.fderiv]
    exact (LipschitzWith.const _).lipschitzOnWith
  · intro i _ y _ y' _
    rw [Article.Local.coordinateGradient_dot, Article.Local.coordinateGradient_dot, sub_self,
      show euclideanVector (0 : Vec 1) = 0 from rfl, norm_zero, zero_mul]
  · show ‖euclideanVector (OneDimensional.embed (-1 / 2) - 0)‖ < 1
    rw [Article.Global.norm_euclideanVector, Real.sqrt_lt' one_pos]
    simp only [sqNorm, Fin.sum_univ_one, Pi.sub_apply, Pi.zero_apply, sub_zero,
      OneDimensional.embed_apply]
    norm_num
  · intro j
    show dot (fun _ => sg 0) (OneDimensional.embed (-1 / 2)) ≤ 0
    rw [hdot]
    simp [hsg]
    norm_num
  · obtain ⟨R', hR'⟩ := exists_low_run (Article.Global.absRun _ fun _ => rfl)
      (absRun_values (fun _ => rfl)) ε hε
    exact ⟨R', by simpa using hR'⟩

/-- Display `disp/043` (and `mixed_powers_covered`) can have all its assumptions at once, with an
admissible run starting in $K$: $F(u,v)=u^2+|v|$, $x_*=0$, $\psi(z)=z_0^2$, one gauge
$\gamma=|\cdot|$ on $\R^1$, $A=(0\ 1)$, $p=1$, the run `benchRun` and $b=F(x_0)$. -/
example : ∃ (F ψ : Vec 2 → ℝ) (γ : Fin 1 → Vec 1 → ℝ) (A : Fin 1 → Matrix (Fin 1) (Fin 2) ℝ)
    (p : Fin 1 → ℝ) (b : ℝ) (run : AdmissibleBFGSRun 2 F),
    ConvexOn ℝ univ F ∧ (∀ x, F 0 ≤ F x) ∧ F 0 < b ∧ IsCompact {x | F x ≤ b} ∧
      ConvexOn ℝ univ ψ ∧ CenteredSmoothSublinear.LocallyC11On univ ψ ∧
      (∀ j, Sublinear (γ j)) ∧ (∀ j x, 0 ≤ γ j x) ∧ (∀ j, 1 ≤ p j) ∧
      (∀ z, F (0 + z) = ψ z + ∑ j, γ j (A j *ᵥ z) ^ p j) ∧ F (run.x 0) ≤ b := by
  obtain ⟨hconv, hmin, -, hK, hψ, hψ11, -, -, -⟩ :=
    Article.Global.mixed_hypotheses UnexcitedMetric.objective (fun _ => rfl)
  have hA : ∀ z : Vec 2, (!![0, 1] : Matrix (Fin 1) (Fin 2) ℝ) *ᵥ z = fun _ => z 1 := by
    intro z; ext i; fin_cases i; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  refine ⟨UnexcitedMetric.objective, fun z => z 0 ^ 2, fun _ v => |v 0|, fun _ => !![0, 1],
    fun _ => 1, _, benchRun, hconv, hmin, Article.Global.initial_value_gt benchRun 0 hmin, hK _,
    hψ, hψ11, fun _ => (sublinear_iff _).mpr ⟨Article.Global.abs_coord_convex, fun t ht x => by
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg ht]⟩,
    fun _ _ => abs_nonneg _, fun _ => le_rfl, fun z => ?_, le_rfl⟩
  simp only [zero_add, hA, Real.rpow_one, Finset.univ_unique, Finset.sum_singleton]
  rfl

/-- The theorems of Sections 4.6.2-4.6.3 (`l1_covered`, `generalized_l1_covered`, `hinge_covered`,
`quantile_covered`, `euclidean_residuals_local_condition`; `affine_residual_local` and
`euclidean_residual_local` have no standing assumptions) can have all their assumptions at once,
and low-starting runs exist: the benchmark $F(u,v)=u^2+|v|$ is $\psi+|a^Tx-b|$,
$\psi+\|Dx-c\|_1$, $\psi+\max\{0,v\}+\max\{0,-v\}$, $\psi+\rho_{1/2}(v)+\rho_{1/2}(v)$ and
$\psi+\|Ax-b\|_2$, with $\psi(u,v)=u^2$ convex and $C^2$ (so locally $C^{1,1}$), $a=(0,1)$,
$D=A=(0\ 1)$, $b=c=0$; its
minimizer $0$ is unique; and tails of `benchRun` start below every $\varepsilon>0$. -/
example : ∃ (F ψ : Vec 2 → ℝ),
    ConvexOn ℝ univ ψ ∧ CenteredSmoothSublinear.LocallyC11On univ ψ ∧ (∀ x, F 0 ≤ F x) ∧
      (∀ x, F x = F 0 → x = 0) ∧
      (∀ x, F x = ψ x + ∑ i : Unit, |dot ((fun _ => ![0, 1]) i) x - (fun _ => (0 : ℝ)) i|) ∧
      (∀ x, F x = ψ x + ∑ i, |((!![0, 1] : Matrix (Fin 1) (Fin 2) ℝ) *ᵥ x - 0) i|) ∧
      (∀ x, F x = ψ x + ∑ i : Fin 2,
          max 0 (dot (![![0, 1], ![0, -1]] i) x - (fun _ => (0 : ℝ)) i)) ∧
      (∀ x, F x = ψ x + ∑ i : Fin 2,
        ((fun _ => (1 / 2 : ℝ)) i * max (dot ((fun _ => ![0, 1]) i) x - (fun _ => (0 : ℝ)) i) 0 +
          (1 - (fun _ => (1 / 2 : ℝ)) i) *
            max (-(dot ((fun _ => ![0, 1]) i) x - (fun _ => (0 : ℝ)) i)) 0)) ∧
      (∀ x, F x = ψ x + ∑ j : Unit, ‖euclideanVector
        ((fun _ => (!![0, 1] : Matrix (Fin 1) (Fin 2) ℝ)) j *ᵥ x - (fun _ => (0 : Vec 1)) j)‖) ∧
      ∀ ε : ℝ, 0 < ε → ∃ run : AdmissibleBFGSRun 2 F, F (run.x 0) ≤ F 0 + ε := by
  obtain ⟨-, hmin, huniq, -, hF0, hF, hrun⟩ := bench_facts
  obtain ⟨-, -, -, -, hψ, -, -, -, -⟩ :=
    Article.Global.mixed_hypotheses UnexcitedMetric.objective (fun _ => rfl)
  have hd : ∀ x : Vec 2, dot ![0, 1] x = x 1 := fun x => by simp [dot, Fin.sum_univ_two]
  have hd' : ∀ x : Vec 2, dot ![0, -1] x = -x 1 := fun x => by simp [dot, Fin.sum_univ_two]
  have hA : ∀ (x : Vec 2) (i : Fin 1), ((!![0, 1] : Matrix (Fin 1) (Fin 2) ℝ) *ᵥ x) i = x 1 :=
    fun x i => by fin_cases i; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  refine ⟨UnexcitedMetric.objective, fun x => x 0 ^ 2, hψ,
    locallyC11_of_contDiff_two (by fun_prop), hmin, huniq,
    fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_, fun ε hε => ?_⟩
  · rw [hF]
    simp only [Finset.univ_unique, Finset.sum_singleton, hd, sub_zero]
  · rw [hF]
    simp only [Finset.univ_unique, Finset.sum_singleton, Fin.sum_univ_one, Pi.sub_apply,
      Pi.zero_apply, sub_zero, hA]
  · rw [hF]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, hd,
      hd', sub_zero]
    rw [max_comm 0 (x 1), max_comm 0 (-x 1), max_zero_add_max_neg_zero_eq_abs_self]
  · rw [hF]
    simp only [Fin.sum_univ_two, hd, sub_zero]
    rw [← max_zero_add_max_neg_zero_eq_abs_self (x 1)]
    ring
  · rw [hF, Finset.univ_unique, Finset.sum_singleton, Article.Global.norm_euclideanVector]
    simp only [sqNorm, Fin.sum_univ_one, Pi.sub_apply, Pi.zero_apply, sub_zero, hA,
      Real.sqrt_sq_eq_abs]
  · obtain ⟨R', hR'⟩ := exists_low_run benchRun (hrun benchRun) ε hε
    exact ⟨R', by rw [hF0]; exact hR'⟩

/-- The assumptions of `fused_l1_covered` can hold, and low-starting runs exist: on $\R^2$,
$F(x)=(x_0+x_1)^2+|x_1-x_0|$ ($\psi(x)=(x_0+x_1)^2$, $w=1$) is the benchmark composed with the
invertible map $\mathcal Ax=(x_0+x_1,x_1-x_0)$ (`AffineWhitening.objective`), with unique
minimizer $0$; the whitened benchmark run (`AffineWhitening.run`) has the benchmark's values,
which tend to $0$. -/
example : ∃ (ψ F : Vec (1 + 1) → ℝ), ConvexOn ℝ univ ψ ∧
    CenteredSmoothSublinear.LocallyC11On univ ψ ∧
    (∀ x, F x = ψ x + 1 * ∑ i : Fin 1, |x i.succ - x i.castSucc|) ∧ (∀ x, F 0 ≤ F x) ∧
    (∀ x, F x = F 0 → x = 0) ∧
    ∀ ε : ℝ, 0 < ε → ∃ run : AdmissibleBFGSRun (1 + 1) F, F (run.x 0) ≤ F 0 + ε := by
  obtain ⟨-, hmin, huniq, -, hF0, hF, hrun⟩ := bench_facts
  set A : Mat 2 := !![1, 1; -1, 1] with hA
  have hdet : A.det ≠ 0 := by rw [hA, Matrix.det_fin_two_of]; norm_num
  have hAx : ∀ x : Vec 2, (A *ᵥ x) 0 = x 0 + x 1 ∧ (A *ᵥ x) 1 = x 1 - x 0 := fun x => by
    refine ⟨by simp [hA, Matrix.mulVec, dotProduct, Fin.sum_univ_two], ?_⟩
    simp [hA, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  have hψ : ConvexOn ℝ univ (fun x : Vec 2 => (x 0 + x 1) ^ 2) :=
    (Article.Local.sqNorm_affine_convex (!![1, 1] : Matrix (Fin 1) (Fin 2) ℝ) 0).congr
      (fun x _ => by simp [sqNorm, Matrix.mulVec, dotProduct, Fin.sum_univ_two])
  have hval : ∀ k, AffineWhitening.objective A UnexcitedMetric.objective
      ((AffineWhitening.run A hdet benchRun).x k) = UnexcitedMetric.objective (benchRun.x k) :=
    fun k => by
      rw [AffineWhitening.run_x]
      show UnexcitedMetric.objective (A *ᵥ AffineWhitening.point A (benchRun.x k)) = _
      rw [AffineWhitening.map_point A hdet]
  have h0 : AffineWhitening.objective A UnexcitedMetric.objective 0 = 0 := by
    show UnexcitedMetric.objective (A *ᵥ 0) = 0
    rw [Matrix.mulVec_zero, hF0]
  refine ⟨fun x => (x 0 + x 1) ^ 2, AffineWhitening.objective A UnexcitedMetric.objective, hψ,
    locallyC11_of_contDiff_two (by fun_prop), fun x => ?_, fun x => ?_, fun x hx => ?_,
    fun ε hε => ?_⟩
  · show UnexcitedMetric.objective (A *ᵥ x) = _
    rw [hF, (hAx x).1, (hAx x).2]
    simp
  · rw [h0]
    exact hF0 ▸ hmin (A *ᵥ x)
  · rw [h0] at hx
    have h1 : A *ᵥ x = 0 := huniq _ (hx.trans hF0.symm)
    rw [← AffineWhitening.point_map A hdet x, h1]
    simp [AffineWhitening.point]
  · obtain ⟨R', hR'⟩ := exists_low_run (AffineWhitening.run A hdet benchRun)
      (by simpa only [hval] using hrun benchRun) ε hε
    exact ⟨R', by rw [h0]; exact hR'⟩

/-- Display `disp/044` (with `ray_active_agreement`, `ray_derivative_selection`,
`finite_max_necessity`, `finite_max_quadratic_iff`) can have all its assumptions at once, and
low-starting runs exist: $F(x)=|x|=\max\{x,-x\}$ on $\R$, $x_*=0$, $U=\R$ (the only tie is at
$0$); tails of `Article.Global.absRun`. -/
example : ∃ (hne : (Finset.univ : Finset (Fin 2)).Nonempty) (F : Vec 1 → ℝ)
    (f : Fin 2 → Vec 1 → ℝ),
    (∀ i, ContDiffOn ℝ 2 (f i) univ) ∧
      (∀ w ∈ (univ : Set (Vec 1)), F w = Finset.univ.sup' hne fun i => f i w) ∧
      ConvexOn ℝ univ F ∧ (∀ x, F 0 ≤ F x) ∧ (∀ x, F x = F 0 → x = 0) ∧
      (∀ i, ConvexOn ℝ univ (f i)) ∧
      (∀ w ∈ (univ : Set (Vec 1)), ∀ i j, f i w = F w → f j w = F w →
        dot (coordinateGradient (f i) w - coordinateGradient (f j) w) (w - 0) = 0) ∧
      ∀ ε : ℝ, 0 < ε → ∃ run : AdmissibleBFGSRun 1 F, F (run.x 0) ≤ F 0 + ε := by
  set sg : Fin 2 → ℝ := ![1, -1] with hsg
  have hdot : ∀ (u : ℝ) (x : Vec 1), dot (fun _ : Fin 1 => u) x = u * x 0 := by
    intro u x; simp [dot]
  have hlin : ∀ i, (fun x : Vec 1 => dot (fun _ : Fin 1 => sg i) x) =
      ⇑(gradientFunctional (fun _ : Fin 1 => sg i)) :=
    fun i => funext fun x => (gradientFunctional_apply _ x).symm
  have hsup : ∀ w : Vec 1, |w 0| = Finset.univ.sup' Finset.univ_nonempty
      (fun i => dot (fun _ : Fin 1 => sg i) w) := by
    intro w
    apply le_antisymm
    · rcases abs_choice (w 0) with h | h
      · exact Finset.le_sup'_of_le _ (Finset.mem_univ 0) (by rw [hdot, h]; simp [hsg])
      · exact Finset.le_sup'_of_le _ (Finset.mem_univ 1) (by rw [hdot, h]; simp [hsg])
    · refine Finset.sup'_le _ _ fun i _ => ?_
      rw [hdot]
      fin_cases i
      · simpa [hsg] using le_abs_self (w 0)
      · simpa [hsg] using neg_le_abs (w 0)
  refine ⟨Finset.univ_nonempty, fun x => |x 0|, fun i x => dot (fun _ => sg i) x, fun i => ?_,
    fun w _ => hsup w, Article.Global.abs_coord_convex, fun x => by simp, fun x hx => ?_,
    fun i => ?_, fun w _ i j hi hj => ?_, fun ε hε => ?_⟩
  · show ContDiffOn ℝ 2 (fun x => dot (fun _ : Fin 1 => sg i) x) univ
    rw [hlin i]
    exact (gradientFunctional (fun _ : Fin 1 => sg i)).contDiff.contDiffOn
  · ext i; fin_cases i; simpa using hx
  · show ConvexOn ℝ univ (fun x => dot (fun _ : Fin 1 => sg i) x)
    rw [hlin i]
    exact (gradientFunctional (fun _ : Fin 1 => sg i)).toLinearMap.convexOn convex_univ
  · rw [Article.Local.coordinateGradient_dot, Article.Local.coordinateGradient_dot, sub_zero]
    have h := hi.trans hj.symm
    simp only [hdot] at h
    rw [show (fun _ : Fin 1 => sg i) - (fun _ => sg j) = fun _ => sg i - sg j from rfl, hdot]
    linarith
  · obtain ⟨R', hR'⟩ := exists_low_run (Article.Global.absRun _ fun _ => rfl)
      (absRun_values (fun _ => rfl)) ε hε
    exact ⟨R', by simpa using hR'⟩

/-- The assumptions of the homogeneous-intercept statements (`homogeneous_intercept_zero`,
`euler_identity`, `compact_positive_degree`, `midpoint_bound` without its contradiction
hypothesis, `compact_homogeneous_optimizer`, `compact_homogeneous_intercept`) can hold at once:
$F(x)=|x|$ on $\R$, degree $p=1$, $b=1$, $z=x_*=0$ and the differentiable point $x=1$ with
gradient $1$. -/
example : ∃ (F : Vec 1 → ℝ) (p b : ℝ) (z xstar x g : Vec 1),
    1 ≤ 1 ∧ ConvexOn ℝ univ F ∧ (∀ x, 0 ≤ F x) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ x, F (t • x) = t ^ p * F x) ∧ Homogeneous.PositiveDegreeOne F ∧
      IsCompact {x | F x ≤ b} ∧ F z < b ∧ (∀ x, F xstar ≤ F x) ∧
      HasFDerivAt F (gradientFunctional g) x := by
  have hmin : ∀ x : Vec 1, |(0 : Vec 1) 0| ≤ |x 0| := fun x => by simp
  have huniq : ∀ x : Vec 1, |x 0| = |(0 : Vec 1) 0| → x = 0 := fun x hx => by
    ext i; fin_cases i; simpa using hx
  refine ⟨fun x => |x 0|, 1, 1, 0, 0, OneDimensional.embed 1, OneDimensional.embed 1, le_rfl,
    Article.Global.abs_coord_convex, fun x => abs_nonneg _, fun t ht x => ?_, fun t ht x => ?_,
    Localization.sublevel_compact Article.Global.abs_coord_convex 0 hmin huniq 1, by simp, hmin,
    ScalarCounterexamples.coordinate_hasGradient (f := fun t => |t|)
      (hasDerivAt_abs_pos (by norm_num))⟩
  · simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg ht, Real.rpow_one]
  · simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg ht]

/-- The standing assumptions of the four-piece statements can hold: $\delta$, $a$, $\mathcal L$ by
their defining equations and $c_1=1/4$, $c_2=1/2$; an admissible run with these constants exists
(`fourPiece_failure_run`). -/
example : ∃ (δ a : ℝ) (L : Mat 2) (c₁ c₂ : ℝ), δ = SeedOrbit.seedC - 16 * SeedOrbit.seedD - 1 ∧
    a = 25 / (4 * δ) ∧ L = !![1, 0; 0, 16 / 5] ∧ 0 < c₁ ∧ c₁ ≤ 1 / 3 ∧ c₁ < c₂ ∧ c₂ < 1 ∧
    Nonempty (AdmissibleBFGSRun 2 ReconstructedFourPiece.objective) := by
  obtain ⟨R, -⟩ := fourPiece_failure_run _ _ _ rfl rfl rfl (1 / 4) (1 / 2) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact ⟨_, _, _, 1 / 4, 1 / 2, rfl, rfl, rfl, by norm_num, by norm_num, by norm_num, by norm_num,
    ⟨R⟩⟩

/-- `euclidean_norm_recovered` is not vacuous: for $n=1$ the Euclidean norm is $|x|$, and
`Article.Global.absRun` is an admissible run on it. -/
example : 1 ≤ 1 ∧ Nonempty (AdmissibleBFGSRun 1 (fun x : Vec 1 => ‖euclideanVector x‖)) :=
  ⟨le_rfl, ⟨Article.Global.absRun _ fun x => by
    rw [Article.Global.norm_euclideanVector]
    simp [sqNorm, Real.sqrt_sq_eq_abs]⟩⟩

/-- The coordinate discriminant of the nuclear norm is even. -/
theorem nuclear_discr_neg (y : Vec 3) :
    NuclearSymmetric2.discr (-y) = NuclearSymmetric2.discr y := by
  simp only [NuclearSymmetric2.discr, Pi.neg_apply]
  ring

/-- The nuclear norm is even. -/
theorem nuclear_neg (y : Vec 3) :
    NuclearSymmetric2.nuclearCoords (-y) = NuclearSymmetric2.nuclearCoords y := by
  rw [NuclearSymmetric2.nuclearCoords_eq, NuclearSymmetric2.nuclearCoords_eq, nuclear_discr_neg]
  simp only [Pi.neg_apply]
  rw [← neg_add, abs_neg]

/-- The nuclear norm of symmetric $2\times2$ matrices (coordinates
`NuclearSymmetric2.nuclearCoords`) is differentiable off the cone $(x_0+x_2)^2=$ `discr` $x$ of
singular matrices: there one of the two branches $|\operatorname{tr}|$, $\sqrt{\texttt{discr}}$ of
`NuclearSymmetric2.nuclearCoords_eq` is strictly active. -/
theorem nuclear_differentiableAt {x : Vec 3}
    (hx : (x 0 + x 2) ^ 2 ≠ NuclearSymmetric2.discr x) :
    DifferentiableAt ℝ NuclearSymmetric2.nuclearCoords x := by
  have hD := NuclearSymmetric2.discr_nonneg x
  have hne : |x 0 + x 2| ≠ Real.sqrt (NuclearSymmetric2.discr x) := by
    intro h
    apply hx
    rw [← sq_abs, h, Real.sq_sqrt hD]
  rcases lt_or_gt_of_ne hne with h | h
  · exact (NuclearSymmetric2.nuclearCoords_hasGradient_indef h).differentiableAt
  · rcases le_or_lt 0 (x 0 + x 2) with htr | htr
    · rw [abs_of_nonneg htr] at h
      exact (NuclearSymmetric2.nuclearCoords_hasGradient_pos h).differentiableAt
    · have hneg : Real.sqrt (NuclearSymmetric2.discr (-x)) < (-x) 0 + (-x) 2 := by
        rw [nuclear_discr_neg, abs_of_neg htr] at *
        simp only [Pi.neg_apply]
        linarith
      have hd := (NuclearSymmetric2.nuclearCoords_hasGradient_pos hneg).differentiableAt
      have hcomp : DifferentiableAt ℝ (fun y => NuclearSymmetric2.nuclearCoords (-y)) x :=
        hd.comp x differentiableAt_id.neg
      simpa only [nuclear_neg] using hcomp

/-- On the cone $(x_0+x_2)^2=$ `discr` $x$ (singular matrices, including $0$) the nuclear norm is
not differentiable: along $e=(1,0,1)$ (the identity matrix) it is $s\mapsto\max\{|c+2s|,|c|\}$,
$c=x_0+x_2$, which has a local minimum at $0$ and grows like $2|s|$ on one side. -/
theorem nuclear_not_differentiableAt {x : Vec 3}
    (hx : (x 0 + x 2) ^ 2 = NuclearSymmetric2.discr x) :
    ¬ DifferentiableAt ℝ NuclearSymmetric2.nuclearCoords x := by
  intro hdiff
  have hN : Real.sqrt (NuclearSymmetric2.discr x) = |x 0 + x 2| := by
    rw [← hx, Real.sqrt_sq_eq_abs]
  have hφs : ∀ s : ℝ, NuclearSymmetric2.nuclearCoords (x + s • ![1, 0, 1]) =
      max |x 0 + x 2 + 2 * s| |x 0 + x 2| := by
    intro s
    rw [NuclearSymmetric2.nuclearCoords_eq]
    have h1 : NuclearSymmetric2.discr (x + s • ![1, 0, 1]) = NuclearSymmetric2.discr x := by
      simp only [NuclearSymmetric2.discr, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons]
      ring
    rw [h1, hN]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    ring_nf
  have hline : HasDerivAt (fun s : ℝ => x + s • (![1, 0, 1] : Vec 3)) ![1, 0, 1] 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (![1, 0, 1] : Vec 3)).const_add x
  have hφd : HasDerivAt (fun s : ℝ => NuclearSymmetric2.nuclearCoords (x + s • ![1, 0, 1]))
      (fderiv ℝ NuclearSymmetric2.nuclearCoords x ![1, 0, 1]) 0 :=
    HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hdiff.hasFDerivAt hline (by simp)
  have hmin : IsLocalMin (fun s : ℝ => NuclearSymmetric2.nuclearCoords (x + s • ![1, 0, 1])) 0 :=
    Filter.Eventually.of_forall fun s => by
      simp only [hφs, mul_zero, add_zero, max_self]
      exact le_max_right _ _
  rw [hmin.hasDerivAt_eq_zero hφd] at hφd
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp
    ((hasDerivAt_iff_isLittleO.mp hφd).def (by norm_num : (0 : ℝ) < 1))
  have hδ2 : 0 < δ / 2 := half_pos hδ
  have key : ∀ s : ℝ, 0 < |s| → |s| < δ →
      |x 0 + x 2| + 2 * |s| ≤ |x 0 + x 2 + 2 * s| → False := by
    intro s hs0 hsδ hgrow
    have hb := @hball s (by rw [Real.dist_eq, sub_zero]; exact hsδ)
    simp only [hφs, mul_zero, add_zero, max_self, smul_zero, sub_zero, Real.norm_eq_abs,
      one_mul] at hb
    have h1 := (abs_le.mp hb).2
    have h2 : |x 0 + x 2 + 2 * s| ≤ max |x 0 + x 2 + 2 * s| |x 0 + x 2| := le_max_left _ _
    linarith
  rcases le_or_lt 0 (x 0 + x 2) with hc | hc
  · refine key (δ / 2) (by rw [abs_of_pos hδ2]; exact hδ2) (by rw [abs_of_pos hδ2]; linarith) ?_
    rw [abs_of_pos hδ2, abs_of_nonneg hc, abs_of_nonneg (by linarith)]
  · refine key (-(δ / 2)) (by rw [abs_neg, abs_of_pos hδ2]; exact hδ2)
      (by rw [abs_neg, abs_of_pos hδ2]; linarith) ?_
    rw [abs_neg, abs_of_pos hδ2, abs_of_neg hc, abs_of_neg (by linarith)]
    linarith

/-- Every line through a point of differentiability of the nuclear norm contains at most two
points of non-differentiability: they lie on the cone of `nuclear_not_differentiableAt`, a
quadratic equation in the line parameter whose constant term is nonzero. -/
theorem nuclear_line_countable (x p : Vec 3)
    (hx : DifferentiableAt ℝ NuclearSymmetric2.nuclearCoords x) :
    {t : ℝ | ¬ DifferentiableAt ℝ NuclearSymmetric2.nuclearCoords (x + t • p)}.Countable := by
  have hx' : (x 0 + x 2) ^ 2 - NuclearSymmetric2.discr x ≠ 0 :=
    sub_ne_zero.mpr fun h => nuclear_not_differentiableAt h hx
  have hq : ∀ t : ℝ, ((x + t • p) 0 + (x + t • p) 2) ^ 2 - NuclearSymmetric2.discr (x + t • p) =
      ((p 0 + p 2) ^ 2 - (p 0 - p 2) ^ 2 - 2 * p 1 ^ 2) * t ^ 2 +
        (2 * (x 0 + x 2) * (p 0 + p 2) - 2 * (x 0 - x 2) * (p 0 - p 2) - 4 * x 1 * p 1) * t +
        ((x 0 + x 2) ^ 2 - NuclearSymmetric2.discr x) := by
    intro t
    simp only [NuclearSymmetric2.discr, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  refine Set.Countable.mono (fun t ht => ?_) (AdmissibleRunExistence.quadratic_zeros_finite
    (a := (p 0 + p 2) ^ 2 - (p 0 - p 2) ^ 2 - 2 * p 1 ^ 2)
    (b := 2 * (x 0 + x 2) * (p 0 + p 2) - 2 * (x 0 - x 2) * (p 0 - p 2) - 4 * x 1 * p 1)
    (fun h => hx' h.2.2)).countable
  show _ = (0 : ℝ)
  rw [← hq t]
  exact Classical.byContradiction fun h => ht (nuclear_differentiableAt (sub_ne_zero.mp h))

/-- No point of differentiability of the nuclear norm has gradient zero: it would be a minimizer,
hence $0$, where the norm is not differentiable. -/
theorem nuclear_gradient_ne_zero {y g : Vec 3}
    (h : HasFDerivAt NuclearSymmetric2.nuclearCoords (gradientFunctional g) y) : g ≠ 0 := by
  rintro rfl
  have hle : NuclearSymmetric2.nuclearCoords y ≤ NuclearSymmetric2.nuclearCoords 0 := by
    have hs := convex_supporting_inequality NuclearSymmetric2.nuclearCoords_convex h 0
    simp only [dot, Pi.zero_apply, zero_mul, Finset.sum_const_zero] at hs
    linarith
  have hy : y = 0 := NuclearSymmetric2.nuclearCoords_unique_zero y (le_antisymm
    (hle.trans_eq NuclearSymmetric2.nuclearCoords_zero)
    (NuclearSymmetric2.nuclearCoords_zero ▸ NuclearSymmetric2.nuclearCoords_minimum y))
  subst hy
  exact nuclear_not_differentiableAt (by simp [NuclearSymmetric2.discr]) h.differentiableAt

/-- Admissible runs on the nuclear norm of symmetric $2\times2$ matrices exist, by the general
existence theorem `AdmissibleRunExistence.exists_admissible_run` (from $x_0=(1,0,1)$, the
identity matrix, with $H_0=I$, $c_1=1/4$, $c_2=1/2$): the norm is convex and bounded below,
differentiable at all but at most two points of every line through a point of differentiability
(`nuclear_line_countable`), and no point of differentiability has gradient zero
(`nuclear_gradient_ne_zero`). -/
theorem nuclear_run_exists : Nonempty (AdmissibleBFGSRun 3 NuclearSymmetric2.nuclearCoords) := by
  have hg0 : HasFDerivAt NuclearSymmetric2.nuclearCoords (gradientFunctional ![1, 0, 1])
      ![1, 0, 1] :=
    NuclearSymmetric2.nuclearCoords_hasGradient_pos (by
      norm_num [NuclearSymmetric2.discr, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons])
  obtain ⟨R, -⟩ := AdmissibleRunExistence.exists_admissible_run
    NuclearSymmetric2.nuclearCoords_convex
    ⟨0, by
      rintro _ ⟨y, rfl⟩
      exact NuclearSymmetric2.nuclearCoords_zero ▸ NuclearSymmetric2.nuclearCoords_minimum y⟩
    (fun x p hx _ => nuclear_line_countable x p hx) (fun _ _ h => nuclear_gradient_ne_zero h)
    hg0 Matrix.PosDef.one (c₁ := 1 / 4) (c₂ := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨R⟩

/-- `centered_nuclear_covered` is not vacuous: admissible runs on the nuclear norm of symmetric
$2\times2$ matrices exist (`nuclear_run_exists`). -/
example : Nonempty (AdmissibleBFGSRun 3 NuclearSymmetric2.nuclearCoords) := nuclear_run_exists

/-- An admissible run on the objective $F(x)=x^2+\max\{x,0\}^2+|x-1|$ of `plq_hessians_and_jumps`
(built by `Article.Global.oneDimRun`): $x_k=\frac14+2^{-k-2}$ in the cell $[0,1]$, where
$F=2x^2-x+1$, with gradients $g_k=2^{-k}$, $H_k=\frac14$ (the secant ratio), steps
$\alpha_k=\frac12$ and $c_1=\frac14$, $c_2=\frac12$; its values tend to $F_*=F(1/4)=7/8$. -/
theorem plq_example_run (F : Vec 1 → ℝ)
    (hF_def : ∀ x, F x = x 0 ^ 2 + max (x 0) 0 ^ 2 + |x 0 - 1|) :
    ∃ R : AdmissibleBFGSRun 1 F,
      Tendsto (fun k => F (R.x k)) atTop (𝓝 (F (fun _ => 1 / 4))) := by
  obtain ⟨_a, _b, _P, _Q, _c, _d, hconv, -⟩ := plq_hessians_and_jumps F hF_def
  set f : ℝ → ℝ := fun t => t ^ 2 + max t 0 ^ 2 + |t - 1| with hf
  have hFe : F = fun x => f (x 0) := funext hF_def
  have hcell : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → f t = 2 * t ^ 2 + (-1) * t + 1 := by
    intro t h0 h1
    simp only [hf, max_eq_left h0, abs_of_nonpos (by linarith : t - 1 ≤ 0)]
    ring
  have hFv : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      F (OneDimensional.embed t) = 2 * t ^ 2 + (-1) * t + 1 := by
    intro t h0 h1
    rw [hFe]
    exact hcell t h0 h1
  set xs : ℕ → ℝ := fun k => 1 / 4 + (1 / 2) ^ (k + 2) with hxs
  set gs : ℕ → ℝ := fun k => (1 / 2) ^ k with hgs
  have e2 : ∀ k : ℕ, (1 / 2 : ℝ) ^ (k + 2) = (1 / 2) ^ k / 4 := fun k => by ring
  have e3 : ∀ k : ℕ, (1 / 2 : ℝ) ^ (k + 1 + 2) = (1 / 2) ^ k / 8 := fun k => by ring
  have e1 : ∀ k : ℕ, (1 / 2 : ℝ) ^ (k + 1) = (1 / 2) ^ k / 2 := fun k => by ring
  have hpos : ∀ k : ℕ, (0 : ℝ) < (1 / 2) ^ k := fun k => by positivity
  have hle : ∀ k : ℕ, (1 / 2 : ℝ) ^ k ≤ 1 := fun k => pow_le_one₀ (by norm_num) (by norm_num)
  have hx0 : ∀ k, 0 < xs k := fun k => by simp only [hxs]; positivity
  have hx1 : ∀ k, xs k < 1 := fun k => by simp only [hxs]; rw [e2]; linarith [hle k]
  have hgrad : ∀ k, HasFDerivAt F (gradientFunctional (OneDimensional.embed (gs k)))
      (OneDimensional.embed (xs k)) := by
    intro k
    rw [hFe]
    apply ScalarCounterexamples.coordinate_hasGradient
    have hev : f =ᶠ[𝓝 (xs k)] fun s => 2 * s ^ 2 + (-1) * s + 1 := by
      filter_upwards [Ioo_mem_nhds (hx0 k) (hx1 k)] with s hs
      exact hcell s hs.1.le hs.2.le
    have h := (hasDerivAt_quad 2 (-1) 1 (xs k)).congr_of_eventuallyEq hev
    convert h using 1
    simp only [hgs, hxs]
    rw [e2]
    ring
  have hvals : ∀ k, F (OneDimensional.embed (xs k)) = 7 / 8 + ((1 / 2) ^ k) ^ 2 / 8 := by
    intro k
    rw [hFv _ (hx0 k).le (hx1 k).le]
    simp only [hxs]
    rw [e2]
    ring
  have hstar : F (fun _ => 1 / 4) = 7 / 8 := by
    rw [show (fun _ : Fin 1 => (1 / 4 : ℝ)) = OneDimensional.embed (1 / 4) from rfl,
      hFv _ (by norm_num) (by norm_num)]
    norm_num
  let R := Article.Global.oneDimRun F hconv xs gs (fun _ => 1 / 4) (fun _ => 1 / 2) (1 / 4)
    (1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun _ => by norm_num)
    (fun k => (hpos k).ne') hgrad
    (fun k => by simp only [hxs, hgs]; rw [e3, e2]; ring)
    (fun k => by
      simp only [hxs]
      rw [e3, e2]
      intro h
      linarith [hpos k])
    (fun k => by
      simp only [hgs]
      rw [e1]
      intro h
      linarith [hpos k])
    (fun k => by
      simp only [hxs, hgs]
      rw [e3, e2, e1, eq_div_iff (by linarith [hpos k])]
      ring)
    (fun k => by
      rw [hFv _ (hx0 _).le (hx1 _).le, hFv _ (hx0 _).le (hx1 _).le]
      simp only [hxs, hgs]
      rw [e3, e2]
      nlinarith [sq_nonneg ((1 / 2 : ℝ) ^ k)])
    (fun k => by
      simp only [hxs, hgs]
      rw [e3, e2, e1]
      apply le_of_eq
      ring)
  refine ⟨R, ?_⟩
  have hR : (fun k => F (R.x k)) = fun k => 7 / 8 + ((1 / 2 : ℝ) ^ k) ^ 2 / 8 :=
    funext fun k => hvals k
  rw [hR, hstar]
  have h0 := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)).pow 2).div_const 8
  simpa using (tendsto_const_nhds (x := (7 / 8 : ℝ))).add h0

/-- `plq_hessians_and_jumps`, `plq_broader` and `smooth_plus_polyhedral_covered` are not vacuous:
on $F(x)=x^2+\max\{x,0\}^2+|x-1|$, for every $\varepsilon>0$ a tail of `plq_example_run` starts
below $F_*+\varepsilon$. -/
example (F : Vec 1 → ℝ) (hF_def : ∀ x, F x = x 0 ^ 2 + max (x 0) 0 ^ 2 + |x 0 - 1|) (ε : ℝ)
    (hε : 0 < ε) : ∃ run : AdmissibleBFGSRun 1 F, F (run.x 0) ≤ F (fun _ => 1 / 4) + ε := by
  obtain ⟨R, hR⟩ := plq_example_run F hF_def
  exact exists_low_run R hR ε hε

/-- `plq_covered_objective`, `plq_covered_loss` and `smooth_plus_polyhedral_covered` can have all
their assumptions at once, with low-starting runs: the loss $0$ plus the piecewise quadratic
regularizer $x^2+\max\{x,0\}^2+|x-1|$ with the cells of `plq_hessians_and_jumps` (runs: tails of
`plq_example_run`); and the benchmark as $\psi+\varphi$ with $\psi(u,v)=u^2$ and
$\varphi(u,v)=\max\{v,-v\}$ (runs: tails of `benchRun`). -/
example : (∃ (loss reg F : Vec 1 → ℝ) (a : Fin 3 → Fin 2 → Vec 1) (b : Fin 3 → Fin 2 → ℝ)
      (P : Fin 3 → Set (Vec 1)) (Q : Fin 3 → Mat 1) (c : Fin 3 → Vec 1) (d : Fin 3 → ℝ)
      (xstar : Vec 1),
      ConvexOn ℝ univ loss ∧ CenteredSmoothSublinear.LocallyC11On univ loss ∧
        ConvexOn ℝ univ reg ∧
        (∀ i, P i = {x | ∀ j, dot (a i j) x ≤ b i j}) ∧ (∀ i, (interior (P i)).Nonempty) ∧
        (∀ x, ∃ i, x ∈ P i) ∧
        (∀ i, ∀ x ∈ P i, reg x = dot x (Q i *ᵥ x) + dot (c i) x + d i) ∧
        (∀ x, F x = loss x + reg x) ∧ (∀ x, F xstar ≤ F x) ∧
        (∀ x, F x = F xstar → x = xstar) ∧
        ∀ ε : ℝ, 0 < ε → ∃ run : AdmissibleBFGSRun 1 F, F (run.x 0) ≤ F xstar + ε) ∧
    (∃ (ψ φ G : Vec 2 → ℝ) (p : Fin 2 → Vec 2) (q : Fin 2 → ℝ),
      ConvexOn ℝ univ ψ ∧ CenteredSmoothSublinear.LocallyC11On univ ψ ∧
        (∀ x, IsGreatest (Set.range fun j => dot (p j) x + q j) (φ x)) ∧
        (∀ x, G x = ψ x + φ x) ∧ (∀ x, G 0 ≤ G x) ∧ (∀ x, G x = G 0 → x = 0) ∧
        ∀ ε : ℝ, 0 < ε → ∃ run : AdmissibleBFGSRun 2 G, G (run.x 0) ≤ G 0 + ε) := by
  refine ⟨?_, ?_⟩
  · set F : Vec 1 → ℝ := fun x => x 0 ^ 2 + max (x 0) 0 ^ 2 + |x 0 - 1| with hFdef
    have hF_def : ∀ x, F x = x 0 ^ 2 + max (x 0) 0 ^ 2 + |x 0 - 1| := fun _ => rfl
    obtain ⟨a, b, P, Q, c, d, hconv, hmin, huniq, hP, hint, hcov, hrep, -⟩ :=
      plq_hessians_and_jumps F hF_def
    obtain ⟨R, hR⟩ := plq_example_run F hF_def
    exact ⟨fun _ => 0, F, F, a, b, P, Q, c, d, fun _ => 1 / 4, convexOn_const 0 convex_univ,
      locallyC11_of_contDiff_two contDiff_const, hconv, hP, hint, hcov, hrep,
      fun x => (zero_add _).symm, hmin, huniq,
      fun ε hε => exists_low_run R hR ε hε⟩
  · obtain ⟨-, hmin, huniq, -, hF0, hF, hrun⟩ := bench_facts
    obtain ⟨-, -, -, -, hψ, -, -, -, -⟩ :=
      Article.Global.mixed_hypotheses UnexcitedMetric.objective (fun _ => rfl)
    refine ⟨fun x => x 0 ^ 2, fun x => |x 1|, UnexcitedMetric.objective, ![![0, 1], ![0, -1]],
      fun _ => 0, hψ, locallyC11_of_contDiff_two (by fun_prop), fun x => ?_, fun x => hF x, hmin,
      huniq, fun ε hε => ?_⟩
    · have h0 : dot ![0, 1] x = x 1 := by simp [dot, Fin.sum_univ_two]
      have h1 : dot ![0, -1] x = -x 1 := by simp [dot, Fin.sum_univ_two]
      refine ⟨?_, ?_⟩
      · rcases abs_choice (x 1) with h | h
        · exact ⟨0, by simp only [Matrix.cons_val_zero, h0, add_zero, h]⟩
        · exact ⟨1, by simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero, h1,
            add_zero, h]⟩
      · rintro _ ⟨j, rfl⟩
        fin_cases j
        · simp only [Fin.zero_eta, Matrix.cons_val_zero, h0, add_zero]
          exact le_abs_self _
        · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero, h1,
            add_zero]
          exact neg_le_abs _
    · obtain ⟨R', hR'⟩ := exists_low_run benchRun (hrun benchRun) ε hε
      exact ⟨R', by rw [hF0]; exact hR'⟩

/-- The two-dimensional witness $u^2+v^2+(2+|u|)|v|$ is not differentiable on the axes. -/
theorem plq2d_not_differentiableAt_axes (F : Vec 2 → ℝ)
    (hF_def : ∀ x, F x = x 0 ^ 2 + x 1 ^ 2 + (2 + |x 0|) * |x 1|) (y : Vec 2)
    (hy : y 0 = 0 ∨ y 1 = 0) : ¬ DifferentiableAt ℝ F y := by
  intro hd
  have key : ∀ (e : Vec 2) (A c : ℝ), 0 < c →
      (∀ s : ℝ, F (y + s • e) = A + s ^ 2 + c * |s|) → False := by
    intro e A c hc hline
    have hl : DifferentiableAt ℝ (fun s : ℝ => y + s • e) 0 :=
      (differentiableAt_const _).add (differentiableAt_id.smul_const _)
    have hd0 : DifferentiableAt ℝ F (y + (0 : ℝ) • e) := by simpa using hd
    have hc' : DifferentiableAt ℝ (fun s : ℝ => F (y + s • e)) 0 := hd0.comp (0 : ℝ) hl
    have hcomp : DifferentiableAt ℝ (fun s : ℝ => (F (y + s • e) - A - s ^ 2) / c) 0 :=
      ((hc'.sub_const A).sub (differentiableAt_id.pow 2)).div_const c
    apply not_differentiableAt_abs_zero
    convert hcomp using 1
    funext s
    rw [hline s]
    field_simp
    ring
  by_cases h1 : y 1 = 0
  · refine key ![0, 1] (y 0 ^ 2) (2 + |y 0|) (by positivity) (fun s => ?_)
    rw [hF_def]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, mul_zero, add_zero, mul_one, h1, zero_add]
  · have h0 : y 0 = 0 := hy.resolve_right h1
    refine key ![1, 0] (y 1 ^ 2 + 2 * |y 1|) (|y 1|) (abs_pos.mpr h1) (fun s => ?_)
    rw [hF_def]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, mul_zero, add_zero, mul_one, h0, zero_add]
    ring

/-- The two-dimensional witness is differentiable off the axes (there it is locally a
quadratic). -/
theorem plq2d_differentiableAt (F : Vec 2 → ℝ)
    (hF_def : ∀ x, F x = x 0 ^ 2 + x 1 ^ 2 + (2 + |x 0|) * |x 1|) (y : Vec 2)
    (h0 : y 0 ≠ 0) (h1 : y 1 ≠ 0) : DifferentiableAt ℝ F y := by
  have hgen : ∀ σ0 σ1 : ℝ, |σ0| = 1 → |σ1| = 1 → 0 < σ0 * y 0 → 0 < σ1 * y 1 →
      DifferentiableAt ℝ F y := by
    intro σ0 σ1 hs0 hs1 hy0 hy1
    have hO : IsOpen {x : Vec 2 | 0 < σ0 * x 0 ∧ 0 < σ1 * x 1} :=
      (isOpen_lt continuous_const (continuous_const.mul (continuous_apply 0))).inter
        (isOpen_lt continuous_const (continuous_const.mul (continuous_apply 1)))
    have hev : F =ᶠ[𝓝 y] fun x : Vec 2 => x 0 ^ 2 + x 1 ^ 2 + (2 + σ0 * x 0) * (σ1 * x 1) := by
      filter_upwards [hO.mem_nhds ⟨hy0, hy1⟩] with x hx
      rw [hF_def]
      have ha0 : |x 0| = σ0 * x 0 := by
        have := abs_of_pos hx.1
        rw [abs_mul, hs0, one_mul] at this
        exact this
      have ha1 : |x 1| = σ1 * x 1 := by
        have := abs_of_pos hx.2
        rw [abs_mul, hs1, one_mul] at this
        exact this
      rw [ha0, ha1]
    have hpoly : DifferentiableAt ℝ
        (fun x : Vec 2 => x 0 ^ 2 + x 1 ^ 2 + (2 + σ0 * x 0) * (σ1 * x 1)) y := by fun_prop
    exact hpoly.congr_of_eventuallyEq hev
  rcases lt_or_gt_of_ne h0 with ha | ha <;> rcases lt_or_gt_of_ne h1 with hb | hb
  · exact hgen (-1) (-1) (by norm_num) (by norm_num) (by linarith) (by linarith)
  · exact hgen (-1) 1 (by norm_num) (by norm_num) (by linarith) (by linarith)
  · exact hgen 1 (-1) (by norm_num) (by norm_num) (by linarith) (by linarith)
  · exact hgen 1 1 (by norm_num) (by norm_num) (by linarith) (by linarith)

/-- Admissible runs on the two-dimensional witness start arbitrarily low: the general
existence theorem `AdmissibleRunExistence.exists_admissible_run` applies (the
non-differentiability set is the union of the axes, which a line through a point of
differentiability meets at most twice; the only stationary candidate is the minimizer $0$, where
$F$ is not differentiable), from $x_0=(\delta,\delta)$ with $\delta=\min\{1,\varepsilon/5\}$. -/
theorem plq2d_low_runs (F : Vec 2 → ℝ)
    (hF_def : ∀ x, F x = x 0 ^ 2 + x 1 ^ 2 + (2 + |x 0|) * |x 1|) (ε : ℝ) (hε : 0 < ε) :
    ∃ run : AdmissibleBFGSRun 2 F, F (run.x 0) ≤ F 0 + ε := by
  obtain ⟨hconv, hmin, huniq, -⟩ := plq2d_covered F hF_def
  have hF0 : F 0 = 0 := by simp [hF_def]
  have hbdd : BddBelow (range F) := ⟨0, by rintro _ ⟨y, rfl⟩; exact hF0 ▸ hmin y⟩
  have hline : ∀ x p : Vec 2, DifferentiableAt ℝ F x → p ≠ 0 →
      {t : ℝ | ¬ DifferentiableAt ℝ F (x + t • p)}.Countable := by
    intro x p hx _
    have hx0 : x 0 ≠ 0 := fun h => plq2d_not_differentiableAt_axes F hF_def x (Or.inl h) hx
    have hx1 : x 1 ≠ 0 := fun h => plq2d_not_differentiableAt_axes F hF_def x (Or.inr h) hx
    have hsub : {t : ℝ | ¬ DifferentiableAt ℝ F (x + t • p)} ⊆
        {t | x 0 + t * p 0 = 0} ∪ {t | x 1 + t * p 1 = 0} := by
      intro t ht
      refine Classical.byContradiction fun hn => ?_
      simp only [mem_union, mem_setOf_eq, not_or] at hn
      exact ht (plq2d_differentiableAt F hF_def _ (by simpa using hn.1) (by simpa using hn.2))
    have hsing : ∀ (a q : ℝ), a ≠ 0 → {t : ℝ | a + t * q = 0}.Subsingleton := by
      intro a q ha t1 h1 t2 h2
      simp only [mem_setOf_eq] at h1 h2
      by_cases hq : q = 0
      · rw [hq, mul_zero, add_zero] at h1
        exact absurd h1 ha
      · have : (t1 - t2) * q = 0 := by linarith
        rcases mul_eq_zero.mp this with h | h
        · linarith
        · exact absurd h hq
    exact Set.Countable.mono hsub
      (((hsing _ _ hx0).countable).union ((hsing _ _ hx1).countable))
  have hstat : ∀ y g, HasFDerivAt F (gradientFunctional g) y → g ≠ 0 := by
    rintro y g hg rfl
    have hs := convex_supporting_inequality hconv hg 0
    have hle : F y ≤ F 0 := by
      simp only [dot, Pi.zero_apply, zero_mul, Finset.sum_const_zero] at hs
      linarith
    have hy : y = 0 := huniq y (le_antisymm hle (hmin y))
    subst hy
    exact plq2d_not_differentiableAt_axes F hF_def 0 (Or.inl rfl) hg.differentiableAt
  set δ := min 1 (ε / 5) with hδ
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ ≤ ε / 5 := min_le_right _ _
  have hd : DifferentiableAt ℝ F ![δ, δ] :=
    plq2d_differentiableAt F hF_def _ (by simpa using hδ0.ne') (by simpa using hδ0.ne')
  obtain ⟨R, hx, -⟩ := AdmissibleRunExistence.exists_admissible_run hconv hbdd hline hstat
    (hasFDerivAt_coordinateGradient hd) Matrix.PosDef.one (c₁ := 1 / 4) (c₂ := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨R, ?_⟩
  rw [hx, hF0, hF_def]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, abs_of_pos hδ0]
  nlinarith

/-- `plq_broader_2d`, `plq2d_covered` and `plq2d_not_smooth_plus_max_affine` are not vacuous: on
$u^2+v^2+(2+|u|)|v|$, admissible runs start below $F_*+\varepsilon$ for every $\varepsilon>0$
(`plq2d_low_runs`). -/
example (F : Vec 2 → ℝ) (hF_def : ∀ x, F x = x 0 ^ 2 + x 1 ^ 2 + (2 + |x 0|) * |x 1|) (ε : ℝ)
    (hε : 0 < ε) : ∃ run : AdmissibleBFGSRun 2 F, F (run.x 0) ≤ F 0 + ε :=
  plq2d_low_runs F hF_def ε hε

/-- `centered_nuclear_smooth_covered` is not vacuous: with $\psi=0$ its assumptions hold for the
nuclear norm, with $b=F(x_0)$ for an admissible run (`nuclear_run_exists`), which starts in
$K$. -/
example : ∃ (F ψ : Vec 3 → ℝ) (b : ℝ) (K : Set (Vec 3)) (run : AdmissibleBFGSRun 3 F),
    ConvexOn ℝ univ ψ ∧ CenteredSmoothSublinear.LocallyC11On univ ψ ∧
      (∀ x, F x = ψ x + NuclearSymmetric2.nuclearCoords x) ∧ (∀ x, F 0 ≤ F x) ∧ F 0 < b ∧
      K = {x | F x ≤ b} ∧ IsCompact K ∧ F (run.x 0) ≤ b := by
  obtain ⟨R⟩ := nuclear_run_exists
  have hmin : ∀ x, NuclearSymmetric2.nuclearCoords 0 ≤ NuclearSymmetric2.nuclearCoords x :=
    NuclearSymmetric2.nuclearCoords_minimum
  exact ⟨NuclearSymmetric2.nuclearCoords, fun _ => 0, _, _, R, convexOn_const 0 convex_univ,
    locallyC11_of_contDiff_two contDiff_const, fun x => (zero_add _).symm, hmin,
    Article.Global.initial_value_gt R 0 hmin, rfl,
    NuclearSymmetric2.nuclearCoords_sublevel_compact _, le_rfl⟩

/-- `gauge_sublinear` is not vacuous for asymmetric sets: $S=\{x\in\R:-1/2<x<1\}$ is convex and
absorbent and not symmetric. -/
example : ∃ S : Set (Vec 1), Convex ℝ S ∧ Absorbent ℝ S ∧ ∃ x ∈ S, -x ∉ S := by
  set S : Set (Vec 1) := {x | -1 < 2 * x 0 ∧ x 0 < 1} with hS
  have hc1 : Convex ℝ {x : Vec 1 | -1 < 2 * x 0} := by
    have h := convex_halfSpace_gt (𝕜 := ℝ)
      (f := fun x : Vec 1 => 2 * x 0) (by
        refine ⟨fun x y => ?_, fun c x => ?_⟩ <;> simp [mul_add, mul_left_comm]) (-1)
    simpa using h
  have hc2 : Convex ℝ {x : Vec 1 | x 0 < 1} := by
    have h := convex_halfSpace_lt (𝕜 := ℝ)
      (f := fun x : Vec 1 => x 0) (by
        refine ⟨fun x y => ?_, fun c x => ?_⟩ <;> simp) 1
    simpa using h
  have hopen : IsOpen S :=
    (isOpen_lt continuous_const (continuous_const.mul (continuous_apply 0))).inter
      (isOpen_lt (continuous_apply 0) continuous_const)
  have h0 : (0 : Vec 1) ∈ S := by simp [hS]
  refine ⟨S, hc1.inter hc2, absorbent_nhds_zero (hopen.mem_nhds h0), fun _ => 9 / 10, ?_, ?_⟩
  · simp only [hS, mem_setOf_eq]
    norm_num
  · simp only [hS, mem_setOf_eq, Pi.neg_apply]
    norm_num

end BfgsCoverage.Companion.Ch04R
