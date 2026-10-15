import BfgsArticle.Coverage.Article.Global
import BfgsArticle.Coverage.Article.Local
import BfgsArticle.Coverage.Article.Energy
import BfgsVerification.MaxAffineBasin
import BfgsVerification.MaxAffineCalculus
import BfgsVerification.TransformedGaugeInverse
import BfgsVerification.AffineImageLifting
import BfgsVerification.AffineImageRanges
import BfgsVerification.ObjectiveLogRates
import BfgsVerification.QuadraticGaugeRates
import BfgsVerification.HarmonicRates
import BfgsVerification.UnexcitedMetric
import BfgsVerification.FiniteRayLineSearch
import BfgsVerification.FivePieceObstruction
import BfgsVerification.ScalarResidualFamilies
import BfgsVerification.EuclideanResidualLineSearch
import BfgsVerification.PoweredGaugeRadial
import BfgsVerification.CenteredSpectral
import BfgsArticle.AdmissibleRunExistence

/-!
# Lean coverage: `companion/chapters/06_F.tex`

Chapter F ("Concrete objectives, lifting and rates") of the companion: Theorems `F:centered`,
`F:transform` and `F:lifting`, the displays of their proofs, the max-affine identity
\eqref{F:active} and threshold \eqref{F:basin}, the residual reductions, the rate paragraphs,
the $u^2+|v|$ matrix example, the tilted-minimum line-search construction, the five-piece
obstruction, and the claims of the surrounding text. Register:
`editorial/lean_coverage/register/C_06_F.json`.

## Conventions

* `Vec n` carries the sup norm; Euclidean norms are explicit: $\|v\|$ is `‖euclideanVector v‖`,
  $\|v\|^2$ is `sqNorm v`, $a^Tb$ is `dot a b`. "Finite convex" is `ConvexOn ℝ univ F` with
  `F : Vec n → ℝ`; $x_*$ minimizes $F$ is `∀ x, F xstar ≤ F x`; uniqueness is
  `∀ x, F x = F xstar → x = xstar` (or `∀ y, (∀ x, F y ≤ F x) → y = xstar`).
* An infinite admissible full-BFGS run (the convention of `01_I.tex:40-47`: nonzero gradients at
  differentiable accepted iterates, positive lengths, fixed $0<c_1<c_2<1$, arbitrary
  $H_0\succ0$) is `R : AdmissibleBFGSRun n F`; `R.x k`, `R.g k`, `R.H k`, `R.α k`, `R.c₁`,
  `R.c₂` are $x_k,g_k,H_k,\alpha_k,c_1,c_2$; $s_k$, $y_k$, $t_k$, $q_k$, $d_k$ are
  `R.displacement k`, `R.gradientChange k`, `R.curvature k`, `R.q k`, `R.d k`;
  $R_k=(y_k^T(x_{k+1}-x_*))^2/t_k$ and $E_0=(x_0-x_*)^TH_0^{-1}(x_0-x_*)$ are written out;
  $S_N=\sum_{k<N}q_k^{-1}$ is a variable `S` with its defining equation.
* "Locally $C^{1,1}$ on $U$" is `CenteredSmoothSublinear.LocallyC11On U ψ` (differentiable on
  $U$ with locally Lipschitz derivative); $\nabla\psi(x)$ is `coordinateGradient ψ x`;
  "positively homogeneous of degree one" is `Homogeneous.PositiveDegreeOne γ`; $h\in\partial\gamma
  (x)$ is `Homogeneous.Supports γ x h`; "coercive" is `Tendsto F (cocompact _) atTop`.
* Objects introduced by the text ($a,b,\xi,\zeta$, $y_\psi$, $y_\gamma$, $\Theta$, $\Phi^{-1}$,
  $\delta_j$, $P_j$, $\tau_*$, $L_0$, $\Phi_0$, $A_N$, $C_\gamma$, $\sigma$, $\psi$, ...) are
  variables with their defining equations; a hypothesis whose name starts with `_` is a standing
  assumption that the Lean proof does not use.

## Items

* `theorem/F:centered` (lines 11-13): `centered`, `centered_local`.
* `disp/001`, `disp/002` (16-27): `centered_split_notation`, `centered_secant_bound`.
* `theorem/F:transform` (37-39): `transform`.
* `disp/003`-`disp/006` (42-57): `transform_euler`, `transform_theta_derivative`,
  `transform_secant_pairing`, `transform_correction`.
* `disp/007` (`F:active`), `disp/008` (68-74): `maxAffine_active`, `maxAffine_inactive`.
* `disp/009`, `disp/010` (`F:basin`) (78-85): `maxAffine_active_region`,
  `maxAffine_threshold_def`.
* `theorem/F:lifting` with `disp/011` (98-103): `lifting`.
* `disp/012` (106-108): `lifting_right_inverse`.
* `disp/013`, `disp/014` (122-132): `bounded_correction_rate`, `homogeneous_weighted_sum`.
* `disp/015`-`disp/021` (137-168): `quadGauge_split`, `quadGauge_split_bounds`,
  `quadGauge_correction`, `quadGauge_budget`, `quadGauge_increment`,
  `quadGauge_increment_exact`, `quadGauge_rate`.
* `disp/022`, `disp/023` (178-186): `unexcited_run`.
* `disp/024`, `disp/025` (190-196): `tilted_armijo`, `tilted_wolfe`.
* `disp/026` (200-202): `five_piece_def`.

Prose items are covered by the theorems whose docstrings cite them. Undisplayed steps of proofs
are stated by `centered_split_bounds`, `transform_inverse`, `lifting_steps`.

## Non-vacuity

The `example`s at the end show that the standing assumptions can hold, with explicit admissible
runs: `mixedRun` (the library's `UnexcitedMetric.run` on $u^2+|v|$) for Theorem `F:centered`, its
proof displays, `mixed_full_convergence`, `powered_gauges_covered`, the rate statements with
bounded corrections and the quadratic-plus-gauge paragraph ($Q=\operatorname{diag}(2)$,
$\gamma=|\cdot|$); `basinRun` (the same run started at $F(x_0)=\delta$) inside the basins of the
local statements `centered_local`, `maxAffine_local_basin`, `kink_sums_basin` and
`residual_sums_basin`; a run on $x^4+|x|$ (`quarticAbs_run_exists`, by the general existence
result) for `centered_no_global_lipschitz`; the article's `absRun` on $|x|$ for Theorem
`F:transform` and the displays of its proof (with $L=F(x_1)>0$), the max-affine and threshold
statements ($p=\max\{x,-x\}$), Theorem `F:lifting` and the homogeneous rates;
$p=\max\{x,-x,x-1\}$ for an inactive piece (`maxAffine_inactive`); and simple data for the
tilted-minimum and line-search statements. The displays of the proof of Theorem `F:transform`
(`transform_euler` to `transform_correction`) are stated without the proof's contradiction
hypothesis $F_k\ge L>0$ for all $k$ (which no run satisfies): the first three need none,
`transform_correction` only $F(x_{k+1})\ge L$; likewise `transform_correction_annulus` asks
$F(x_{k+1})\ge\eta$ only of the pairs it bounds.
-/

noncomputable section
open scoped Topology
open Set Filter Matrix BfgsVerification

namespace BfgsCoverage.Companion.Ch06F

/-! ### Helpers -/

/-- `‖euclideanVector v‖ ^ 2 = sqNorm v`. -/
theorem norm_sq {n : ℕ} (v : Vec n) : ‖euclideanVector v‖ ^ 2 = sqNorm v :=
  BfgsCoverage.Article.Global.norm_euclideanVector_sq v

/-- Uniqueness of a gradient at a differentiable point. -/
theorem gradient_unique {n : ℕ} {F : Vec n → ℝ} {x g h : Vec n}
    (hg : HasFDerivAt F (gradientFunctional g) x) (hh : HasFDerivAt F (gradientFunctional h) x) :
    g = h :=
  AffineProjection.gradientFunctional_injective (hg.unique hh)

/-- The accepted step of a run is the difference of consecutive iterates. -/
theorem displacement_eq {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (k : ℕ) :
    R.displacement k = R.x (k + 1) - R.x k := by
  rw [R.step k]
  simp only [add_sub_cancel_left]
  rfl

/-! ### Theorem `F:centered` -/

/-- Item `C/06_F/theorem/F:centered`, Theorem `F:centered` (`companion/chapters/06_F.tex:11-13`)
("Centered smooth-plus-sublinear convergence"), first four sentences.

"Let $F(x)=\psi(x)+\gamma(x-x_*)$, where $\psi$ is convex and locally $C^{1,1}$ on an open convex
neighborhood of a compact initial sublevel, and $\gamma$ is finite convex and positively
homogeneous of degree one. Suppose $x_*$ minimizes $F$. Every infinite admissible full-BFGS run
has $F(x_k)\to F(x_*)$. If $x_*$ is unique, then $x_k\to x_*$."

The representation is global (`hrep`); $\psi$ is convex and locally $C^{1,1}$ on the open convex
set $U$ (`LocallyC11On U ψ`: differentiable on $U$ with locally Lipschitz derivative), and the
run's initial sublevel $\{F\le F(x_0)\}$ is compact and contained in $U$. The proof is
Theorem `art:centered` of the article (`BfgsCoverage.Article.Global.centered`), whose
representation is only required on $U$. The last sentence of the theorem is `centered_local`. -/
theorem centered {n : ℕ} {F : Vec n → ℝ} (xstar : Vec n) (ψ γ : Vec n → ℝ)
    (hrep : ∀ x, F x = ψ x + γ (x - xstar))
    (U : Set (Vec n)) (hU : IsOpen U) (hUc : Convex ℝ U)
    (hψ : ConvexOn ℝ U ψ) (hψ11 : CenteredSmoothSublinear.LocallyC11On U ψ)
    (hγ : ConvexOn ℝ univ γ) (hγh : Homogeneous.PositiveDegreeOne γ)
    (hmin : ∀ x, F xstar ≤ F x)
    (R : AdmissibleBFGSRun n F) (hK : IsCompact {x | F x ≤ F (R.x 0)})
    (hKU : {x | F x ≤ F (R.x 0)} ⊆ U) :
    Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) ∧
      ((∀ y, (∀ x, F y ≤ F x) → y = xstar) → Tendsto R.x atTop (𝓝 xstar)) := by
  obtain ⟨hv, -, hi⟩ := BfgsCoverage.Article.Global.centered R.convex xstar hmin U hU hUc ψ hψ
    hψ11 γ hγ hγh (fun x _ => hrep x) R hK hKU
  exact ⟨hv, hi⟩

/-- Item `C/06_F/theorem/F:centered`, Theorem `F:centered` (`companion/chapters/06_F.tex:11-13`),
last sentence: "A representation only near a unique minimizer gives a low-starting local theorem
by Lemma~\ref{M:localization}."

$F$ finite convex with unique minimizer $x_*$; the representation $F=\psi+\gamma(\cdot-x_*)$ and
the regularity of $\psi$ hold only on an open convex neighborhood $U$ of $x_*$. Then some
$\varepsilon>0$, chosen before the run and its initial matrix, gives for every admissible run with
$F(x_0)\le F(x_*)+\varepsilon$: iterates in $U$, $F(x_k)\to F(x_*)$ and $x_k\to x_*$. This is the
article's Corollary `art:local-centered` (`BfgsCoverage.Article.Local.local_centered`), proved
with the localization lemma. -/
theorem centered_local {n : ℕ} (F ψ γ : Vec n → ℝ) (hF : ConvexOn ℝ univ F) (xstar : Vec n)
    (hmin : ∀ x, F xstar ≤ F x) (huniq : ∀ x, F x = F xstar → x = xstar)
    (U : Set (Vec n)) (hU : IsOpen U) (hUc : Convex ℝ U) (hxU : xstar ∈ U)
    (hψ : ConvexOn ℝ U ψ) (hψ11 : CenteredSmoothSublinear.LocallyC11On U ψ)
    (hγ : ConvexOn ℝ univ γ) (hγh : Homogeneous.PositiveDegreeOne γ)
    (hrep : ∀ x ∈ U, F x = ψ x + γ (x - xstar)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ R : AdmissibleBFGSRun n F, F (R.x 0) ≤ F xstar + ε →
      (∀ k, R.x k ∈ U) ∧ Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) ∧
        Tendsto R.x atTop (𝓝 xstar) :=
  BfgsCoverage.Article.Local.local_centered F ψ γ hF xstar hmin huniq U hU hUc hxU hψ hψ11 hγ hγh
    hrep

/-! ### The proof of Theorem `F:centered` -/

/-- The gradient of $\gamma$ at a translated differentiable point of the representation. -/
theorem gamma_gradient {n : ℕ} {F : Vec n → ℝ} (xstar : Vec n) (ψ γ : Vec n → ℝ)
    (hrep : ∀ x, F x = ψ x + γ (x - xstar)) (U : Set (Vec n)) (hU : IsOpen U)
    (hψ11 : CenteredSmoothSublinear.LocallyC11On U ψ) {x g : Vec n} (hx : x ∈ U)
    (hg : HasFDerivAt F (gradientFunctional g) x) :
    HasFDerivAt γ (gradientFunctional (g - coordinateGradient ψ x)) (x - xstar) :=
  CenteredSmoothSublinear.homogeneous_summand_derivative xstar hU (fun z _ => hrep z) hx hg
    (hasFDerivAt_coordinateGradient ((hψ11.1 x hx).differentiableAt (hU.mem_nhds hx)))

/-- Item `C/06_F/disp/001` (`companion/chapters/06_F.tex:16-19`), in the proof of Theorem
`F:centered`: the notation
\[ a=y_\psi^Ts,\quad b=y_\gamma^Ts,\quad \xi=y_\psi^Tx',\quad\zeta=y_\gamma^Tx' \]
for an accepted pair $(x,z)=(x_k,x_{k+1})$, with $s=s_k$, $x'=x_{k+1}-x_*$ (the new point after
the translation $x_*=0$), and $y=y_k=y_\psi+y_\gamma$ split into the secant differences
$y_\psi=\nabla\psi(x_{k+1})-\nabla\psi(x_k)$ and $y_\gamma$ of $\gamma$ at the translated
endpoints. Under the hypotheses of the theorem and for a run whose initial sublevel is compact
and contained in $U$, the theorem states the facts behind this notation (proof, line 15): "At
differentiable endpoints, $\gamma$ is differentiable because $F$ and $\psi$ are", with gradient
$g_k-\nabla\psi(x_k)$ at $x_k-x_*$, so that $y_\gamma=(g_{k+1}-\nabla\psi(x_{k+1}))-(g_k-\nabla\psi
(x_k))$; then $y=y_\psi+y_\gamma$, $t=a+b$ and $y^Tx'=\xi+\zeta$. `yψ`, `yγ`, `a`, `b`, `ξ`, `ζ`
are variables with their defining equations. -/
theorem centered_split_notation {n : ℕ} {F : Vec n → ℝ} (xstar : Vec n) (ψ γ : Vec n → ℝ)
    (hrep : ∀ x, F x = ψ x + γ (x - xstar))
    (U : Set (Vec n)) (hU : IsOpen U) (_hUc : Convex ℝ U)
    (_hψ : ConvexOn ℝ U ψ) (hψ11 : CenteredSmoothSublinear.LocallyC11On U ψ)
    (_hγ : ConvexOn ℝ univ γ) (_hγh : Homogeneous.PositiveDegreeOne γ)
    (_hmin : ∀ x, F xstar ≤ F x)
    (R : AdmissibleBFGSRun n F) (_hK : IsCompact {x | F x ≤ F (R.x 0)})
    (hKU : {x | F x ≤ F (R.x 0)} ⊆ U) (k : ℕ)
    (yψ yγ : Vec n)
    (hyψ : yψ = coordinateGradient ψ (R.x (k + 1)) - coordinateGradient ψ (R.x k))
    (hyγ : yγ = (R.g (k + 1) - coordinateGradient ψ (R.x (k + 1))) -
      (R.g k - coordinateGradient ψ (R.x k)))
    (a b ξ ζ : ℝ) (ha : a = dot yψ (R.displacement k)) (hb : b = dot yγ (R.displacement k))
    (hξ : ξ = dot yψ (R.x (k + 1) - xstar)) (hζ : ζ = dot yγ (R.x (k + 1) - xstar)) :
    HasFDerivAt γ (gradientFunctional (R.g k - coordinateGradient ψ (R.x k))) (R.x k - xstar) ∧
      HasFDerivAt γ (gradientFunctional (R.g (k + 1) - coordinateGradient ψ (R.x (k + 1))))
        (R.x (k + 1) - xstar) ∧
      R.gradientChange k = yψ + yγ ∧ R.curvature k = a + b ∧
      dot (R.gradientChange k) (R.x (k + 1) - xstar) = ξ + ζ := by
  have hy : R.gradientChange k = yψ + yγ := by
    rw [hyψ, hyγ]
    simp only [AdmissibleBFGSRun.gradientChange]
    abel
  refine ⟨gamma_gradient xstar ψ γ hrep U hU hψ11 (hKU (R.iterate_mem_initialSublevel k))
      (R.hasGradient k),
    gamma_gradient xstar ψ γ hrep U hU hψ11 (hKU (R.iterate_mem_initialSublevel (k + 1)))
      (R.hasGradient (k + 1)), hy, ?_, ?_⟩
  · rw [AdmissibleBFGSRun.curvature, hy, ha, hb]
    exact add_dotProduct _ _ _
  · rw [hy, hξ, hζ]
    exact add_dotProduct _ _ _

/-- Proof of Theorem `F:centered`, undisplayed claims of `companion/chapters/06_F.tex:20-22`
(not a register item): "Then $a,b\ge0$ and $t=a+b$. Convex local $L$-smoothness gives
$\|y_\psi\|^2\le La$, hence $\xi^2\le LR^2a$. [...] If $h\in\partial\gamma(x)$, homogeneity and
the supporting inequality give $h^Tx=\gamma(x)$ and $h^Tz\le\gamma(z)$. Hence
$0\le\zeta\le b$. All subgradients of $\gamma$ are bounded by some $G_\gamma$, so
$\zeta\le2G_\gamma R$."

Standing assumptions: those of `centered_split_notation`, a radius `Rad` ($R$ of the text) with
$\|x-x_*\|\le R$ on the initial sublevel $K$, a constant $L>0$ with the convex local $L$-smoothness
estimate $\|\nabla\psi(y)-\nabla\psi(x)\|^2\le L(\nabla\psi(y)-\nabla\psi(x))^T(y-x)$ on $K$, and a
bound $G_\gamma$ on all subgradients of $\gamma$ (Euclidean norms). -/
theorem centered_split_bounds {n : ℕ} {F : Vec n → ℝ} (xstar : Vec n) (ψ γ : Vec n → ℝ)
    (hrep : ∀ x, F x = ψ x + γ (x - xstar))
    (U : Set (Vec n)) (hU : IsOpen U) (_hUc : Convex ℝ U)
    (_hψ : ConvexOn ℝ U ψ) (hψ11 : CenteredSmoothSublinear.LocallyC11On U ψ)
    (hγ : ConvexOn ℝ univ γ) (hγh : Homogeneous.PositiveDegreeOne γ)
    (_hmin : ∀ x, F xstar ≤ F x)
    (R : AdmissibleBFGSRun n F) (_hK : IsCompact {x | F x ≤ F (R.x 0)})
    (hKU : {x | F x ≤ F (R.x 0)} ⊆ U)
    (Rad : ℝ) (hRad : ∀ x ∈ {x | F x ≤ F (R.x 0)}, ‖euclideanVector (x - xstar)‖ ≤ Rad)
    (L : ℝ) (hL0 : 0 < L)
    (hL : ∀ x ∈ {x | F x ≤ F (R.x 0)}, ∀ y ∈ {x | F x ≤ F (R.x 0)},
      ‖euclideanVector (coordinateGradient ψ y - coordinateGradient ψ x)‖ ^ 2 ≤
        L * dot (coordinateGradient ψ y - coordinateGradient ψ x) (y - x))
    (Gγ : ℝ) (hG : ∀ x h, Homogeneous.Supports γ x h → ‖euclideanVector h‖ ≤ Gγ) (k : ℕ)
    (yψ yγ : Vec n)
    (hyψ : yψ = coordinateGradient ψ (R.x (k + 1)) - coordinateGradient ψ (R.x k))
    (hyγ : yγ = (R.g (k + 1) - coordinateGradient ψ (R.x (k + 1))) -
      (R.g k - coordinateGradient ψ (R.x k)))
    (a b ξ ζ : ℝ) (ha : a = dot yψ (R.displacement k)) (hb : b = dot yγ (R.displacement k))
    (hξ : ξ = dot yψ (R.x (k + 1) - xstar)) (hζ : ζ = dot yγ (R.x (k + 1) - xstar)) :
    0 ≤ a ∧ 0 ≤ b ∧ ‖euclideanVector yψ‖ ^ 2 ≤ L * a ∧ ξ ^ 2 ≤ L * Rad ^ 2 * a ∧
      0 ≤ ζ ∧ ζ ≤ b ∧ ζ ≤ 2 * Gγ * Rad := by
  have hxk := R.iterate_mem_initialSublevel k
  have hxk1 := R.iterate_mem_initialSublevel (k + 1)
  have hs := displacement_eq R k
  have hγk := gamma_gradient xstar ψ γ hrep U hU hψ11 (hKU hxk) (R.hasGradient k)
  have hγk1 := gamma_gradient xstar ψ γ hrep U hU hψ11 (hKU hxk1) (R.hasGradient (k + 1))
  have hsk := convex_supporting_inequality hγ hγk
  have hsk1 := convex_supporting_inequality hγ hγk1
  obtain ⟨hζ0, hζb⟩ := CenteredSmoothSublinear.homogeneous_secant_pairing hγh hsk hsk1
  have hsub : R.x (k + 1) - xstar - (R.x k - xstar) = R.displacement k := by rw [hs]; abel
  rw [hsub] at hζb
  have hyLa : ‖euclideanVector yψ‖ ^ 2 ≤ L * a := by
    rw [ha, hyψ, hs]
    exact hL _ hxk _ hxk1
  have ha0 : 0 ≤ a := by
    have := (sq_nonneg ‖euclideanVector yψ‖).trans hyLa
    exact nonneg_of_mul_nonneg_right (by linarith) hL0
  have hR := hRad _ hxk1
  have hR0 : 0 ≤ Rad := (norm_nonneg _).trans hR
  have hcs := BfgsCoverage.Article.Global.abs_dot_le_norm_mul_norm yψ (R.x (k + 1) - xstar)
  have hξsq : ξ ^ 2 ≤ L * Rad ^ 2 * a := by
    rw [hξ, ← sq_abs]
    have h1 : |dot yψ (R.x (k + 1) - xstar)| ≤ ‖euclideanVector yψ‖ * Rad :=
      hcs.trans (mul_le_mul_of_nonneg_left hR (norm_nonneg _))
    have h2 : |dot yψ (R.x (k + 1) - xstar)| ^ 2 ≤ (‖euclideanVector yψ‖ * Rad) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) h1 2
    calc |dot yψ (R.x (k + 1) - xstar)| ^ 2 ≤ (‖euclideanVector yψ‖ * Rad) ^ 2 := h2
      _ = ‖euclideanVector yψ‖ ^ 2 * Rad ^ 2 := by ring
      _ ≤ L * a * Rad ^ 2 := mul_le_mul_of_nonneg_right hyLa (sq_nonneg _)
      _ = L * Rad ^ 2 * a := by ring
  have hζG : ζ ≤ 2 * Gγ * Rad := by
    have hG1 := hG _ _ hsk1
    have hG2 := hG _ _ hsk
    have hdiff : ‖euclideanVector yγ‖ ≤ 2 * Gγ := by
      rw [hyγ]
      have he : euclideanVector ((R.g (k + 1) - coordinateGradient ψ (R.x (k + 1))) -
          (R.g k - coordinateGradient ψ (R.x k))) =
          euclideanVector (R.g (k + 1) - coordinateGradient ψ (R.x (k + 1))) -
            euclideanVector (R.g k - coordinateGradient ψ (R.x k)) := rfl
      rw [he]
      exact (norm_sub_le _ _).trans (by linarith)
    have hc := BfgsCoverage.Article.Global.abs_dot_le_norm_mul_norm yγ (R.x (k + 1) - xstar)
    rw [hζ]
    calc dot yγ (R.x (k + 1) - xstar) ≤ |dot yγ (R.x (k + 1) - xstar)| := le_abs_self _
      _ ≤ ‖euclideanVector yγ‖ * ‖euclideanVector (R.x (k + 1) - xstar)‖ := hc
      _ ≤ 2 * Gγ * Rad := mul_le_mul hdiff hR (norm_nonneg _)
          ((norm_nonneg _).trans hdiff)
  have hζeq : ζ = dot (R.g (k + 1) - coordinateGradient ψ (R.x (k + 1)) -
      (R.g k - coordinateGradient ψ (R.x k))) (R.x (k + 1) - xstar) := by rw [hζ, hyγ]
  have hbeq : b = dot (R.g (k + 1) - coordinateGradient ψ (R.x (k + 1)) -
      (R.g k - coordinateGradient ψ (R.x k))) (R.displacement k) := by rw [hb, hyγ]
  refine ⟨ha0, ?_, hyLa, hξsq, ?_, ?_, hζG⟩
  · rw [hbeq]; linarith
  · rw [hζeq]; exact hζ0
  · rw [hζeq, hbeq]; exact hζb

/-- Item `C/06_F/disp/002` (`companion/chapters/06_F.tex:23-27`), in the proof of Theorem
`F:centered`: "Weighted Cauchy--Schwarz gives
\[ \frac{(y^Tx')^2}{t}\le\frac{\xi^2}{a}+\frac{\zeta^2}{b}\le LR^2+2G_\gamma R. \]
Terms with zero denominator are zero since their numerators vanish."

Under the standing assumptions of `centered_split_bounds` (the theorem's hypotheses, the run, the
radius $R$ = `Rad`, the constants $L$ and $G_\gamma$, the notation of display `disp/001`), for
every accepted pair $(x_k,x_{k+1})$, with $t=t_k$ and $x'=x_{k+1}-x_*$. Lean's $u/0=0$ is the
convention of the last sentence (and its numerators do vanish: `centered_split_bounds`). -/
theorem centered_secant_bound {n : ℕ} {F : Vec n → ℝ} (xstar : Vec n) (ψ γ : Vec n → ℝ)
    (hrep : ∀ x, F x = ψ x + γ (x - xstar))
    (U : Set (Vec n)) (hU : IsOpen U) (hUc : Convex ℝ U)
    (hψ : ConvexOn ℝ U ψ) (hψ11 : CenteredSmoothSublinear.LocallyC11On U ψ)
    (hγ : ConvexOn ℝ univ γ) (hγh : Homogeneous.PositiveDegreeOne γ)
    (hmin : ∀ x, F xstar ≤ F x)
    (R : AdmissibleBFGSRun n F) (hK : IsCompact {x | F x ≤ F (R.x 0)})
    (hKU : {x | F x ≤ F (R.x 0)} ⊆ U)
    (Rad : ℝ) (hRad : ∀ x ∈ {x | F x ≤ F (R.x 0)}, ‖euclideanVector (x - xstar)‖ ≤ Rad)
    (L : ℝ) (hL0 : 0 < L)
    (hL : ∀ x ∈ {x | F x ≤ F (R.x 0)}, ∀ y ∈ {x | F x ≤ F (R.x 0)},
      ‖euclideanVector (coordinateGradient ψ y - coordinateGradient ψ x)‖ ^ 2 ≤
        L * dot (coordinateGradient ψ y - coordinateGradient ψ x) (y - x))
    (Gγ : ℝ) (hG : ∀ x h, Homogeneous.Supports γ x h → ‖euclideanVector h‖ ≤ Gγ) (k : ℕ)
    (yψ yγ : Vec n)
    (hyψ : yψ = coordinateGradient ψ (R.x (k + 1)) - coordinateGradient ψ (R.x k))
    (hyγ : yγ = (R.g (k + 1) - coordinateGradient ψ (R.x (k + 1))) -
      (R.g k - coordinateGradient ψ (R.x k)))
    (a b ξ ζ : ℝ) (ha : a = dot yψ (R.displacement k)) (hb : b = dot yγ (R.displacement k))
    (hξ : ξ = dot yψ (R.x (k + 1) - xstar)) (hζ : ζ = dot yγ (R.x (k + 1) - xstar)) :
    dot (R.gradientChange k) (R.x (k + 1) - xstar) ^ 2 / R.curvature k ≤
        ξ ^ 2 / a + ζ ^ 2 / b ∧
      ξ ^ 2 / a + ζ ^ 2 / b ≤ L * Rad ^ 2 + 2 * Gγ * Rad := by
  obtain ⟨-, -, -, ht, hnum⟩ := centered_split_notation xstar ψ γ hrep U hU hUc hψ hψ11 hγ hγh
    hmin R hK hKU k yψ yγ hyψ hyγ a b ξ ζ ha hb hξ hζ
  obtain ⟨ha0, hb0, hyLa, hξsq, hζ0, hζb, hζG⟩ := centered_split_bounds xstar ψ γ hrep U hU hUc
    hψ hψ11 hγ hγh hmin R hK hKU Rad hRad L hL0 hL Gγ hG k yψ yγ hyψ hyγ a b ξ ζ ha hb hξ hζ
  have htpos : 0 < R.curvature k := R.curvature_pos k
  rw [ht] at htpos
  rw [ht, hnum]
  -- numerators vanish with their denominators
  have hξ0 : a = 0 → ξ = 0 := fun h => by
    rw [h, mul_zero] at hξsq
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm hξsq (sq_nonneg ξ))
  have hζ0' : b = 0 → ζ = 0 := fun h => le_antisymm (h ▸ hζb) hζ0
  have hRad0 : 0 ≤ Rad := (norm_nonneg _).trans (hRad _ (R.iterate_mem_initialSublevel 0))
  have hG0 : 0 ≤ Gγ := (norm_nonneg _).trans (hG _ _ (convex_supporting_inequality hγ
    (gamma_gradient xstar ψ γ hrep U hU hψ11 (hKU (R.iterate_mem_initialSublevel 0))
      (R.hasGradient 0))))
  have hfirst : ξ ^ 2 / a ≤ L * Rad ^ 2 := by
    rcases ha0.eq_or_lt with h | h
    · rw [← h, div_zero]; positivity
    · rw [div_le_iff₀ h]; linarith
  have hsecond : ζ ^ 2 / b ≤ 2 * Gγ * Rad := by
    rcases hb0.eq_or_lt with h | h
    · rw [← h, div_zero]; positivity
    · rw [div_le_iff₀ h]
      have h1 : ζ ^ 2 ≤ b * ζ := by nlinarith
      have h2 : b * ζ ≤ b * (2 * Gγ * Rad) := mul_le_mul_of_nonneg_left hζG hb0
      linarith
  refine ⟨?_, add_le_add hfirst hsecond⟩
  rcases ha0.eq_or_lt with h | h
  · have hξz := hξ0 h.symm
    rw [← h, hξz]
    simp
  rcases hb0.eq_or_lt with h' | h'
  · have hζz := hζ0' h'.symm
    rw [← h', hζz]
    simp
  rw [div_add_div _ _ h.ne' h'.ne', div_le_div_iff₀ htpos (mul_pos h h')]
  nlinarith [sq_nonneg (b * ξ - a * ζ)]

/-! ### Remarks after the proof of Theorem `F:centered` (`06_F.tex:30`) -/

/-- Item `C/06_F/prose/004` (`companion/chapters/06_F.tex:30`): "Optimality implies
$-\nabla\psi(x_*)\in\partial\gamma(0)$." For $x_*$ minimizing $F$, the representation
$F=\psi+\gamma(\cdot-x_*)$ on an open $U\ni x_*$ with $\gamma$ positively homogeneous, and $\psi$
differentiable at $x_*$ with gradient $p$: $-p$ is a subgradient of $\gamma$ at $0$ (library
`CenteredSmoothSublinear.center_support`). -/
theorem centered_center_support {n : ℕ} (F ψ γ : Vec n → ℝ) (xstar : Vec n)
    (hmin : ∀ x, F xstar ≤ F x) (U : Set (Vec n)) (hU : IsOpen U) (hxU : xstar ∈ U)
    (hγh : Homogeneous.PositiveDegreeOne γ) (hrep : ∀ x ∈ U, F x = ψ x + γ (x - xstar))
    (p : Vec n) (hp : HasFDerivAt ψ (gradientFunctional p) xstar) :
    ∀ z, dot (-p) (z - 0) ≤ γ z - γ 0 :=
  CenteredSmoothSublinear.center_support xstar hmin hU hxU hγh hrep hp

/-- Item `C/06_F/prose/005` (`companion/chapters/06_F.tex:30`): "After translating, subtract the
smooth tangent plane from $\psi$ and add it to $\gamma$; both adjusted summands are then
nonnegative and minimized at zero." With $p=\nabla\psi(x_*)$, $\tilde\psi(x)=\psi(x)-\psi(x_*)-
p^T(x-x_*)$ and $\tilde\gamma(z)=\gamma(z)+p^Tz$ (variables with defining equations): on $U$,
$\tilde\psi\ge0$ with $\tilde\psi(x_*)=0$; $\tilde\gamma\ge0$ with $\tilde\gamma(0)=0$; and
$F(x)-F(x_*)=\tilde\psi(x)+\tilde\gamma(x-x_*)$ on $U$ (library
`CenteredSmoothSublinear.centered_rewriting`). $\tilde\gamma$ is still positively homogeneous and
$\tilde\psi$ still locally $C^{1,1}$ (`recenteredHomogeneous_homogeneous`,
`smoothRemainder_locallyC11`). -/
theorem centered_recentering {n : ℕ} (F ψ γ : Vec n → ℝ) (xstar : Vec n)
    (hmin : ∀ x, F xstar ≤ F x) (U : Set (Vec n)) (hU : IsOpen U) (hxU : xstar ∈ U)
    (hψ : ConvexOn ℝ U ψ) (hγh : Homogeneous.PositiveDegreeOne γ)
    (hrep : ∀ x ∈ U, F x = ψ x + γ (x - xstar))
    (p : Vec n) (hp : HasFDerivAt ψ (gradientFunctional p) xstar)
    (ψt γt : Vec n → ℝ) (hψt : ∀ x, ψt x = ψ x - ψ xstar - dot p (x - xstar))
    (hγt : ∀ z, γt z = γ z + dot p z) :
    (∀ x ∈ U, 0 ≤ ψt x) ∧ ψt xstar = 0 ∧ (∀ z, 0 ≤ γt z) ∧ γt 0 = 0 ∧
      ∀ x ∈ U, F x - F xstar = ψt x + γt (x - xstar) := by
  have hψe : ψt = CenteredSmoothSublinear.smoothRemainder ψ xstar p := funext hψt
  have hγe : γt = CenteredSmoothSublinear.recenteredHomogeneous γ p := funext hγt
  subst hψe hγe
  exact CenteredSmoothSublinear.centered_rewriting xstar hmin hU hxU hψ hγh hrep hp

/-! ### Theorem `F:transform` -/

/-- The six hypotheses on $\Phi$ in Theorem `F:transform` are the library structure
`TransformedGauge.IncreasingTransform`. -/
theorem increasingTransform_iff (Φ : ℝ → ℝ) :
    TransformedGauge.IncreasingTransform Φ ↔
      ContinuousOn Φ (Ici 0) ∧ ConvexOn ℝ (Ici 0) Φ ∧ StrictMonoOn Φ (Ici 0) ∧ Φ 0 = 0 ∧
        ContDiffOn ℝ 2 Φ (Ioi 0) ∧ ∀ r, 0 < r → 0 < deriv Φ r :=
  ⟨fun h => ⟨h.continuous, h.convex, h.strictMono, h.zero, h.smooth, h.deriv_pos⟩,
    fun ⟨h1, h2, h3, h4, h5, h6⟩ => ⟨h1, h2, h3, h4, h5, h6⟩⟩

/-- Item `C/06_F/theorem/F:transform`, Theorem `F:transform` (`companion/chapters/06_F.tex:37-39`)
("Transformed-gauge convergence").

"Let $\gamma$ be finite convex, degree-one homogeneous and coercive. Let
$\Phi:[0,\infty)\to\mathbb R$ be continuous, convex, strictly increasing, with $\Phi(0)=0$,
$\Phi\in C^2((0,\infty))$ and $\Phi'>0$ there. Then every infinite admissible full-BFGS run on
$F(x)=\Phi(\gamma(x-x_*))$ converges to $x_*$."

$\Phi$ is a function `ℝ → ℝ` constrained only on $[0,\infty)$ (and $C^2$ with $\Phi'>0$ on the
open half-line); coercive is `Tendsto γ (cocompact (Vec n)) atTop`. Proof: the library's
`AdmissibleBFGSRun.transformedGauge_convergence`, through the annulus route described in the
text after the proof. -/
theorem transform {n : ℕ} (γ : Vec n → ℝ) (hγ : ConvexOn ℝ univ γ)
    (hγh : Homogeneous.PositiveDegreeOne γ) (hγc : Tendsto γ (cocompact (Vec n)) atTop)
    (Φ : ℝ → ℝ) (hΦc : ContinuousOn Φ (Ici 0)) (hΦv : ConvexOn ℝ (Ici 0) Φ)
    (hΦm : StrictMonoOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0) (hΦ2 : ContDiffOn ℝ 2 Φ (Ioi 0))
    (hΦ' : ∀ r, 0 < r → 0 < deriv Φ r)
    (xstar : Vec n) (F : Vec n → ℝ) (hF : ∀ x, F x = Φ (γ (x - xstar)))
    (R : AdmissibleBFGSRun n F) :
    Tendsto R.x atTop (𝓝 xstar) := by
  have hT : TransformedGauge.IncreasingTransform Φ := ⟨hΦc, hΦv, hΦm, hΦ0, hΦ2, hΦ'⟩
  obtain rfl : F = TransformedGauge.objective Φ γ xstar := funext hF
  exact (AdmissibleBFGSRun.transformedGauge_convergence hT hγ hγh hγc xstar R).2

/-- The inverse $\Phi^{-1}$ of the proof of Theorem `F:transform` (`06_F.tex:44`): under the
hypotheses on $\Phi$, $\Phi$ maps $[0,\infty)$ onto $[0,\infty)$ bijectively; the library's
`TransformedGauge.inverse Φ` is an inverse there, and every inverse on $[0,\infty)$ agrees with it
on $[0,\infty)$. -/
theorem transform_inverse (Φ : ℝ → ℝ) (hΦ : TransformedGauge.IncreasingTransform Φ) :
    (∀ t, 0 ≤ t → 0 ≤ TransformedGauge.inverse Φ t ∧ Φ (TransformedGauge.inverse Φ t) = t) ∧
      ∀ Φinv : ℝ → ℝ, (∀ t, 0 ≤ t → 0 ≤ Φinv t ∧ Φ (Φinv t) = t) →
        ∀ t, 0 ≤ t → Φinv t = TransformedGauge.inverse Φ t := by
  refine ⟨fun t ht => ⟨TransformedGauge.inverse_nonneg hΦ ht,
    TransformedGauge.transform_inverse hΦ ht⟩, fun Φinv hinv t ht => ?_⟩
  apply hΦ.strictMono.injOn (hinv t ht).1 (TransformedGauge.inverse_nonneg hΦ ht)
  rw [(hinv t ht).2, TransformedGauge.transform_inverse hΦ ht]

/-- Item `C/06_F/disp/003` (`companion/chapters/06_F.tex:42-45`), in the proof of Theorem
`F:transform`: "Euler's identity and the chain rule give
\[ a_k=g_k^Tx_k=\gamma(x_k)\Phi'(\gamma(x_k))=\Theta(F_k),\quad
   \Theta(t)=\Phi^{-1}(t)\Phi'(\Phi^{-1}(t)). \]"

Under the hypotheses of the theorem, for every admissible run on $F$ and every $k$; after the
translation $x_*=0$, $x_k$ is $x_k-x_*$. $\Phi^{-1}$ is any inverse of $\Phi$ on $[0,\infty)$
(`Φinv`, unique there by `transform_inverse`), $\Theta$ and $a_k$ are variables with their defining
equations, $F_k=F(x_k)$. The proof states the display under its contradiction hypothesis
$F_k\ge L>0$ for all $k$, which the identity does not need, so it is stated without it. -/
theorem transform_euler {n : ℕ} (γ : Vec n → ℝ) (_hγ : ConvexOn ℝ univ γ)
    (hγh : Homogeneous.PositiveDegreeOne γ) (hγc : Tendsto γ (cocompact (Vec n)) atTop)
    (Φ : ℝ → ℝ) (hΦc : ContinuousOn Φ (Ici 0)) (hΦv : ConvexOn ℝ (Ici 0) Φ)
    (hΦm : StrictMonoOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0) (hΦ2 : ContDiffOn ℝ 2 Φ (Ioi 0))
    (hΦ' : ∀ r, 0 < r → 0 < deriv Φ r)
    (xstar : Vec n) (F : Vec n → ℝ) (hF : ∀ x, F x = Φ (γ (x - xstar)))
    (R : AdmissibleBFGSRun n F)
    (Φinv : ℝ → ℝ) (hΦinv : ∀ t, 0 ≤ t → 0 ≤ Φinv t ∧ Φ (Φinv t) = t)
    (Θ : ℝ → ℝ) (hΘ : ∀ t, Θ t = Φinv t * deriv Φ (Φinv t))
    (a : ℕ → ℝ) (ha : ∀ k, a k = dot (R.g k) (R.x k - xstar)) (k : ℕ) :
    a k = γ (R.x k - xstar) * deriv Φ (γ (R.x k - xstar)) ∧
      γ (R.x k - xstar) * deriv Φ (γ (R.x k - xstar)) = Θ (F (R.x k)) := by
  have hT : TransformedGauge.IncreasingTransform Φ := ⟨hΦc, hΦv, hΦm, hΦ0, hΦ2, hΦ'⟩
  obtain rfl : F = TransformedGauge.objective Φ γ xstar := funext hF
  obtain ⟨h1, h2⟩ := R.transformedGauge_euler hT hγh hγc xstar k
  have hnn : 0 ≤ TransformedGauge.objective Φ γ xstar (R.x k) :=
    TransformedGauge.objective_nonneg hT hγh hγc xstar (R.x k)
  have hinv := (transform_inverse Φ hT).2 Φinv hΦinv _ hnn
  refine ⟨by rw [ha]; exact h1, ?_⟩
  rw [hΘ, hinv, ← TransformedGauge.theta, ← h2, ← h1]

/-- Item `C/06_F/disp/004` (`companion/chapters/06_F.tex:47-49`), in the proof of Theorem
`F:transform`: "On $[L,F_0]$, the derivative
\[ \Theta'(t)=1+\frac{r\Phi''(r)}{\Phi'(r)},\qquad r=\Phi^{-1}(t), \]
is bounded."

Under the hypotheses of `transform_euler` ($\Phi^{-1}$ and $\Theta$ as there; $F_0=F(x_0)$), for
every $L>0$ (in the proof, the lower bound of its contradiction hypothesis $F_k\ge L$, which is
not needed here): for every $t\in[L,F_0]$, $\Theta$ has derivative $1+r\Phi''(r)/\Phi'(r)$ at
$t$ with $r=\Phi^{-1}(t)$ ($\Phi''$ is `deriv (deriv Φ)`), and this derivative is bounded on
$[L,F_0]$. -/
theorem transform_theta_derivative {n : ℕ} (γ : Vec n → ℝ) (_hγ : ConvexOn ℝ univ γ)
    (_hγh : Homogeneous.PositiveDegreeOne γ) (_hγc : Tendsto γ (cocompact (Vec n)) atTop)
    (Φ : ℝ → ℝ) (hΦc : ContinuousOn Φ (Ici 0)) (hΦv : ConvexOn ℝ (Ici 0) Φ)
    (hΦm : StrictMonoOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0) (hΦ2 : ContDiffOn ℝ 2 Φ (Ioi 0))
    (hΦ' : ∀ r, 0 < r → 0 < deriv Φ r)
    (xstar : Vec n) (F : Vec n → ℝ) (_hF : ∀ x, F x = Φ (γ (x - xstar)))
    (R : AdmissibleBFGSRun n F) (L : ℝ) (hL : 0 < L)
    (Φinv : ℝ → ℝ) (hΦinv : ∀ t, 0 ≤ t → 0 ≤ Φinv t ∧ Φ (Φinv t) = t)
    (Θ : ℝ → ℝ) (hΘ : ∀ t, Θ t = Φinv t * deriv Φ (Φinv t)) :
    (∀ t ∈ Icc L (F (R.x 0)),
      HasDerivAt Θ (1 + Φinv t * deriv (deriv Φ) (Φinv t) / deriv Φ (Φinv t)) t) ∧
      ∃ C : ℝ, ∀ t ∈ Icc L (F (R.x 0)),
        |1 + Φinv t * deriv (deriv Φ) (Φinv t) / deriv Φ (Φinv t)| ≤ C := by
  have hT : TransformedGauge.IncreasingTransform Φ := ⟨hΦc, hΦv, hΦm, hΦ0, hΦ2, hΦ'⟩
  have hinv := (transform_inverse Φ hT).2 Φinv hΦinv
  -- near a positive `t`, `Θ` is the library's `theta Φ`
  have hloc : ∀ t, 0 < t → Θ =ᶠ[𝓝 t] TransformedGauge.theta Φ := by
    intro t ht
    filter_upwards [eventually_gt_nhds ht] with s hs
    rw [hΘ, TransformedGauge.theta, hinv s hs.le]
  have hder : ∀ t, 0 < t →
      HasDerivAt Θ (1 + Φinv t * deriv (deriv Φ) (Φinv t) / deriv Φ (Φinv t)) t := by
    intro t ht
    rw [hinv t ht.le]
    exact (TransformedGauge.theta_hasDerivAt hT ht).congr_of_eventuallyEq (hloc t ht)
  refine ⟨fun t ht => hder t (hL.trans_le ht.1), ?_⟩
  obtain ⟨C, -, hC⟩ := TransformedGauge.theta_derivative_bounded (b := F (R.x 0)) hT hL
  refine ⟨C, fun t ht => ?_⟩
  have ht0 : 0 < t := hL.trans_le ht.1
  have he : deriv (TransformedGauge.theta Φ) t =
      1 + Φinv t * deriv (deriv Φ) (Φinv t) / deriv Φ (Φinv t) := by
    rw [hinv t ht0.le]
    exact (TransformedGauge.theta_hasDerivAt hT ht0).deriv
  rw [← he]
  exact hC t ht

/-- Item `C/06_F/disp/005` (`companion/chapters/06_F.tex:51-53`), in the proof of Theorem
`F:transform`: "Since $y_k^Tx_{k+1}=d_k+a_{k+1}-a_k$", with $a_k=g_k^Tx_k$ after the translation
$x_*=0$ (so $x_k$ is $x_k-x_*$). Under the hypotheses of `transform_euler`, for every admissible
run and every $k$ (without the proof's contradiction hypothesis; the hypotheses on $\gamma$,
$\Phi$ are not used: the identity holds for every run and every reference point). -/
theorem transform_secant_pairing {n : ℕ} (γ : Vec n → ℝ) (_hγ : ConvexOn ℝ univ γ)
    (_hγh : Homogeneous.PositiveDegreeOne γ) (_hγc : Tendsto γ (cocompact (Vec n)) atTop)
    (Φ : ℝ → ℝ) (_hΦc : ContinuousOn Φ (Ici 0)) (_hΦv : ConvexOn ℝ (Ici 0) Φ)
    (_hΦm : StrictMonoOn Φ (Ici 0)) (_hΦ0 : Φ 0 = 0) (_hΦ2 : ContDiffOn ℝ 2 Φ (Ioi 0))
    (_hΦ' : ∀ r, 0 < r → 0 < deriv Φ r)
    (xstar : Vec n) (F : Vec n → ℝ) (_hF : ∀ x, F x = Φ (γ (x - xstar)))
    (R : AdmissibleBFGSRun n F)
    (a : ℕ → ℝ) (ha : ∀ k, a k = dot (R.g k) (R.x k - xstar)) (k : ℕ) :
    dot (R.gradientChange k) (R.x (k + 1) - xstar) = R.d k + a (k + 1) - a k := by
  have hstep : R.x (k + 1) - xstar = (R.x k - xstar) + R.displacement k := by
    rw [displacement_eq]; abel
  have hd : dot (R.g k) (R.displacement k) = -R.d k := R.dot_step_eq_neg_d k
  have hadd : dot (R.g k) (R.x (k + 1) - xstar) =
      dot (R.g k) (R.x k - xstar) + dot (R.g k) (R.displacement k) := by
    rw [hstep]; exact dotProduct_add _ _ _
  rw [ha, ha, AdmissibleBFGSRun.gradientChange, dot_sub_left, hadd, hd]
  ring

/-- Item `C/06_F/disp/006` (`companion/chapters/06_F.tex:55-57`), in the proof of Theorem
`F:transform`: "Thus $|a_{k+1}-a_k|\le C\Delta_k$. Since [disp/005], \eqref{M:basic} implies
\[ R_k\le\frac{(1+C)^2}{(1-c_2)c_1}\Delta_k. \]"

Under the hypotheses of `transform_euler`, with $L>0$ and $C\ge0$ a Lipschitz constant of
$\Theta$ on $[L,F_0]$ (which the bounded derivative of display `disp/004` supplies), for every $k$
with $F(x_{k+1})\ge L$: $|a_{k+1}-a_k|\le C\Delta_k$ and the displayed bound, with
$R_k=(y_k^T(x_{k+1}-x_*))^2/t_k$ and $\Delta_k=F(x_k)-F(x_{k+1})$. The proof's contradiction
hypothesis ($F_k\ge L$ for all $k$) is weakened to this pointwise one, which holds for instance
with $L=F(x_{k+1})>0$ (`example` at the end). -/
theorem transform_correction {n : ℕ} (γ : Vec n → ℝ) (hγ : ConvexOn ℝ univ γ)
    (hγh : Homogeneous.PositiveDegreeOne γ) (hγc : Tendsto γ (cocompact (Vec n)) atTop)
    (Φ : ℝ → ℝ) (hΦc : ContinuousOn Φ (Ici 0)) (hΦv : ConvexOn ℝ (Ici 0) Φ)
    (hΦm : StrictMonoOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0) (hΦ2 : ContDiffOn ℝ 2 Φ (Ioi 0))
    (hΦ' : ∀ r, 0 < r → 0 < deriv Φ r)
    (xstar : Vec n) (F : Vec n → ℝ) (hF : ∀ x, F x = Φ (γ (x - xstar)))
    (R : AdmissibleBFGSRun n F) (L : ℝ) (_hL : 0 < L)
    (Φinv : ℝ → ℝ) (hΦinv : ∀ t, 0 ≤ t → 0 ≤ Φinv t ∧ Φ (Φinv t) = t)
    (Θ : ℝ → ℝ) (hΘ : ∀ t, Θ t = Φinv t * deriv Φ (Φinv t))
    (a : ℕ → ℝ) (ha : ∀ k, a k = dot (R.g k) (R.x k - xstar))
    (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ t ∈ Icc L (F (R.x 0)), ∀ u ∈ Icc L (F (R.x 0)), |Θ u - Θ t| ≤ C * |u - t|)
    (k : ℕ) (hLk : L ≤ F (R.x (k + 1))) :
    |a (k + 1) - a k| ≤ C * (F (R.x k) - F (R.x (k + 1))) ∧
      dot (R.gradientChange k) (R.x (k + 1) - xstar) ^ 2 / R.curvature k ≤
        (1 + C) ^ 2 / ((1 - R.c₂) * R.c₁) * (F (R.x k) - F (R.x (k + 1))) := by
  have heul : ∀ j, a j = Θ (F (R.x j)) := fun j => by
    obtain ⟨h1, h2⟩ := transform_euler γ hγ hγh hγc Φ hΦc hΦv hΦm hΦ0 hΦ2 hΦ' xstar F hF R
      Φinv hΦinv Θ hΘ a ha j
    rw [h1, h2]
  have hdec := R.objective_strict_decrease k
  have hmem0 : F (R.x k) ∈ Icc L (F (R.x 0)) := ⟨by linarith, R.objective_le_initial k⟩
  have hmem1 : F (R.x (k + 1)) ∈ Icc L (F (R.x 0)) := ⟨hLk, R.objective_le_initial (k + 1)⟩
  have hΔ0 : 0 ≤ F (R.x k) - F (R.x (k + 1)) := by linarith
  have hlip : |a (k + 1) - a k| ≤ C * (F (R.x k) - F (R.x (k + 1))) := by
    rw [heul, heul]
    have h := hC _ hmem0 _ hmem1
    rwa [abs_sub_comm (F (R.x (k + 1))), abs_of_nonneg hΔ0] at h
  refine ⟨hlip, ?_⟩
  have hpair := transform_secant_pairing γ hγ hγh hγc Φ hΦc hΦv hΦm hΦ0 hΦ2 hΦ' xstar F hF R
    a ha k
  have hd := R.d_pos k
  have hc1 := R.c₁_pos
  have hc2 : 0 < 1 - R.c₂ := R.wolfe_constant_pos
  have harm := R.armijo_decrease k
  have hup := R.convexity_decrease_upper k
  have ht : (1 - R.c₂) * R.d k ≤ R.curvature k := R.curvature_lower_bound k
  have htpos : 0 < R.curvature k := R.curvature_pos k
  have hnum : |dot (R.gradientChange k) (R.x (k + 1) - xstar)| ≤ (1 + C) * R.d k := by
    rw [hpair]
    calc |R.d k + a (k + 1) - a k| ≤ |R.d k| + |a (k + 1) - a k| := by
          rw [add_sub_assoc]; exact abs_add_le _ _
      _ ≤ R.d k + C * R.d k := by
          rw [abs_of_pos hd]
          exact add_le_add_left (hlip.trans (mul_le_mul_of_nonneg_left hup hC0)) _
      _ = (1 + C) * R.d k := by ring
  have hsq : dot (R.gradientChange k) (R.x (k + 1) - xstar) ^ 2 ≤ ((1 + C) * R.d k) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hnum 2
  rw [div_le_iff₀ htpos]
  have hfac : (1 + C) ^ 2 / ((1 - R.c₂) * R.c₁) * (F (R.x k) - F (R.x (k + 1))) * R.curvature k ≥
      (1 + C) ^ 2 / ((1 - R.c₂) * R.c₁) * (R.c₁ * R.d k) * ((1 - R.c₂) * R.d k) := by
    apply mul_le_mul (mul_le_mul_of_nonneg_left harm (by positivity)) ht (by positivity)
      (mul_nonneg (by positivity) hΔ0)
  have hval : (1 + C) ^ 2 / ((1 - R.c₂) * R.c₁) * (R.c₁ * R.d k) * ((1 - R.c₂) * R.d k) =
      ((1 + C) * R.d k) ^ 2 := by
    field_simp
    ring
  linarith

/-- Item `C/06_F/prose/007` (`companion/chapters/06_F.tex:60`): "The same correction estimate
can be obtained without introducing an inverse: on a compact positive gauge annulus, bound the
derivative of $r\Phi'(r)$ and bound $\Phi'$ away from zero, then apply the scalar
mean-value theorem twice."

Under the hypotheses of Theorem `F:transform`, for every admissible run and every $\eta>0$: some
$C>0$ gives $R_k\le(1+C)^2\Delta_k/((1-c_2)c_1)$ for every $k$ with $F(x_{k+1})\ge\eta$ (both
endpoints then lie in the compact positive gauge annulus $\eta\le F\le F(x_0)$). The library proves
the pairing bound by the annulus route
(`TransformedGauge.actual_pairing_variation_on_positive_band`, the derivative of $r\Phi'(r)$ and the
lower bound of $\Phi'$ on the annulus, with the mean-value theorem), and the numeric step is
`TransformedGauge.correction_numeric`. -/
theorem transform_correction_annulus {n : ℕ} (γ : Vec n → ℝ) (hγ : ConvexOn ℝ univ γ)
    (hγh : Homogeneous.PositiveDegreeOne γ) (hγc : Tendsto γ (cocompact (Vec n)) atTop)
    (Φ : ℝ → ℝ) (hΦc : ContinuousOn Φ (Ici 0)) (hΦv : ConvexOn ℝ (Ici 0) Φ)
    (hΦm : StrictMonoOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0) (hΦ2 : ContDiffOn ℝ 2 Φ (Ioi 0))
    (hΦ' : ∀ r, 0 < r → 0 < deriv Φ r)
    (xstar : Vec n) (F : Vec n → ℝ) (hF : ∀ x, F x = Φ (γ (x - xstar)))
    (R : AdmissibleBFGSRun n F) (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ k, η ≤ F (R.x (k + 1)) →
      dot (R.gradientChange k) (R.x (k + 1) - xstar) ^ 2 / R.curvature k ≤
        (1 + C) ^ 2 / ((1 - R.c₂) * R.c₁) * (F (R.x k) - F (R.x (k + 1))) := by
  have hT : TransformedGauge.IncreasingTransform Φ := ⟨hΦc, hΦv, hΦm, hΦ0, hΦ2, hΦ'⟩
  obtain rfl : F = TransformedGauge.objective Φ γ xstar := funext hF
  have hK : IsCompact R.initialSublevel :=
    TransformedGauge.objective_sublevel_compact hT hγ hγh hγc xstar _
  obtain ⟨C, hC, hbound⟩ :=
    TransformedGauge.actual_pairing_variation_on_positive_band hT hγ hγh hγc xstar hK hη
  refine ⟨C, hC, fun k hk => ?_⟩
  have hv := hbound (R.x k) (R.iterate_mem_initialSublevel k)
    (R.x (k + 1)) (R.iterate_mem_initialSublevel (k + 1)) hk
    (R.objective_antitone (Nat.le_succ k)) (R.g k) (R.g (k + 1))
    (R.hasGradient k) (R.hasGradient (k + 1))
  have h := TransformedGauge.correction_numeric (R.d_pos k) R.wolfe_constant_pos R.c₁_pos hC.le
    (R.convexity_decrease_upper k) (R.armijo_decrease k) (R.curvature_lower_bound k) hv
  have e := R.reference_new_pairing_difference xstar k
  unfold AdmissibleBFGSRun.referencePairing at e
  rw [e]
  convert h using 2

/-- $\Phi(r)=r^{3/2}$: its first derivative on $(0,\infty)$. -/
theorem rpow32_deriv : deriv (fun r : ℝ => r ^ (3 / 2 : ℝ)) =
    fun r => 3 / 2 * Real.sqrt r := by
  funext r
  rw [(Real.hasDerivAt_rpow_const (Or.inr (by norm_num : (1 : ℝ) ≤ 3 / 2))).deriv,
    Real.sqrt_eq_rpow]
  norm_num

/-- Item `C/06_F/prose/010` (`companion/chapters/06_F.tex:60`): "It includes cases whose scalar
second derivative is unbounded at zero." The transform $\Phi(r)=r^{3/2}$ satisfies every
hypothesis of Theorem `F:transform`, and $\Phi''$ is unbounded on every interval $(0,\delta)$. -/
theorem transform_unbounded_second_derivative :
    ∃ Φ : ℝ → ℝ, ContinuousOn Φ (Ici 0) ∧ ConvexOn ℝ (Ici 0) Φ ∧ StrictMonoOn Φ (Ici 0) ∧
      Φ 0 = 0 ∧ ContDiffOn ℝ 2 Φ (Ioi 0) ∧ (∀ r, 0 < r → 0 < deriv Φ r) ∧
      ∀ δ : ℝ, 0 < δ → ¬ BddAbove (deriv (deriv Φ) '' Ioo 0 δ) := by
  refine ⟨fun r => r ^ (3 / 2 : ℝ), (Real.continuous_rpow_const (by norm_num)).continuousOn,
    convexOn_rpow (by norm_num), Real.strictMonoOn_rpow_Ici_of_exponent_pos (by norm_num),
    Real.zero_rpow (by norm_num), fun r hr =>
      (Real.contDiffAt_rpow_const_of_ne (ne_of_gt hr)).contDiffWithinAt, ?_, ?_⟩
  · intro r hr
    rw [rpow32_deriv]
    positivity
  · intro δ hδ hbdd
    obtain ⟨M, hM⟩ := hbdd
    have hdd : ∀ r, 0 < r → deriv (deriv (fun r : ℝ => r ^ (3 / 2 : ℝ))) r =
        3 / 2 * (1 / (2 * Real.sqrt r)) := by
      intro r hr
      rw [rpow32_deriv]
      exact ((Real.hasDerivAt_sqrt (ne_of_gt hr)).const_mul (3 / 2)).deriv
    set ε : ℝ := min (Real.sqrt (δ / 2)) (1 / (2 * (|M| + 1))) with hε
    have hε0 : 0 < ε := lt_min (Real.sqrt_pos.mpr (by linarith)) (by positivity)
    have hr0 : 0 < ε ^ 2 := by positivity
    have hrδ : ε ^ 2 < δ := by
      have h1 : ε ≤ Real.sqrt (δ / 2) := min_le_left _ _
      have h2 : ε ^ 2 ≤ δ / 2 := by
        calc ε ^ 2 ≤ Real.sqrt (δ / 2) ^ 2 := pow_le_pow_left₀ hε0.le h1 2
          _ = δ / 2 := Real.sq_sqrt (by linarith)
      linarith
    have hval := hM ⟨ε ^ 2, ⟨hr0, hrδ⟩, rfl⟩
    rw [hdd _ hr0, Real.sqrt_sq hε0.le] at hval
    have hεM : ε ≤ 1 / (2 * (|M| + 1)) := min_le_right _ _
    have hkey : 2 * (|M| + 1) ≤ 1 / ε := by
      rw [le_div_iff₀ hε0]
      rw [le_div_iff₀ (by positivity)] at hεM
      linarith
    have hexp : 3 / 2 * (1 / (2 * ε)) = 3 / 4 * (1 / ε) := by field_simp; ring
    rw [hexp] at hval
    have := le_abs_self M
    have := abs_nonneg M
    nlinarith

/-- Item `C/06_F/prose/011` (`companion/chapters/06_F.tex:60`): "Finite sums of differently
powered gauges are instead covered by the radial argument in Chapter~\ref{comp:R}, including
$1<p<2$." For $F(x)=\psi(x)+\sum_j\gamma_j(A_j(x-x_*))^{p_j}$ on an open $U$ with $\psi$ locally
$C^{1,1}$, nonnegative finite convex positively homogeneous $\gamma_j$, linear $A_j$ and powers
$p_j\ge1$ (so $1<p_j<2$ is allowed), $x_*$ a minimizer, and a run whose initial sublevel is
compact and contained in $U$: value convergence, distance convergence and, under uniqueness,
iterate convergence (library `AdmissibleBFGSRun.mixed_linear_powers_convergence`, the radial
argument of Chapter~\ref{comp:R}). -/
theorem powered_gauges_covered {n : ℕ} {ι : Type*} [Fintype ι] {m : ι → ℕ}
    {F ψ : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (γ : ∀ j, Vec (m j) → ℝ)
    (hγ : ∀ j, ConvexOn ℝ univ (γ j)) (hh : ∀ j, Homogeneous.PositiveDegreeOne (γ j))
    (hn : ∀ j x, 0 ≤ γ j x) (A : ∀ j, Vec n →ₗ[ℝ] Vec (m j))
    (p : ι → ℝ) (hp : ∀ j, 1 ≤ p j) (xstar : Vec n) (hmin : ∀ x, F xstar ≤ F x)
    (U : Set (Vec n)) (hU : IsOpen U) (hψ : CenteredSmoothSublinear.LocallyC11On U ψ)
    (hK : IsCompact {x | F x ≤ F (R.x 0)}) (hKU : {x | F x ≤ F (R.x 0)} ⊆ U)
    (hrep : ∀ x ∈ U, F x = ψ x + ∑ j, (γ j (A j (x - xstar))) ^ (p j)) :
    Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) ∧
      Tendsto (fun k => euclideanSolutionDistance F (R.x k)) atTop (𝓝 0) ∧
      ((∀ x, F x = F xstar → x = xstar) → Tendsto R.x atTop (𝓝 xstar)) :=
  R.mixed_linear_powers_convergence γ hγ hh hn A p hp xstar hmin hU hψ hK hKU hrep

/-! ### Finite max-affine terms and the certified basin (`06_F.tex:66-89`) -/

/-- The finite maximum $p(x)=\max_i(a_i^Tx+b_i)$, written as `IsGreatest` of the values, is the
library's `MaxAffine.Family.objective`. -/
theorem family_objective_eq {n m : ℕ} (a : Fin m → Vec n) (b : Fin m → ℝ) (hm : Nonempty (Fin m))
    (p : Vec n → ℝ) (hp : ∀ x, IsGreatest (Set.range fun i => dot (a i) x + b i) (p x)) :
    (⟨a, b, hm⟩ : MaxAffine.Family n m).objective = p := by
  funext x
  apply IsGreatest.unique _ (hp x)
  refine ⟨?_, ?_⟩
  · obtain ⟨i, hi⟩ := (⟨a, b, hm⟩ : MaxAffine.Family n m).exists_active x
    exact ⟨i, hi⟩
  · rintro _ ⟨i, rfl⟩
    exact (⟨a, b, hm⟩ : MaxAffine.Family n m).branch_le i x

/-- The active index set $I_*$ is the library's `activeIndices`. -/
theorem family_activeIndices_eq {n m : ℕ} (a : Fin m → Vec n) (b : Fin m → ℝ)
    (hm : Nonempty (Fin m)) (p : Vec n → ℝ)
    (hp : ∀ x, IsGreatest (Set.range fun i => dot (a i) x + b i) (p x))
    (xstar : Vec n) (I : Finset (Fin m)) (hI : ∀ i, i ∈ I ↔ dot (a i) xstar + b i = p xstar) :
    (⟨a, b, hm⟩ : MaxAffine.Family n m).activeIndices xstar = I := by
  have hobj := family_objective_eq a b hm p hp
  ext i
  simp only [MaxAffine.Family.activeIndices, Finset.mem_filter, Finset.mem_univ, true_and, hI]
  rw [← hobj]
  rfl

/-- The active maximum $z\mapsto\max_{i\in I_*}a_i^Tz$ is the library's `activeGauge`. -/
theorem family_activeGauge_eq {n m : ℕ} (a : Fin m → Vec n) (b : Fin m → ℝ)
    (hm : Nonempty (Fin m)) (p : Vec n → ℝ)
    (hp : ∀ x, IsGreatest (Set.range fun i => dot (a i) x + b i) (p x))
    (xstar : Vec n) (I : Finset (Fin m)) (hI : ∀ i, i ∈ I ↔ dot (a i) xstar + b i = p xstar)
    (q : Vec n → ℝ) (hq : ∀ z, IsGreatest ((fun i => dot (a i) z) '' I) (q z)) :
    (⟨a, b, hm⟩ : MaxAffine.Family n m).activeGauge xstar = q := by
  set P : MaxAffine.Family n m := ⟨a, b, hm⟩
  have hI' : P.activeIndices xstar = I := family_activeIndices_eq a b hm p hp xstar I hI
  funext z
  apply IsGreatest.unique _ (hq z)
  refine ⟨?_, ?_⟩
  · obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup' (P.activeIndices_nonempty xstar)
      (fun i => dot (P.a i) z)
    exact ⟨i, hI' ▸ hi, he.symm⟩
  · rintro _ ⟨i, hi, rfl⟩
    exact Finset.le_sup' (fun i => dot (P.a i) z) (hI' ▸ hi)

/-- Item `C/06_F/disp/007`, equation `F:active` (`companion/chapters/06_F.tex:68-70`): "Let
$F=\psi+p$, with $\psi$ convex locally $C^{1,1}$ and $p(x)=\max_i\ell_i(x)$,
$\ell_i(x)=a_i^Tx+b_i$, a finite real-valued maximum. At a unique minimizer $x_*$, put
$I_*=\{i:\ell_i(x_*)=p(x_*)\}$. Inactive pieces have positive gaps, so on a sufficiently small
ball
\[ p(x_*+z)=p(x_*)+\max_{i\in I_*}a_i^Tz. \]"

Standing assumptions (lines 67): $m\ge1$ pieces, `hp` ($p(x)$ is the greatest of the
$\ell_i(x)$), $\psi$ convex and locally $C^{1,1}$ on $\R^n$, $F=\psi+p$, $x_*$ the unique
minimizer of $F$; $I_*$ and $q(z)=\max_{i\in I_*}a_i^Tz$ are variables with their defining
equations. The ball is Euclidean. The identity itself only uses `hp` (it holds at every point). -/
theorem maxAffine_active {n m : ℕ} (a : Fin m → Vec n) (b : Fin m → ℝ) (hm : Nonempty (Fin m))
    (p : Vec n → ℝ) (hp : ∀ x, IsGreatest (Set.range fun i => dot (a i) x + b i) (p x))
    (ψ : Vec n → ℝ) (_hψ : ConvexOn ℝ univ ψ) (_hψ11 : CenteredSmoothSublinear.LocallyC11On univ ψ)
    (F : Vec n → ℝ) (_hF : ∀ x, F x = ψ x + p x)
    (xstar : Vec n) (_hmin : ∀ x, F xstar ≤ F x) (_huniq : ∀ x, F x = F xstar → x = xstar)
    (I : Finset (Fin m)) (hI : ∀ i, i ∈ I ↔ dot (a i) xstar + b i = p xstar)
    (q : Vec n → ℝ) (hq : ∀ z, IsGreatest ((fun i => dot (a i) z) '' I) (q z)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z : Vec n, ‖euclideanVector z‖ < ε → p (xstar + z) = p xstar + q z := by
  set P : MaxAffine.Family n m := ⟨a, b, hm⟩
  have hobj : P.objective = p := family_objective_eq a b hm p hp
  have hgauge : P.activeGauge xstar = q := family_activeGauge_eq a b hm p hp xstar I hI q hq
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (P.local_active_identity xstar)
  refine ⟨ε, hε, fun z hz => ?_⟩
  have hd : dist (xstar + z) xstar < ε := by
    rw [dist_eq_norm, add_sub_cancel_left]
    exact (BfgsCoverage.Article.Global.norm_le_norm_euclideanVector z).trans_lt hz
  have h := hball hd
  rw [hobj, hgauge] at h
  simpa only [add_sub_cancel_left] using h

/-- Item `C/06_F/disp/008` (`companion/chapters/06_F.tex:72-74`): "Indeed, with any fixed
$i_0\in I_*$, the difference between its value and an inactive piece $j$ is
\[ \delta_j+(a_{i_0}-a_j)^Tz,\qquad \delta_j=p(x_*)-\ell_j(x_*)>0, \]
which stays positive if $\|z\|\le\delta_j/(2\|a_{i_0}-a_j\|)$; a parallel inactive piece stays
dominated everywhere."

Under the standing assumptions of `maxAffine_active`, for $i_0\in I_*$ and $j\notin I_*$, with
$\delta_j$ a variable with its defining equation: the identity
$\ell_{i_0}(x_*+z)-\ell_j(x_*+z)=\delta_j+(a_{i_0}-a_j)^Tz$ for every $z$, $\delta_j>0$, the
positivity on the Euclidean ball when $a_{i_0}\ne a_j$, and positivity for all $z$ when
$a_{i_0}=a_j$ (the parallel case, where the radius is undefined). -/
theorem maxAffine_inactive {n m : ℕ} (a : Fin m → Vec n) (b : Fin m → ℝ) (hm : Nonempty (Fin m))
    (p : Vec n → ℝ) (hp : ∀ x, IsGreatest (Set.range fun i => dot (a i) x + b i) (p x))
    (ψ : Vec n → ℝ) (_hψ : ConvexOn ℝ univ ψ) (_hψ11 : CenteredSmoothSublinear.LocallyC11On univ ψ)
    (F : Vec n → ℝ) (_hF : ∀ x, F x = ψ x + p x)
    (xstar : Vec n) (_hmin : ∀ x, F xstar ≤ F x) (_huniq : ∀ x, F x = F xstar → x = xstar)
    (I : Finset (Fin m)) (hI : ∀ i, i ∈ I ↔ dot (a i) xstar + b i = p xstar)
    (i₀ j : Fin m) (hi₀ : i₀ ∈ I) (hj : j ∉ I)
    (δ : ℝ) (hδ : δ = p xstar - (dot (a j) xstar + b j)) :
    (∀ z : Vec n, (dot (a i₀) (xstar + z) + b i₀) - (dot (a j) (xstar + z) + b j) =
      δ + dot (a i₀ - a j) z) ∧ 0 < δ ∧
      (a i₀ ≠ a j → ∀ z : Vec n, ‖euclideanVector z‖ ≤ δ / (2 * ‖euclideanVector (a i₀ - a j)‖) →
        0 < δ + dot (a i₀ - a j) z) ∧
      (a i₀ = a j → ∀ z : Vec n, 0 < δ + dot (a i₀ - a j) z) := by
  set P : MaxAffine.Family n m := ⟨a, b, hm⟩
  have hobj : P.objective = p := family_objective_eq a b hm p hp
  have hact : P.activeIndices xstar = I := family_activeIndices_eq a b hm p hp xstar I hI
  have hi₀' : i₀ ∈ P.activeIndices xstar := hact ▸ hi₀
  have hj' : j ∉ P.activeIndices xstar := hact ▸ hj
  have hgap := P.inactive_gap_pos xstar hj'
  have hδ' : δ = P.objective xstar - P.branch j xstar := by rw [hδ, hobj]; rfl
  have hid : ∀ z : Vec n, (dot (a i₀) (xstar + z) + b i₀) - (dot (a j) (xstar + z) + b j) =
      δ + dot (a i₀ - a j) z := by
    intro z
    have h1 := P.branch_translate i₀ xstar z
    have h2 := P.branch_translate j xstar z
    have hv : P.branch i₀ xstar = P.objective xstar := (Finset.mem_filter.mp hi₀').2
    change dot (a i₀) (xstar + z) + b i₀ = P.branch i₀ xstar + dot (a i₀) z at h1
    change dot (a j) (xstar + z) + b j = P.branch j xstar + dot (a j) z at h2
    rw [h1, h2, hδ', hv, dot_sub_left]
    ring
  refine ⟨hid, hδ' ▸ hgap, fun hne z hz => ?_, fun heq z => ?_⟩
  · have h := P.inactive_radius_domination xstar z hi₀' hj' hne (by rw [← hδ']; exact hz)
    have h' := hid z
    change dot (a j) (xstar + z) + b j < dot (a i₀) (xstar + z) + b i₀ at h
    linarith
  · have h := P.parallel_inactive_domination xstar z hi₀' hj' heq
    have h' := hid z
    change dot (a j) (xstar + z) + b j < dot (a i₀) (xstar + z) + b i₀ at h
    linarith

/-- The objective $F=\psi+p$ is the library's `fun x => ψ x + P.objective x`. -/
theorem maxAffine_objective_eq {n m : ℕ} (a : Fin m → Vec n) (b : Fin m → ℝ)
    (hm : Nonempty (Fin m)) (p : Vec n → ℝ)
    (hp : ∀ x, IsGreatest (Set.range fun i => dot (a i) x + b i) (p x))
    (ψ F : Vec n → ℝ) (hF : ∀ x, F x = ψ x + p x) :
    F = fun x => ψ x + (⟨a, b, hm⟩ : MaxAffine.Family n m).objective x := by
  funext x
  rw [hF, family_objective_eq a b hm p hp]

/-- Item `C/06_F/prose/013` (`companion/chapters/06_F.tex:75`): "This exact local identity and
Theorem~\ref{F:centered} prove local convergence without strict complementarity or Hessian
nondegeneracy."

Under the standing assumptions of `maxAffine_active` (no complementarity or second-order
hypothesis): some $\delta>0$, chosen before the run and its initial matrix, gives
$F(x_k)\to F(x_*)$ and $x_k\to x_*$ for every admissible run with $F(x_0)\le F(x_*)+\delta$
(library `MaxAffine.Family.local_basin`, through the centered theorem). -/
theorem maxAffine_local_basin {n m : ℕ} (a : Fin m → Vec n) (b : Fin m → ℝ)
    (hm : Nonempty (Fin m)) (p : Vec n → ℝ)
    (hp : ∀ x, IsGreatest (Set.range fun i => dot (a i) x + b i) (p x))
    (ψ : Vec n → ℝ) (hψ : ConvexOn ℝ univ ψ) (hψ11 : CenteredSmoothSublinear.LocallyC11On univ ψ)
    (F : Vec n → ℝ) (hF : ∀ x, F x = ψ x + p x)
    (xstar : Vec n) (hmin : ∀ x, F xstar ≤ F x) (huniq : ∀ x, F x = F xstar → x = xstar) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ R : AdmissibleBFGSRun n F, F (R.x 0) ≤ F xstar + δ →
      Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) ∧ Tendsto R.x atTop (𝓝 xstar) := by
  have hFe := maxAffine_objective_eq a b hm p hp ψ F hF
  subst hFe
  exact MaxAffine.Family.local_basin _ hψ hψ11 xstar hmin huniq

/-- Item `C/06_F/disp/009` (`companion/chapters/06_F.tex:78-81`): "For an explicit sufficient
level, define the closed active region
\[ P_j=\{x:\ell_j(x)=p(x)\}=\{x:(a_j-a_i)^Tx\ge b_i-b_j\ \forall i\}." \]
The display defines $P_j$ (a variable with its defining equation, the first set) and asserts the
equality of the two sets. It only uses `hp`. -/
theorem maxAffine_active_region {n m : ℕ} (a : Fin m → Vec n) (b : Fin m → ℝ)
    (p : Vec n → ℝ) (hp : ∀ x, IsGreatest (Set.range fun i => dot (a i) x + b i) (p x))
    (j : Fin m) (Pj : Set (Vec n)) (hPj : Pj = {x | dot (a j) x + b j = p x}) :
    Pj = {x | ∀ i, b i - b j ≤ dot (a j - a i) x} := by
  subst hPj
  ext x
  simp only [mem_setOf_eq, dot_sub_left]
  constructor
  · intro h i
    have := (hp x).2 ⟨i, rfl⟩
    simp only at this
    linarith
  · intro h
    obtain ⟨i, hi⟩ := (hp x).1
    apply le_antisymm ((hp x).2 ⟨j, rfl⟩)
    rw [← hi]
    have := h i
    simp only
    linarith

/-- Item `C/06_F/disp/010`, equation `F:basin` (`companion/chapters/06_F.tex:83-85`): the
threshold
\[ \tau_*=\min_{j\notin I_*}\inf_{x\in P_j}F(x), \]
"with empty infima or minima equal to $+\infty$." In `EReal`, $\tau_*$ (the variable `τ` with its
defining equation) is the infimum over the inactive indices of the infima of $F$ over $P_j$.
This theorem unfolds it: it is the library's `MaxAffine.Family.threshold` (the infimum of $F$ over
the union of the $P_j$, $j\notin I_*$); an empty $P_j$ has infimum $+\infty$; if no index is
inactive, $\tau_*=+\infty$; otherwise the minimum is attained at an inactive index. -/
theorem maxAffine_threshold_def {n m : ℕ} (a : Fin m → Vec n) (b : Fin m → ℝ)
    (hm : Nonempty (Fin m)) (p : Vec n → ℝ)
    (hp : ∀ x, IsGreatest (Set.range fun i => dot (a i) x + b i) (p x))
    (F : Vec n → ℝ) (xstar : Vec n)
    (I : Finset (Fin m)) (hI : ∀ i, i ∈ I ↔ dot (a i) xstar + b i = p xstar)
    (τ : EReal) (hτ : τ = ⨅ j : {j : Fin m // j ∉ I},
      sInf ((fun x => (F x : EReal)) '' {x | dot (a j.1) x + b j.1 = p x})) :
    τ = (⟨a, b, hm⟩ : MaxAffine.Family n m).threshold F xstar ∧
      (∀ j : Fin m, {x | dot (a j) x + b j = p x} = ∅ →
        sInf ((fun x => (F x : EReal)) '' {x | dot (a j) x + b j = p x}) = ⊤) ∧
      ((∀ j, j ∈ I) → τ = ⊤) ∧
      ((∃ j, j ∉ I) → ∃ j : {j : Fin m // j ∉ I},
        τ = sInf ((fun x => (F x : EReal)) '' {x | dot (a j.1) x + b j.1 = p x})) := by
  set P : MaxAffine.Family n m := ⟨a, b, hm⟩
  have hobj : P.objective = p := family_objective_eq a b hm p hp
  have hact : P.activeIndices xstar = I := family_activeIndices_eq a b hm p hp xstar I hI
  have hreg : ∀ j, P.activeRegion j = {x | dot (a j) x + b j = p x} := by
    intro j
    ext x
    simp only [MaxAffine.Family.activeRegion, mem_setOf_eq, hobj]
    rfl
  refine ⟨?_, fun j hj => by rw [hj]; simp, fun hall => ?_, fun ⟨j, hj⟩ => ?_⟩
  · rw [hτ, P.threshold_eq_inactive_infima F xstar]
    rw [hact]
    simp only [hreg]
  · rw [hτ]
    haveI : IsEmpty {j : Fin m // j ∉ I} := ⟨fun j => j.2 (hall j.1)⟩
    exact iInf_of_empty _
  · haveI : Nonempty {j : Fin m // j ∉ I} := ⟨⟨j, hj⟩⟩
    obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := fun j : {j : Fin m // j ∉ I} =>
      sInf ((fun x => (F x : EReal)) '' {x | dot (a j.1) x + b j.1 = p x}))
    exact ⟨i, by rw [hτ, ← hi]⟩

/-- The threshold of display `disp/010` is the library's `threshold`. -/
theorem threshold_eq_library {n m : ℕ} (a : Fin m → Vec n) (b : Fin m → ℝ)
    (hm : Nonempty (Fin m)) (p : Vec n → ℝ)
    (hp : ∀ x, IsGreatest (Set.range fun i => dot (a i) x + b i) (p x))
    (F : Vec n → ℝ) (xstar : Vec n)
    (I : Finset (Fin m)) (hI : ∀ i, i ∈ I ↔ dot (a i) xstar + b i = p xstar)
    (τ : EReal) (hτ : τ = ⨅ j : {j : Fin m // j ∉ I},
      sInf ((fun x => (F x : EReal)) '' {x | dot (a j.1) x + b j.1 = p x})) :
    τ = (⟨a, b, hm⟩ : MaxAffine.Family n m).threshold F xstar :=
  (maxAffine_threshold_def a b hm p hp F xstar I hI τ hτ).1

/-- Item `C/06_F/prose/015` (`companion/chapters/06_F.tex:86`): "Then $\tau_*>F_*$."
Under the standing assumptions of `maxAffine_active` ($F_*=F(x_*)$), with $\tau_*$ as in
display `disp/010`. -/
theorem maxAffine_threshold_gt {n m : ℕ} (a : Fin m → Vec n) (b : Fin m → ℝ)
    (hm : Nonempty (Fin m)) (p : Vec n → ℝ)
    (hp : ∀ x, IsGreatest (Set.range fun i => dot (a i) x + b i) (p x))
    (ψ : Vec n → ℝ) (hψ : ConvexOn ℝ univ ψ) (_hψ11 : CenteredSmoothSublinear.LocallyC11On univ ψ)
    (F : Vec n → ℝ) (hF : ∀ x, F x = ψ x + p x)
    (xstar : Vec n) (hmin : ∀ x, F xstar ≤ F x) (huniq : ∀ x, F x = F xstar → x = xstar)
    (I : Finset (Fin m)) (hI : ∀ i, i ∈ I ↔ dot (a i) xstar + b i = p xstar)
    (τ : EReal) (hτ : τ = ⨅ j : {j : Fin m // j ∉ I},
      sInf ((fun x => (F x : EReal)) '' {x | dot (a j.1) x + b j.1 = p x})) :
    (F xstar : EReal) < τ := by
  rw [threshold_eq_library a b hm p hp F xstar I hI τ hτ]
  have hFe := maxAffine_objective_eq a b hm p hp ψ F hF
  have hconv : ConvexOn ℝ univ F := hFe ▸ hψ.add (MaxAffine.Family.objective_convex _)
  exact MaxAffine.Family.threshold_gt_minimum _ hconv xstar hmin huniq

/-- Item `C/06_F/prose/016` (`companion/chapters/06_F.tex:86`): "To prove it, note that
unique-minimizer convexity gives compact sublevels; a finite infimum on a nonempty closed $P_j$ is
attained. It cannot equal $F_*$ because $x_*\notin P_j$. Finitely many inactive pieces preserve
the strict gap."

Under the standing assumptions of `maxAffine_active`: all sublevels of $F$ are compact; every
$P_j$ is closed; on a nonempty $P_j$ the infimum of $F$ is attained (a minimum); $x_*\notin P_j$
for $j\notin I_*$; hence every inner infimum exceeds $F_*$ (and so does their finite minimum,
`maxAffine_threshold_gt`). -/
theorem maxAffine_threshold_steps {n m : ℕ} (a : Fin m → Vec n) (b : Fin m → ℝ)
    (hm : Nonempty (Fin m)) (p : Vec n → ℝ)
    (hp : ∀ x, IsGreatest (Set.range fun i => dot (a i) x + b i) (p x))
    (ψ : Vec n → ℝ) (hψ : ConvexOn ℝ univ ψ) (_hψ11 : CenteredSmoothSublinear.LocallyC11On univ ψ)
    (F : Vec n → ℝ) (hF : ∀ x, F x = ψ x + p x)
    (xstar : Vec n) (hmin : ∀ x, F xstar ≤ F x) (huniq : ∀ x, F x = F xstar → x = xstar)
    (I : Finset (Fin m)) (hI : ∀ i, i ∈ I ↔ dot (a i) xstar + b i = p xstar) :
    (∀ c : ℝ, IsCompact {x | F x ≤ c}) ∧
      (∀ j, IsClosed {x | dot (a j) x + b j = p x}) ∧
      (∀ j, {x | dot (a j) x + b j = p x}.Nonempty → ∃ z ∈ {x | dot (a j) x + b j = p x},
        sInf ((fun x => (F x : EReal)) '' {x | dot (a j) x + b j = p x}) = (F z : EReal)) ∧
      (∀ j, j ∉ I → xstar ∉ {x | dot (a j) x + b j = p x}) ∧
      (∀ j, j ∉ I → (F xstar : EReal) < sInf ((fun x => (F x : EReal)) ''
        {x | dot (a j) x + b j = p x})) := by
  set P : MaxAffine.Family n m := ⟨a, b, hm⟩
  have hobj : P.objective = p := family_objective_eq a b hm p hp
  have hFe : F = fun x => ψ x + P.objective x := maxAffine_objective_eq a b hm p hp ψ F hF
  have hconv : ConvexOn ℝ univ F := hFe ▸ hψ.add P.objective_convex
  have hcomp : ∀ c : ℝ, IsCompact {x | F x ≤ c} :=
    Localization.sublevel_compact hconv xstar hmin huniq
  have hreg : ∀ j, {x | dot (a j) x + b j = p x} = P.activeRegion j := by
    intro j
    ext x
    simp only [MaxAffine.Family.activeRegion, mem_setOf_eq, hobj]
    rfl
  have hclosed : ∀ j, IsClosed {x | dot (a j) x + b j = p x} := fun j => by
    rw [hreg]; exact P.activeRegion_closed j
  have hatt : ∀ j, {x | dot (a j) x + b j = p x}.Nonempty → ∃ z ∈ {x | dot (a j) x + b j = p x},
      sInf ((fun x => (F x : EReal)) '' {x | dot (a j) x + b j = p x}) = (F z : EReal) := by
    intro j hne
    obtain ⟨z, hz, hzmin⟩ := MaxAffine.Family.exists_min_on_closed (convex_continuous hconv) hcomp
      (hclosed j) hne
    refine ⟨z, hz, le_antisymm (sInf_le (mem_image_of_mem _ hz)) ?_⟩
    apply le_sInf
    rintro _ ⟨x, hx, rfl⟩
    exact EReal.coe_le_coe_iff.mpr (hzmin x hx)
  have hnot : ∀ j, j ∉ I → xstar ∉ {x | dot (a j) x + b j = p x} := by
    intro j hj hx
    exact hj ((hI j).mpr hx)
  refine ⟨hcomp, hclosed, hatt, hnot, fun j hj => ?_⟩
  by_cases hne : {x | dot (a j) x + b j = p x}.Nonempty
  · obtain ⟨z, hz, he⟩ := hatt j hne
    rw [he]
    apply EReal.coe_lt_coe_iff.mpr
    apply lt_of_le_of_ne (hmin z)
    intro hv
    exact hnot j hj ((huniq z hv.symm) ▸ hz)
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    simp

/-- Item `C/06_F/prose/017` (`companion/chapters/06_F.tex:88`): "Every admissible run with
$F(x_0)<\tau_*$ converges." Under the standing assumptions of `maxAffine_active`, with
$\tau_*$ as in display `disp/010` (library `MaxAffine.Family.threshold_convergence`). -/
theorem maxAffine_threshold_convergence {n m : ℕ} (a : Fin m → Vec n) (b : Fin m → ℝ)
    (hm : Nonempty (Fin m)) (p : Vec n → ℝ)
    (hp : ∀ x, IsGreatest (Set.range fun i => dot (a i) x + b i) (p x))
    (ψ : Vec n → ℝ) (hψ : ConvexOn ℝ univ ψ) (hψ11 : CenteredSmoothSublinear.LocallyC11On univ ψ)
    (F : Vec n → ℝ) (hF : ∀ x, F x = ψ x + p x)
    (xstar : Vec n) (hmin : ∀ x, F xstar ≤ F x) (huniq : ∀ x, F x = F xstar → x = xstar)
    (I : Finset (Fin m)) (hI : ∀ i, i ∈ I ↔ dot (a i) xstar + b i = p xstar)
    (τ : EReal) (hτ : τ = ⨅ j : {j : Fin m // j ∉ I},
      sInf ((fun x => (F x : EReal)) '' {x | dot (a j.1) x + b j.1 = p x}))
    (R : AdmissibleBFGSRun n F) (hstart : (F (R.x 0) : EReal) < τ) :
    Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) ∧ Tendsto R.x atTop (𝓝 xstar) := by
  rw [threshold_eq_library a b hm p hp F xstar I hI τ hτ] at hstart
  have hFe := maxAffine_objective_eq a b hm p hp ψ F hF
  subst hFe
  exact MaxAffine.Family.threshold_convergence _ hψ hψ11 xstar hmin huniq R hstart

/-- Item `C/06_F/prose/018` (`companion/chapters/06_F.tex:88`): "On its full compact initial
sublevel, only indices in $I_*$ can be active, so \eqref{F:active} and the centered correction
estimate apply throughout."

Under the standing assumptions of `maxAffine_active` (with $q(z)=\max_{i\in I_*}a_i^Tz$), for a
run with $F(x_0)<\tau_*$: the initial sublevel is compact; at each of its points every active
index lies in $I_*$ and $p(x)=p(x_*)+q(x-x_*)$; and the secant corrections
$R_k=(y_k^T(x_{k+1}-x_*))^2/t_k$ are uniformly bounded (the centered estimate
$LR^2+2G_\gamma R$ of display `disp/002`, for the representation
$F=(\psi+p(x_*))+q(\cdot-x_*)$ on an open convex sublevel strictly below $\tau_*$). -/
theorem maxAffine_sublevel_active {n m : ℕ} (a : Fin m → Vec n) (b : Fin m → ℝ)
    (hm : Nonempty (Fin m)) (p : Vec n → ℝ)
    (hp : ∀ x, IsGreatest (Set.range fun i => dot (a i) x + b i) (p x))
    (ψ : Vec n → ℝ) (hψ : ConvexOn ℝ univ ψ) (hψ11 : CenteredSmoothSublinear.LocallyC11On univ ψ)
    (F : Vec n → ℝ) (hF : ∀ x, F x = ψ x + p x)
    (xstar : Vec n) (hmin : ∀ x, F xstar ≤ F x) (huniq : ∀ x, F x = F xstar → x = xstar)
    (I : Finset (Fin m)) (hI : ∀ i, i ∈ I ↔ dot (a i) xstar + b i = p xstar)
    (q : Vec n → ℝ) (hq : ∀ z, IsGreatest ((fun i => dot (a i) z) '' I) (q z))
    (τ : EReal) (hτ : τ = ⨅ j : {j : Fin m // j ∉ I},
      sInf ((fun x => (F x : EReal)) '' {x | dot (a j.1) x + b j.1 = p x}))
    (R : AdmissibleBFGSRun n F) (hstart : (F (R.x 0) : EReal) < τ) :
    IsCompact {x | F x ≤ F (R.x 0)} ∧
      (∀ x ∈ {x | F x ≤ F (R.x 0)}, (∀ i, dot (a i) x + b i = p x → i ∈ I) ∧
        p x = p xstar + q (x - xstar)) ∧
      ∃ C : ℝ, ∀ k, dot (R.gradientChange k) (R.x (k + 1) - xstar) ^ 2 / R.curvature k ≤ C := by
  set P : MaxAffine.Family n m := ⟨a, b, hm⟩
  have hobj : P.objective = p := family_objective_eq a b hm p hp
  have hact : P.activeIndices xstar = I := family_activeIndices_eq a b hm p hp xstar I hI
  have hgauge : P.activeGauge xstar = q := family_activeGauge_eq a b hm p hp xstar I hI q hq
  have hthr := threshold_eq_library a b hm p hp F xstar I hI τ hτ
  rw [hthr] at hstart
  have hFe : F = fun x => ψ x + P.objective x := maxAffine_objective_eq a b hm p hp ψ F hF
  have hconv : ConvexOn ℝ univ F := hFe ▸ hψ.add P.objective_convex
  have hK : IsCompact {x | F x ≤ F (R.x 0)} :=
    Localization.sublevel_compact hconv xstar hmin huniq _
  -- a level strictly between `F(x₀)` and the threshold
  obtain ⟨c, hc0, hct⟩ := EReal.exists_between_coe_real hstart
  have hFc : F (R.x 0) < c := EReal.coe_lt_coe_iff.mp hc0
  have hbelow : ∀ x, F x < c → x ∉ P.badRegion xstar := fun x hx =>
    P.below_threshold_not_bad ((EReal.coe_lt_coe_iff.mpr hx).trans hct)
  have hid : ∀ x, F x < c → p x = p xstar + q (x - xstar) := by
    intro x hx
    have h := P.active_identity_outside_badRegion xstar x (hbelow x hx)
    rwa [hobj, hgauge] at h
  refine ⟨hK, fun x hx => ⟨fun i hi => ?_, hid x (lt_of_le_of_lt hx hFc)⟩, ?_⟩
  · by_contra hiI
    apply hbelow x (lt_of_le_of_lt hx hFc)
    refine mem_iUnion.mpr ⟨⟨i, hact ▸ hiI⟩, ?_⟩
    change P.branch i x = P.objective x
    rw [hobj]
    exact hi
  · -- the centered representation on the open convex set `{F < c}`
    set U := {x | F x < c}
    have hU : IsOpen U := isOpen_lt (convex_continuous hconv) continuous_const
    have hUc : Convex ℝ U := by simpa only [mem_univ, true_and] using hconv.convex_lt c
    have hsub : U ⊆ univ := subset_univ _
    have hrep : ∀ x ∈ U, F x = (ψ x + p xstar) + q (x - xstar) := by
      intro x hx
      rw [hF, hid x hx]
      ring
    have hgq : ConvexOn ℝ univ q := hgauge ▸ P.activeGauge_convex xstar
    have hqh : Homogeneous.PositiveDegreeOne q := hgauge ▸ P.activeGauge_homogeneous xstar
    have hψU : ConvexOn ℝ U (fun x => ψ x + p xstar) :=
      (hψ.add_const (p xstar)).subset hsub hUc
    have hψ11U : CenteredSmoothSublinear.LocallyC11On U (fun x => ψ x + p xstar) :=
      MaxAffine.Family.locallyC11_add_const hU ⟨hψ11.1.mono hsub, hψ11.2.mono hsub⟩ _
    have hKU : R.initialSublevel ⊆ U := fun x hx => lt_of_le_of_lt hx hFc
    obtain ⟨L, G, Rr, -, -, -, hbound⟩ := R.centered_uniform_correction xstar hU hψU hψ11U hgq
      hqh hrep hK hKU
    exact ⟨L * Rr ^ 2 + 2 * G * Rr, fun k => hbound k⟩

/-- Item `C/06_F/prose/019` (`companion/chapters/06_F.tex:88`): "A tail that first enters this
sublevel enjoys the same conclusion for its current arbitrary SPD matrix." Under the standing
assumptions of `maxAffine_active`: if $F(x_J)<\tau_*$ for some $J$, then $F(x_k)\to F(x_*)$ and
$x_k\to x_*$ (library `MaxAffine.Family.threshold_tail_convergence`, with the shifted run whose
initial matrix is $H_J$). -/
theorem maxAffine_threshold_tail {n m : ℕ} (a : Fin m → Vec n) (b : Fin m → ℝ)
    (hm : Nonempty (Fin m)) (p : Vec n → ℝ)
    (hp : ∀ x, IsGreatest (Set.range fun i => dot (a i) x + b i) (p x))
    (ψ : Vec n → ℝ) (hψ : ConvexOn ℝ univ ψ) (hψ11 : CenteredSmoothSublinear.LocallyC11On univ ψ)
    (F : Vec n → ℝ) (hF : ∀ x, F x = ψ x + p x)
    (xstar : Vec n) (hmin : ∀ x, F xstar ≤ F x) (huniq : ∀ x, F x = F xstar → x = xstar)
    (I : Finset (Fin m)) (hI : ∀ i, i ∈ I ↔ dot (a i) xstar + b i = p xstar)
    (τ : EReal) (hτ : τ = ⨅ j : {j : Fin m // j ∉ I},
      sInf ((fun x => (F x : EReal)) '' {x | dot (a j.1) x + b j.1 = p x}))
    (R : AdmissibleBFGSRun n F) (J : ℕ) (hJ : (F (R.x J) : EReal) < τ) :
    Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) ∧ Tendsto R.x atTop (𝓝 xstar) := by
  rw [threshold_eq_library a b hm p hp F xstar I hI τ hτ] at hJ
  have hFe := maxAffine_objective_eq a b hm p hp ψ F hF
  subst hFe
  exact MaxAffine.Family.threshold_tail_convergence _ hψ hψ11 xstar hmin huniq R J hJ

/-- Item `C/06_F/prose/021` (`companion/chapters/06_F.tex:88`): "Each inner infimum is a convex
program over the displayed linear inequalities." Under the standing assumptions of
`maxAffine_active`: $F$ is convex and each $P_j$ is a closed convex set, the solution set of the
linear inequalities of display `disp/009`. -/
theorem maxAffine_inner_convex {n m : ℕ} (a : Fin m → Vec n) (b : Fin m → ℝ)
    (hm : Nonempty (Fin m)) (p : Vec n → ℝ)
    (hp : ∀ x, IsGreatest (Set.range fun i => dot (a i) x + b i) (p x))
    (ψ : Vec n → ℝ) (hψ : ConvexOn ℝ univ ψ) (_hψ11 : CenteredSmoothSublinear.LocallyC11On univ ψ)
    (F : Vec n → ℝ) (hF : ∀ x, F x = ψ x + p x)
    (xstar : Vec n) (_hmin : ∀ x, F xstar ≤ F x) (_huniq : ∀ x, F x = F xstar → x = xstar)
    (j : Fin m) :
    ConvexOn ℝ univ F ∧ Convex ℝ {x | dot (a j) x + b j = p x} ∧
      IsClosed {x | dot (a j) x + b j = p x} ∧
      {x | dot (a j) x + b j = p x} = {x | ∀ i, b i - b j ≤ dot (a j - a i) x} := by
  set P : MaxAffine.Family n m := ⟨a, b, hm⟩
  have hobj : P.objective = p := family_objective_eq a b hm p hp
  have hFe := maxAffine_objective_eq a b hm p hp ψ F hF
  have hreg : {x | dot (a j) x + b j = p x} = P.activeRegion j := by
    ext x
    simp only [MaxAffine.Family.activeRegion, mem_setOf_eq, hobj]
    rfl
  refine ⟨hFe ▸ hψ.add P.objective_convex, hreg ▸ P.activeRegion_convex j,
    hreg ▸ P.activeRegion_closed j, maxAffine_active_region a b p hp j _ rfl⟩

/-! ### Residual penalties and Theorem `F:lifting` (`06_F.tex:94-111`) -/

/-- `x ↦ c^Tx - β` is continuous. -/
theorem continuous_residual {n : ℕ} (c : Vec n) (β : ℝ) :
    Continuous (fun x : Vec n => dot c x - β) := by
  have h : (fun x : Vec n => dot c x - β) = fun x => gradientFunctional c x - β := by
    funext x; rw [gradientFunctional_apply]
  rw [h]
  exact (gradientFunctional c).continuous.sub continuous_const

/-- `dot c` is linear on convex combinations. -/
theorem dot_combo {n : ℕ} (c x y : Vec n) (s t : ℝ) :
    dot c (s • x + t • y) = s * dot c x + t * dot c y := by
  change c ⬝ᵥ (s • x + t • y) = s * (c ⬝ᵥ x) + t * (c ⬝ᵥ y)
  rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]

/-- Item `C/06_F/prose/022` (`companion/chapters/06_F.tex:96`): "For a scalar affine residual
nonzero at the solution, its absolute-value or hinge term is locally affine." If
$c^Tx_*-\beta\ne0$, then on a neighborhood of $x_*$ the terms $|c^Tx-\beta|$ and
$\max\{0,c^Tx-\beta\}$ are constant multiples of the affine function $c^Tx-\beta$ (the
multipliers are $\pm1$, respectively $0$ or $1$). The point $x_*$ need not be a minimizer. -/
theorem residual_nonzero_locally_affine {n : ℕ} (c : Vec n) (β : ℝ) (xstar : Vec n)
    (h : dot c xstar - β ≠ 0) :
    ∃ U ∈ 𝓝 xstar, ∃ σ τ : ℝ, ∀ x ∈ U,
      |dot c x - β| = σ * (dot c x - β) ∧ max 0 (dot c x - β) = τ * (dot c x - β) := by
  rcases lt_or_gt_of_ne h with hneg | hpos
  · refine ⟨{x | dot c x - β < 0}, (isOpen_lt (continuous_residual c β) continuous_const).mem_nhds
      hneg, -1, 0, fun x hx => ?_⟩
    simp only [mem_setOf_eq] at hx
    rw [abs_of_neg hx, max_eq_left hx.le]
    constructor <;> ring
  · refine ⟨{x | 0 < dot c x - β}, (isOpen_lt continuous_const (continuous_residual c β)).mem_nhds
      hpos, 1, 1, fun x hx => ?_⟩
    simp only [mem_setOf_eq] at hx
    rw [abs_of_pos hx, max_eq_right hx.le]
    constructor <;> ring

/-- Item `C/06_F/prose/023` (`companion/chapters/06_F.tex:96`): "A zero optimal residual produces
a centered sublinear term." If $c^Tx_*=\beta$, then $|c^Tx-\beta|=\gamma_1(x-x_*)$ and
$\max\{0,c^Tx-\beta\}=\gamma_2(x-x_*)$ with $\gamma_1(r)=|c^Tr|$ and
$\gamma_2(r)=\max\{0,c^Tr\}$ finite, convex and positively homogeneous of degree one. -/
theorem residual_zero_centered {n : ℕ} (c : Vec n) (β : ℝ) (xstar : Vec n)
    (h : dot c xstar - β = 0) :
    (∀ x, |dot c x - β| = |dot c (x - xstar)|) ∧
      (∀ x, max 0 (dot c x - β) = max 0 (dot c (x - xstar))) ∧
      ConvexOn ℝ univ (fun r : Vec n => |dot c r|) ∧
      Homogeneous.PositiveDegreeOne (fun r : Vec n => |dot c r|) ∧
      ConvexOn ℝ univ (fun r : Vec n => max 0 (dot c r)) ∧
      Homogeneous.PositiveDegreeOne (fun r : Vec n => max 0 (dot c r)) := by
  have hsub : ∀ x, dot c (x - xstar) = dot c x - β := fun x => by
    rw [RadialCertificate.dot_sub_right]; linarith
  refine ⟨fun x => by rw [hsub], fun x => by rw [hsub], ?_, ?_, ?_, ?_⟩
  · refine ⟨convex_univ, fun x _ y _ s t hs ht _ => ?_⟩
    simp only [smul_eq_mul]
    rw [dot_combo]
    calc |s * dot c x + t * dot c y| ≤ |s * dot c x| + |t * dot c y| := abs_add_le _ _
      _ = s * |dot c x| + t * |dot c y| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg ht]
  · intro t ht r
    simp only
    rw [dot_smul_right, abs_mul, abs_of_nonneg ht]
  · refine ⟨convex_univ, fun x _ y _ s t hs ht _ => ?_⟩
    simp only [smul_eq_mul]
    rw [dot_combo]
    apply max_le
    · positivity
    · have h1 := mul_le_mul_of_nonneg_left (le_max_right 0 (dot c x)) hs
      have h2 := mul_le_mul_of_nonneg_left (le_max_right 0 (dot c y)) ht
      linarith
  · intro t ht r
    simp only
    rw [dot_smul_right]
    rcases le_total 0 (dot c r) with hr | hr
    · rw [max_eq_right hr, max_eq_right (mul_nonneg ht hr)]
    · rw [max_eq_left hr, max_eq_left (mul_nonpos_of_nonneg_of_nonpos ht hr), mul_zero]

/-- Item `C/06_F/prose/025` (`companion/chapters/06_F.tex:96`): "Finite sums with a convex locally
$C^{1,1}$ smooth part reduce to Theorem~\ref{F:centered}", for sums of absolute-value and hinge
terms. Let $F=\psi+\sum_i|a_i^Tx-b_i|+\sum_j\max\{0,c_j^Tx-d_j\}$ on an open set $U\ni x_*$, with
$F$ finite convex, $\psi$ locally $C^{1,1}$ on $U$, and $x_*$ the unique minimizer. Then some
$\varepsilon>0$, chosen before the run, gives for every admissible run with
$F(x_0)\le F(x_*)+\varepsilon$: iterates in $U$, $F(x_k)\to F(x_*)$, $x_k\to x_*$ (library
`AffineKinks.local_kink_basin`, which applies the centered theorem). For Euclidean residual
norms see `BfgsCoverage.Article.Local.euclidean_residuals_basin`. -/
theorem kink_sums_basin {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F ψ : Vec n → ℝ) (hF : ConvexOn ℝ univ F)
    (a : ι → Vec n) (b : ι → ℝ) (c : κ → Vec n) (d : κ → ℝ)
    (U : Set (Vec n)) (hU : IsOpen U) (hψ : CenteredSmoothSublinear.LocallyC11On U ψ)
    (xstar : Vec n) (hxU : xstar ∈ U)
    (hrep : ∀ x ∈ U, F x = ψ x + ∑ i, |dot (a i) x - b i| + ∑ j, max 0 (dot (c j) x - d j))
    (hmin : ∀ x, F xstar ≤ F x) (huniq : ∀ x, F x = F xstar → x = xstar) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ R : AdmissibleBFGSRun n F, F (R.x 0) ≤ F xstar + ε →
      (∀ k, R.x k ∈ U) ∧ Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) ∧
        Tendsto R.x atTop (𝓝 xstar) := by
  let P : ι ⊕ κ → AffineKinks.Kink n :=
    Sum.elim (fun i => AffineKinks.Kink.absolute (a i) (b i))
      (fun j => AffineKinks.Kink.hinge (c j) (d j))
  have hpen : ∀ x, AffineKinks.penalty P x =
      ∑ i, |dot (a i) x - b i| + ∑ j, max 0 (dot (c j) x - d j) := by
    intro x
    simp only [AffineKinks.penalty, Fintype.sum_sum_type, P, Sum.elim_inl, Sum.elim_inr,
      AffineKinks.Kink.absolute_value, AffineKinks.Kink.hinge_value]
  exact AffineKinks.local_kink_basin hF P hU hψ hxU (fun x hx => by rw [hrep x hx, hpen, add_assoc])
    hmin huniq

open scoped Matrix.L2OpNorm in
/-- $|A_{ii}|\le\|A\|_2$ for the spectral (operator) norm. -/
theorem spectral_diag_le (A : Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 2) : |A i i| ≤ ‖A‖ := by
  have h := Matrix.l2_opNorm_mulVec A (EuclideanSpace.single i 1)
  rw [EuclideanSpace.norm_single, norm_one, mul_one] at h
  refine le_trans ?_ h
  have hc := PiLp.norm_apply_le
    ((EuclideanSpace.equiv (Fin 2) ℝ).symm (A *ᵥ EuclideanSpace.single i 1)) i
  refine le_trans (le_of_eq ?_) hc
  simp [Matrix.mulVec, dotProduct, EuclideanSpace.single_apply, Pi.single_apply]

open scoped Matrix.L2OpNorm in
/-- Item `C/06_F/prose/026` (`companion/chapters/06_F.tex:96`): "For a more general gauge, local
$C^{1,1}$ smoothness at that particular nonzero residual must be checked; a spectral penalty may
fail it." The spectral norm (largest singular value) of a $2\times2$ residual, composed with the
coordinate map $x\mapsto M(x)$ of $\R^{4}$ (the library's `CenteredSpectral.objective`), is not
differentiable at a point whose residual is the nonzero matrix $I$; hence it is not locally
$C^{1,1}$ on any neighborhood of that point. (Along $t\mapsto I+t\,e_1e_1^T$ the norm is at least
$\max\{1+t,1\}$ and equals $1$ at $t=0$.) -/
theorem spectral_penalty_not_smooth :
    ∃ x₀ : Vec (2 * 2), CenteredSpectral.matrix (m := 2) (n := 2) x₀ = 1 ∧
      CenteredSpectral.matrix (m := 2) (n := 2) x₀ ≠ 0 ∧
      ¬ DifferentiableAt ℝ (CenteredSpectral.objective (m := 2) (n := 2)) x₀ ∧
      ∀ U ∈ 𝓝 x₀, ¬ CenteredSmoothSublinear.LocallyC11On U
        (CenteredSpectral.objective (m := 2) (n := 2)) := by
  obtain ⟨x₀, hx₀⟩ := CenteredSpectral.matrix_surjective (m := 2) (n := 2) 1
  obtain ⟨v, hv⟩ := CenteredSpectral.matrix_surjective (m := 2) (n := 2) !![1, 0; 0, 0]
  have hline : ∀ t : ℝ, CenteredSpectral.objective (m := 2) (n := 2) (x₀ + t • v) =
      ‖(1 : Matrix (Fin 2) (Fin 2) ℝ) + t • !![1, 0; 0, 0]‖ := by
    intro t
    change ‖CenteredSpectral.matrix (m := 2) (n := 2) (x₀ + t • v)‖ = _
    rw [CenteredSpectral.matrix_add, CenteredSpectral.matrix_smul, hx₀, hv]
  have hone : ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ = 1 := by
    have h := Matrix.l2_opNorm_conjTranspose_mul_self (1 : Matrix (Fin 2) (Fin 2) ℝ)
    rw [Matrix.conjTranspose_one, Matrix.one_mul] at h
    have hpos : 0 < ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ := norm_pos_iff.mpr one_ne_zero
    nlinarith
  have hlow : ∀ t : ℝ, 1 ≤ ‖(1 : Matrix (Fin 2) (Fin 2) ℝ) + t • !![1, 0; 0, 0]‖ ∧
      1 + t ≤ ‖(1 : Matrix (Fin 2) (Fin 2) ℝ) + t • !![1, 0; 0, 0]‖ := by
    intro t
    set A : Matrix (Fin 2) (Fin 2) ℝ := 1 + t • !![1, 0; 0, 0] with hA
    have h1 := spectral_diag_le A 1
    have h0 := spectral_diag_le A 0
    have e1 : A 1 1 = 1 := by simp [hA]
    have e0 : A 0 0 = 1 + t := by simp [hA]
    rw [e1, abs_one] at h1
    rw [e0] at h0
    exact ⟨h1, (le_abs_self _).trans h0⟩
  have hnd : ¬ DifferentiableAt ℝ (CenteredSpectral.objective (m := 2) (n := 2)) x₀ := by
    intro hd
    set g : ℝ → ℝ := fun t => CenteredSpectral.objective (m := 2) (n := 2) (x₀ + t • v)
    have hpath : HasDerivAt (fun t : ℝ => x₀ + t • v) v 0 := by
      simpa only [one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x₀
    have hg : HasDerivAt g (fderiv ℝ (CenteredSpectral.objective (m := 2) (n := 2)) x₀ v) 0 :=
      hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 hpath (by simp)
    have hg0 : g 0 = 1 := by simp only [g, hline, zero_smul, add_zero, hone]
    have hmin : IsLocalMin g 0 := Filter.Eventually.of_forall fun t => by
      show g 0 ≤ g t
      rw [hg0]
      show 1 ≤ CenteredSpectral.objective (m := 2) (n := 2) (x₀ + t • v)
      rw [hline]
      exact (hlow t).1
    have hzero := hmin.hasDerivAt_eq_zero hg
    have hslope := hg.tendsto_slope_zero_right
    have hge : 1 ≤ fderiv ℝ (CenteredSpectral.objective (m := 2) (n := 2)) x₀ v := by
      apply ge_of_tendsto hslope
      filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      simp only [zero_add, smul_eq_mul, g, hline, zero_smul, add_zero, hone]
      rw [le_inv_mul_iff₀ ht]
      linarith [(hlow t).2]
    linarith
  refine ⟨x₀, hx₀, by rw [hx₀]; exact one_ne_zero, hnd, fun U hU hC => hnd ?_⟩
  exact (hC.1 x₀ (mem_of_mem_nhds hU)).differentiableAt hU

/-- A single row $a^T$ as a $1\times n$ matrix. -/
def rowMat {n : ℕ} (a : Vec n) : Matrix (Fin 1) (Fin n) ℝ := Matrix.of fun _ k => a k

/-- The Euclidean norm of the one-row residual $a^Tx-b$ is $|a^Tx-b|$. -/
theorem rowMat_norm {n : ℕ} (a : Vec n) (b : ℝ) (x : Vec n) :
    ‖euclideanVector (rowMat a *ᵥ x - fun _ => b)‖ = |dot a x - b| := by
  have he : (rowMat a *ᵥ x - fun _ => b) = fun _ : Fin 1 => dot a x - b := by
    ext i
    simp [rowMat, Matrix.mulVec, dotProduct, dot]
  rw [he, ← Real.sqrt_sq_eq_abs, BfgsCoverage.Article.Global.norm_euclideanVector]
  congr 1
  simp [sqNorm]

/-- Item `C/06_F/prose/025` (`companion/chapters/06_F.tex:96`): "Finite sums with a convex locally
$C^{1,1}$ smooth part reduce to Theorem~\ref{F:centered}", for mixed sums of the three kinds of
terms of the paragraph. Let
$F=\ell+\sum_i|a_i^Tx-b_i|+\sum_j\max\{0,c_j^Tx-d_j\}+\sum_l\|A_lx-e_l\|$ with $\ell$ convex and
locally $C^{1,1}$ on $\R^n$, and let $x_*$ be the unique minimizer. Then there are an open
neighborhood $U$ of $x_*$ and $\varepsilon>0$, chosen before the run, such that every admissible run
with $F(x_0)\le F(x_*)+\varepsilon$ stays in $U$ and converges to $x_*$ in value and iterates. The
proof writes $\max\{0,r\}=(|r|+r)/2$, moves the affine halves into the smooth part, treats each
scalar absolute value as a one-row Euclidean residual, and applies the article's
`euclidean_residuals_basin` (which decomposes the terms as in this paragraph and applies the
centered theorem). -/
theorem residual_sums_basin {n : ℕ} {ι κ ν : Type} [Fintype ι] [Fintype κ] [Fintype ν]
    {m : ν → ℕ} (loss : Vec n → ℝ) (hloss : ConvexOn ℝ univ loss)
    (hloss_s : CenteredSmoothSublinear.LocallyC11On univ loss)
    (a : ι → Vec n) (b : ι → ℝ) (c : κ → Vec n) (d : κ → ℝ)
    (A : ∀ l, Matrix (Fin (m l)) (Fin n) ℝ) (e : ∀ l, Vec (m l)) (F : Vec n → ℝ)
    (hFdef : ∀ x, F x = loss x + ∑ i, |dot (a i) x - b i| + ∑ j, max 0 (dot (c j) x - d j) +
      ∑ l, ‖euclideanVector (A l *ᵥ x - e l)‖)
    (xstar : Vec n) (hmin : ∀ x, F xstar ≤ F x) (huniq : ∀ x, F x = F xstar → x = xstar) :
    ∃ U : Set (Vec n), IsOpen U ∧ xstar ∈ U ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ R : AdmissibleBFGSRun n F, F (R.x 0) ≤ F xstar + ε →
        (∀ k, R.x k ∈ U) ∧ Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) ∧
          Tendsto R.x atTop (𝓝 xstar) := by
  classical
  -- the smooth part absorbs the affine halves of the hinge terms
  set loss' : Vec n → ℝ := fun x => loss x + ∑ j, (dot ((1 / 2 : ℝ) • c j) x - d j / 2)
  have haff : ∀ j, ContDiff ℝ 2 (fun x : Vec n => dot ((1 / 2 : ℝ) • c j) x - d j / 2) := by
    intro j
    have h : (fun x : Vec n => dot ((1 / 2 : ℝ) • c j) x - d j / 2) =
        fun x => gradientFunctional ((1 / 2 : ℝ) • c j) x - d j / 2 := by
      funext x; rw [gradientFunctional_apply]
    rw [h]
    exact (gradientFunctional ((1 / 2 : ℝ) • c j)).contDiff.sub (contDiff_const (c := d j / 2))
  have haffc : ConvexOn ℝ univ (fun x : Vec n => ∑ j, (dot ((1 / 2 : ℝ) • c j) x - d j / 2)) := by
    refine ⟨convex_univ, fun x _ y _ s t hs ht hst => le_of_eq ?_⟩
    simp only [smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [dot_combo]
    linear_combination (d j / 2) * hst
  have hloss'c : ConvexOn ℝ univ loss' := hloss.add haffc
  have hloss's : CenteredSmoothSublinear.LocallyC11On univ loss' := by
    apply ConvexCellRadial.locallyC11_add isOpen_univ hloss_s
    exact ConvexCellRadial.contDiffOn_two_locallyC11 isOpen_univ
      (ContDiff.sum fun j _ => haff j).contDiffOn
  -- all nonsmooth terms as Euclidean residual norms indexed by `ι ⊕ κ ⊕ ν`
  let m' : ι ⊕ κ ⊕ ν → ℕ := Sum.elim (fun _ => 1) (Sum.elim (fun _ => 1) m)
  let A' : ∀ j, Matrix (Fin (m' j)) (Fin n) ℝ := fun j => match j with
    | Sum.inl i => rowMat (a i)
    | Sum.inr (Sum.inl j) => rowMat ((1 / 2 : ℝ) • c j)
    | Sum.inr (Sum.inr l) => A l
  let e' : ∀ j, Vec (m' j) := fun j => match j with
    | Sum.inl i => fun _ => b i
    | Sum.inr (Sum.inl j) => fun _ => d j / 2
    | Sum.inr (Sum.inr l) => e l
  have hsum : ∀ x, ∑ j, ‖euclideanVector (A' j *ᵥ x - e' j)‖ =
      ∑ i, |dot (a i) x - b i| + ∑ j, |dot ((1 / 2 : ℝ) • c j) x - d j / 2| +
        ∑ l, ‖euclideanVector (A l *ᵥ x - e l)‖ := by
    intro x
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    have h1 : ∀ i, ‖euclideanVector (A' (Sum.inl i) *ᵥ x - e' (Sum.inl i))‖ =
        |dot (a i) x - b i| := fun i => rowMat_norm (a i) (b i) x
    have h2 : ∀ j, ‖euclideanVector (A' (Sum.inr (Sum.inl j)) *ᵥ x - e' (Sum.inr (Sum.inl j)))‖ =
        |dot ((1 / 2 : ℝ) • c j) x - d j / 2| := fun j => rowMat_norm _ _ x
    have h3 : ∀ l, ‖euclideanVector (A' (Sum.inr (Sum.inr l)) *ᵥ x - e' (Sum.inr (Sum.inr l)))‖ =
        ‖euclideanVector (A l *ᵥ x - e l)‖ := fun l => rfl
    simp only [h1, h2, h3]
    ring
  have hF' : ∀ x, F x = loss' x + ∑ j, ‖euclideanVector (A' j *ᵥ x - e' j)‖ := by
    intro x
    rw [hFdef, hsum]
    simp only [loss']
    have hh : ∀ j, max 0 (dot (c j) x - d j) =
        |dot ((1 / 2 : ℝ) • c j) x - d j / 2| + (dot ((1 / 2 : ℝ) • c j) x - d j / 2) := by
      intro j
      have hs : dot ((1 / 2 : ℝ) • c j) x = 1 / 2 * dot (c j) x := by
        change ((1 / 2 : ℝ) • c j) ⬝ᵥ x = _
        rw [smul_dotProduct, smul_eq_mul]
        rfl
      rw [hs]
      rcases le_total 0 (dot (c j) x - d j) with h | h
      · rw [max_eq_right h, abs_of_nonneg (by linarith)]; ring
      · rw [max_eq_left h, abs_of_nonpos (by linarith)]; ring
    rw [Finset.sum_congr rfl (fun j _ => hh j), Finset.sum_add_distrib]
    ring
  exact BfgsCoverage.Article.Local.euclidean_residuals_basin loss' hloss'c hloss's A' e' F hF'
    xstar hmin huniq

/-! #### Theorem `F:lifting` -/

/-- Item `C/06_F/theorem/F:lifting`, Theorem `F:lifting` (`companion/chapters/06_F.tex:98-103`)
("Exact linear-image lifting"), with its display `C/06_F/disp/011` (lines 100-102).

"Let $A\in\mathbb R^{r\times n}$ have full row rank and $F(x)=\bar F(Ax)$. Suppose the projected
admissible run converges to a unique optimizer $z_*$ of $\bar F$, under any of the retained
sufficient hypotheses. Then
\[ x_k\to x_0+H_0A^T(AH_0A^T)^{-1}(z_*-Ax_0). \]"

Full row rank is injectivity of $A^T$ (linearly independent rows). The projected run has iterates
$z_k=Ax_k$ (it is an admissible run on $\bar F$: `lifting_steps`); its convergence to $z_*$ is the
only hypothesis used, whatever proves it, and $z_*$ is the unique minimizer of $\bar F$ (not used).
Library: `AffineProjection.projectRun_limit_lift`. -/
theorem lifting {n r : ℕ} (A : Matrix (Fin r) (Fin n) ℝ) (hA : Function.Injective Aᵀ.mulVec)
    (Fbar : Vec r → ℝ) (F : Vec n → ℝ) (hF : ∀ x, F x = Fbar (A *ᵥ x))
    (R : AdmissibleBFGSRun n F) (zstar : Vec r)
    (_hzmin : ∀ z, Fbar zstar ≤ Fbar z) (_hzuniq : ∀ z, Fbar z = Fbar zstar → z = zstar)
    (hz : Tendsto (fun k => A *ᵥ R.x k) atTop (𝓝 zstar)) :
    Tendsto R.x atTop
      (𝓝 (R.x 0 + (R.H 0 * Aᵀ * (A * R.H 0 * Aᵀ)⁻¹) *ᵥ (zstar - A *ᵥ R.x 0))) := by
  obtain rfl : F = fun x => Fbar (A *ᵥ x) := funext hF
  exact (AffineProjection.projectRun_limit_lift A hA Fbar R zstar hz).1

/-- Proof of Theorem `F:lifting`, undisplayed claims of `companion/chapters/06_F.tex:105-109`
(not a register item): "With $z_k=Ax_k$ and $\bar H_k=AH_kA^T$, projection of the inverse-BFGS
update gives exactly full BFGS on $\bar F$, with the same step lengths and line-search
comparisons. Let $S=\operatorname{range}A^T$. [...] the update gives $H_{k+1}S\subset H_kS$; both
spaces have dimension $r$, so equality holds. [...] Thus $x_k-x_0=L_0(z_k-z_0)$." Stated as: an
admissible run on $\bar F$ with iterates $Ax_k$, matrices $AH_kA^T$, the same lengths and constants;
$H_kS=H_0S$ (ranges of $H_kA^T$); and $x_k-x_0=H_0A^T(AH_0A^T)^{-1}(Ax_k-Ax_0)$. -/
theorem lifting_steps {n r : ℕ} (A : Matrix (Fin r) (Fin n) ℝ) (hA : Function.Injective Aᵀ.mulVec)
    (Fbar : Vec r → ℝ) (F : Vec n → ℝ) (hF : ∀ x, F x = Fbar (A *ᵥ x))
    (R : AdmissibleBFGSRun n F) :
    (∃ Rbar : AdmissibleBFGSRun r Fbar, (∀ k, Rbar.x k = A *ᵥ R.x k) ∧
      (∀ k, Rbar.H k = A * R.H k * Aᵀ) ∧ (∀ k, Rbar.α k = R.α k) ∧
      Rbar.c₁ = R.c₁ ∧ Rbar.c₂ = R.c₂) ∧
      (∀ k, Set.range (R.H k * Aᵀ).mulVec = Set.range (R.H 0 * Aᵀ).mulVec) ∧
      (∀ k, R.x k - R.x 0 = (R.H 0 * Aᵀ * (A * R.H 0 * Aᵀ)⁻¹) *ᵥ (A *ᵥ R.x k - A *ᵥ R.x 0)) := by
  obtain rfl : F = fun x => Fbar (A *ᵥ x) := funext hF
  refine ⟨⟨AffineProjection.projectRun A hA Fbar R, fun k => rfl, fun k => rfl, fun k => rfl,
    rfl, rfl⟩, AffineProjection.image_objective_matrix_image A hA Fbar R, fun k => ?_⟩
  have h := AffineProjection.projectRun_iterate_lift A hA Fbar R k
  rw [AffineProjection.projectRun_x] at h
  conv_lhs => rw [h]
  simp only [AffineProjection.fiberPoint, AffineProjection.lift, AffineProjection.compress,
    add_sub_cancel_left]

/-- Item `C/06_F/disp/012` (`companion/chapters/06_F.tex:106-108`), in the proof of Theorem
`F:lifting`: "All displacements lie in $H_0S$. The restriction of $A$ to that space has right
inverse
\[ L_0=H_0A^T(AH_0A^T)^{-1}." \]
Under the hypotheses of the theorem ($S=\operatorname{range}A^T$, $H_0S$ the range of
$H_0A^T$), with $L_0$ a variable with its defining equation: $AL_0=I$, $L_0$ maps into $H_0S$, and
$L_0Aw=w$ for $w\in H_0S$ (so $L_0$ inverts $A$ restricted to $H_0S$). -/
theorem lifting_right_inverse {n r : ℕ} (A : Matrix (Fin r) (Fin n) ℝ)
    (hA : Function.Injective Aᵀ.mulVec)
    (Fbar : Vec r → ℝ) (F : Vec n → ℝ) (_hF : ∀ x, F x = Fbar (A *ᵥ x))
    (R : AdmissibleBFGSRun n F) (L0 : Matrix (Fin n) (Fin r) ℝ)
    (hL0 : L0 = R.H 0 * Aᵀ * (A * R.H 0 * Aᵀ)⁻¹) :
    A * L0 = 1 ∧ (∀ z, ∃ v, L0 *ᵥ z = (R.H 0 * Aᵀ) *ᵥ v) ∧
      ∀ v, L0 *ᵥ (A *ᵥ ((R.H 0 * Aᵀ) *ᵥ v)) = (R.H 0 * Aᵀ) *ᵥ v := by
  have hpos := AffineProjection.compress_posDef A hA (R.positive_definite 0)
  have hunit : IsUnit (A * R.H 0 * Aᵀ).det := isUnit_iff_ne_zero.mpr hpos.det_pos.ne'
  refine ⟨?_, fun z => ⟨(A * R.H 0 * Aᵀ)⁻¹ *ᵥ z, ?_⟩, fun v => ?_⟩
  · rw [hL0]
    have h := AffineProjection.mul_lift A hA (R.positive_definite 0)
    simpa only [AffineProjection.lift, AffineProjection.compress] using h
  · rw [hL0, Matrix.mulVec_mulVec]
  · have hM : R.H 0 * Aᵀ * (A * R.H 0 * Aᵀ)⁻¹ * A * (R.H 0 * Aᵀ) = R.H 0 * Aᵀ := by
      calc R.H 0 * Aᵀ * (A * R.H 0 * Aᵀ)⁻¹ * A * (R.H 0 * Aᵀ)
          = R.H 0 * Aᵀ * ((A * R.H 0 * Aᵀ)⁻¹ * (A * R.H 0 * Aᵀ)) := by
            simp only [Matrix.mul_assoc]
        _ = R.H 0 * Aᵀ := by rw [Matrix.nonsing_inv_mul _ hunit, Matrix.mul_one]
    rw [hL0, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM]

/-! ### Finite-horizon rates and strengthened asymptotic corollaries (`06_F.tex:116-170`) -/

/-- Bounded gradients and a minimizer give superquadratic reciprocal growth
(Theorem `M:superquadratic`; the summability of $d_k$ follows from the lower bound). -/
theorem superquadratic_of_bounded {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (xstar : Vec n) (hmin : ∀ x, F xstar ≤ F x)
    (hbdd : ∃ G : ℝ, ∀ k, ‖euclideanVector (R.g k)‖ ≤ G) :
    Tendsto (fun N : ℕ => (∑ k ∈ Finset.range N, (R.q k)⁻¹) / (N : ℝ) ^ 2) atTop atTop :=
  BfgsCoverage.Article.Energy.superquadratic_growth R hbdd
    (R.summable_predicted_decreases_of_lower_bound (F xstar) fun k => hmin (R.x k))

/-- A compact initial sublevel gives bounded gradients. -/
theorem bounded_of_compact {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (hK : IsCompact {x | F x ≤ F (R.x 0)}) :
    ∃ G : ℝ, ∀ k, ‖euclideanVector (R.g k)‖ ≤ G := by
  obtain ⟨G, hG, hg⟩ := R.bounded_gradients_of_compact_sublevel hK
  exact ⟨G, fun k => BfgsCoverage.Article.Global.norm_le_of_sqNorm_le hG.le (hg k)⟩

/-- Real analysis: if $S_N/N^2\to\infty$ then $\sqrt N\sqrt{(E+RN)/S_N}\to0$, i.e. the bound is
$o(N^{-1/2})$. -/
theorem sqrt_bound_littleO {S : ℕ → ℝ} (hS : Tendsto (fun N : ℕ => S N / (N : ℝ) ^ 2) atTop atTop)
    (E Rb : ℝ) :
    Tendsto (fun N : ℕ => Real.sqrt N * Real.sqrt ((E + Rb * N) / S N)) atTop (𝓝 0) := by
  have hw : Tendsto (fun N : ℕ => (N : ℝ) ^ 2 / S N) atTop (𝓝 0) := by
    have h := hS.inv_tendsto_atTop
    convert h using 1
    funext N
    simp only [Pi.inv_apply, inv_div]
  have hinv : Tendsto (fun N : ℕ => ((N : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun N : ℕ => E * ((N : ℝ) ^ 2 / S N * ((N : ℝ))⁻¹) +
      Rb * ((N : ℝ) ^ 2 / S N)) atTop (𝓝 0) := by
    have := ((hw.mul hinv).const_mul E).add (hw.const_mul Rb)
    simpa using this
  have hsq := (Real.continuous_sqrt.tendsto 0).comp hlim
  rw [Real.sqrt_zero] at hsq
  apply hsq.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  simp only [Function.comp_apply]
  rw [← Real.sqrt_mul (Nat.cast_nonneg N)]
  congr 1
  by_cases hS0 : S N = 0
  · simp [hS0]
  · field_simp
    ring

/-- Item `C/06_F/prose/029` (`companion/chapters/06_F.tex:125`): "The same estimate holds for a
linear cumulative correction budget."

For an admissible run and a minimizer $x_*$ (the hypotheses of \eqref{M:energybound}), notation
$S_N=\sum_{k<N}q_k^{-1}$, $E_0=r_0^TB_0r_0$, $R_k=(y_k^Tr_{k+1})^2/t_k$, $r_k=x_k-x_*$: if
$\sum_{k<N}R_k\le\bar RN$ for every $N$, then $F(x_N)-F_*\le\sqrt{(E_0+\bar RN)/S_N}$ for $N\ge1$.
If moreover the gradients are bounded (the hypothesis of Theorem `M:superquadratic`, which
"because $S_N/N^2\to\infty$" uses; $\sum d_k<\infty$ is automatic), then $S_N/N^2\to\infty$ and the
bound is $o(N^{-1/2})$ ($\sqrt N$ times it tends to zero). -/
theorem linear_budget_rate {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (xstar : Vec n) (hmin : ∀ x, F xstar ≤ F x)
    (S : ℕ → ℝ) (hS : ∀ N, S N = ∑ k ∈ Finset.range N, (R.q k)⁻¹)
    (E0 : ℝ) (hE0 : E0 = dot (R.x 0 - xstar) ((R.H 0)⁻¹ *ᵥ (R.x 0 - xstar)))
    (Rbar : ℝ)
    (hbudget : ∀ N, ∑ k ∈ Finset.range N,
      dot (R.gradientChange k) (R.x (k + 1) - xstar) ^ 2 / R.curvature k ≤ Rbar * N) :
    (∀ N, 0 < N → F (R.x N) - F xstar ≤ Real.sqrt ((E0 + Rbar * N) / S N)) ∧
      ((∃ G : ℝ, ∀ k, ‖euclideanVector (R.g k)‖ ≤ G) →
        Tendsto (fun N : ℕ => S N / (N : ℝ) ^ 2) atTop atTop ∧
        Tendsto (fun N : ℕ => Real.sqrt N * Real.sqrt ((E0 + Rbar * N) / S N)) atTop (𝓝 0)) := by
  have hSf : S = fun N => ∑ k ∈ Finset.range N, (R.q k)⁻¹ := funext hS
  refine ⟨fun N hN => ?_, fun hbdd => ?_⟩
  · have h := R.reference_linear_budget_sqrt_bound xstar hmin Rbar hN (hbudget N)
    rw [hS, hE0]
    exact h
  · have hsup : Tendsto (fun N : ℕ => S N / (N : ℝ) ^ 2) atTop atTop := by
      rw [hSf]; exact superquadratic_of_bounded R xstar hmin hbdd
    exact ⟨hsup, sqrt_bound_littleO hsup E0 Rbar⟩

/-- Item `C/06_F/disp/013` (`companion/chapters/06_F.tex:122-124`): "Uniformly bounded reference
correction. If $R_k\le\bar R$, then \eqref{M:energybound} gives
\[ F(x_N)-F_*\le\sqrt{\frac{E_0+\bar RN}{S_N}}, \]
and along runs with bounded gradients this is $o(N^{-1/2})$, because $S_N/N^2\to\infty$."
(Wording point W24 applied on 15 October 2026; before, the display ended "$=o(N^{-1/2})$" and the
bounded gradients were implicit.)

Under the hypotheses of `linear_budget_rate` with $R_k\le\bar R$ for all $k$: the inequality for
$N\ge1$ ($S_0=0$) needs nothing more; the little-$o$ and $S_N/N^2\to\infty$ hold for runs with
bounded gradients, the hypothesis of Theorem `M:superquadratic`. -/
theorem bounded_correction_rate {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (xstar : Vec n) (hmin : ∀ x, F xstar ≤ F x)
    (S : ℕ → ℝ) (hS : ∀ N, S N = ∑ k ∈ Finset.range N, (R.q k)⁻¹)
    (E0 : ℝ) (hE0 : E0 = dot (R.x 0 - xstar) ((R.H 0)⁻¹ *ᵥ (R.x 0 - xstar)))
    (Rbar : ℝ)
    (hRbar : ∀ k, dot (R.gradientChange k) (R.x (k + 1) - xstar) ^ 2 / R.curvature k ≤ Rbar) :
    (∀ N, 0 < N → F (R.x N) - F xstar ≤ Real.sqrt ((E0 + Rbar * N) / S N)) ∧
      ((∃ G : ℝ, ∀ k, ‖euclideanVector (R.g k)‖ ≤ G) →
        Tendsto (fun N : ℕ => Real.sqrt N * Real.sqrt ((E0 + Rbar * N) / S N)) atTop (𝓝 0) ∧
        Tendsto (fun N : ℕ => S N / (N : ℝ) ^ 2) atTop atTop) := by
  have hbudget : ∀ N, ∑ k ∈ Finset.range N,
      dot (R.gradientChange k) (R.x (k + 1) - xstar) ^ 2 / R.curvature k ≤ Rbar * N := by
    intro N
    calc ∑ k ∈ Finset.range N,
          dot (R.gradientChange k) (R.x (k + 1) - xstar) ^ 2 / R.curvature k
        ≤ ∑ _k ∈ Finset.range N, Rbar := Finset.sum_le_sum fun k _ => hRbar k
      _ = Rbar * N := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
  obtain ⟨h1, h2⟩ := linear_budget_rate R xstar hmin S hS E0 hE0 Rbar hbudget
  exact ⟨h1, fun hbdd => ⟨(h2 hbdd).2, (h2 hbdd).1⟩⟩

/-- A finite convex degree-one homogeneous function bounded below is nonnegative. -/
theorem homogeneous_nonneg {n : ℕ} {F : Vec n → ℝ} (hF : Homogeneous.PositiveDegreeOne F)
    (hbelow : ∃ L : ℝ, ∀ x, L ≤ F x) (x : Vec n) : 0 ≤ F x := by
  obtain ⟨L, hL⟩ := hbelow
  by_contra hneg
  push_neg at hneg
  have ht : 0 ≤ (|L| + 1) / -F x := div_nonneg (by positivity) (by linarith)
  have h := hL (((|L| + 1) / -F x) • x)
  rw [hF _ ht x] at h
  have he : (|L| + 1) / -F x * F x = -(|L| + 1) := by
    field_simp [(by linarith : -F x ≠ 0)]
    ring
  rw [he] at h
  have := neg_abs_le L
  linarith

/-- Item `C/06_F/disp/014` (`companion/chapters/06_F.tex:129-132`): "Bounded-below degree-one
objectives. Chapter~\ref{comp:H} proves
\[ \sum_{k<N}\frac{F(x_k)^2}{q_k}\le\Phi_0,\quad
   \Phi_0=x_0^TH_0^{-1}x_0+\frac{1-c_1}{c_1}F(x_0). \]"
For every admissible run on a finite convex, positively homogeneous of degree one, bounded-below
$F$, and every $N$; $\Phi_0$ is a variable with its defining equation (library
`AdmissibleBFGSRun.homogeneous_weighted_sum_bound`, with `homogeneousPotential 0` $=\Phi_0$). -/
theorem homogeneous_weighted_sum {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (hF : Homogeneous.PositiveDegreeOne F) (hbelow : ∃ L : ℝ, ∀ x, L ≤ F x)
    (Φ0 : ℝ) (hΦ0 : Φ0 = dot (R.x 0) ((R.H 0)⁻¹ *ᵥ R.x 0) + (1 - R.c₁) / R.c₁ * F (R.x 0))
    (N : ℕ) :
    ∑ k ∈ Finset.range N, F (R.x k) ^ 2 / R.q k ≤ Φ0 := by
  have h := R.homogeneous_weighted_sum_bound hF (fun k => homogeneous_nonneg hF hbelow (R.x k)) N
  have he : R.homogeneousPotential 0 = Φ0 := by
    rw [hΦ0, AdmissibleBFGSRun.homogeneousPotential, AdmissibleBFGSRun.referenceEnergy, sub_zero]
    rfl
  rwa [he] at h

/-- Item `C/06_F/prose/031` (`companion/chapters/06_F.tex:133`): "Hence
$F(x_N)\le\sqrt{\Phi_0/S_N}=o(N^{-1})$." Under the hypotheses of `homogeneous_weighted_sum`
(gradients of a homogeneous $F$ are bounded and $\sum d_k<\infty$, so $S_N/N^2\to\infty$): for
$N\ge1$ the bound, and $N\sqrt{\Phi_0/S_N}\to0$. -/
theorem homogeneous_rate {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (hF : Homogeneous.PositiveDegreeOne F) (hbelow : ∃ L : ℝ, ∀ x, L ≤ F x)
    (Φ0 : ℝ) (hΦ0 : Φ0 = dot (R.x 0) ((R.H 0)⁻¹ *ᵥ R.x 0) + (1 - R.c₁) / R.c₁ * F (R.x 0))
    (S : ℕ → ℝ) (hS : ∀ N, S N = ∑ k ∈ Finset.range N, (R.q k)⁻¹) :
    (∀ N, 0 < N → F (R.x N) ≤ Real.sqrt (Φ0 / S N)) ∧
      Tendsto (fun N : ℕ => (N : ℝ) * Real.sqrt (Φ0 / S N)) atTop (𝓝 0) := by
  have hnn := homogeneous_nonneg hF hbelow
  have he : R.homogeneousPotential 0 = Φ0 := by
    rw [hΦ0, AdmissibleBFGSRun.homogeneousPotential, AdmissibleBFGSRun.referenceEnergy, sub_zero]
    rfl
  have hSf : S = fun N => ∑ k ∈ Finset.range N, (R.q k)⁻¹ := funext hS
  obtain ⟨G, hG, hg⟩ := R.homogeneous_global_gradient_bound hF
  have hsup : Tendsto (fun N : ℕ => S N / (N : ℝ) ^ 2) atTop atTop := by
    rw [hSf]
    exact superquadratic_of_bounded R 0 (fun x => by
      rw [Homogeneous.value_zero hF]; exact hnn x)
      ⟨G, fun k => BfgsCoverage.Article.Global.norm_le_of_sqNorm_le hG.le (hg k)⟩
  refine ⟨fun N hN => ?_, ?_⟩
  · have h := R.homogeneous_sqrt_bound_of_lower_bound hF 0 (fun k => hnn (R.x k)) hN
    rwa [he, ← hS] at h
  · have hw : Tendsto (fun N : ℕ => (N : ℝ) ^ 2 / S N) atTop (𝓝 0) := by
      convert hsup.inv_tendsto_atTop using 1
      funext N
      simp only [Pi.inv_apply, inv_div]
    have hw' := hw.const_mul Φ0
    rw [mul_zero] at hw'
    have hlim := (Real.continuous_sqrt.tendsto 0).comp hw'
    rw [Real.sqrt_zero] at hlim
    apply hlim.congr'
    filter_upwards with N
    simp only [Function.comp_apply]
    rw [show Φ0 * ((N : ℝ) ^ 2 / S N) = (N : ℝ) ^ 2 * (Φ0 / S N) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg N)]

/-- Item `C/06_F/prose/032` (`companion/chapters/06_F.tex:133`): "Coercivity gives
$F(x)\ge\mu\|x\|$ and the same order for the iterate norm." For a coercive finite convex
degree-one homogeneous $F$: some $\mu>0$ has $F(x)\ge\mu\|x\|$ (Euclidean), and
$N\|x_N\|\to0$ for every admissible run. -/
theorem homogeneous_coercive_rate {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (hF : Homogeneous.PositiveDegreeOne F) (hc : Tendsto F (cocompact (Vec n)) atTop) :
    (∃ μ : ℝ, 0 < μ ∧ ∀ x, μ * ‖euclideanVector x‖ ≤ F x) ∧
      Tendsto (fun N : ℕ => (N : ℝ) * ‖euclideanVector (R.x N)‖) atTop (𝓝 0) :=
  ⟨Homogeneous.coercive_euclidean_lower_bound R.convex hF hc,
    R.homogeneous_coercive_norm_rate hF hc⟩

/-! #### Quadratic plus coercive gauge (`06_F.tex:135-169`)

Standing assumptions: $Q\succ0$ ($m\times m$), $\gamma$ finite convex and positively homogeneous
of degree one on $\R^p$ with $\mu\|v\|\le\gamma(v)\le\Lambda\|v\|$ (Euclidean norms, $\mu>0$),
$F(u,v)=u^TQu/2+\gamma(v)$ on $\R^{m+p}$ (`QuadraticGauge.left x` is $u$, `right x` is $v$), and an
admissible run on $F$; the reference point is the minimizer $0$, $F_*=0$. -/

/-- $E_0=x_0^TH_0^{-1}x_0$ is the library's `referenceEnergy 0 0`. -/
theorem referenceEnergy_zero_eq {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) :
    R.referenceEnergy 0 0 = dot (R.x 0) ((R.H 0)⁻¹ *ᵥ R.x 0) := by
  simp only [AdmissibleBFGSRun.referenceEnergy, sub_zero]
  rfl

/-- The objective of the paragraph is the library's `QuadraticGauge.objective Q γ`. -/
theorem quadGauge_objective_eq {m p : ℕ} (Q : Mat m) (γ : Vec p → ℝ) (F : Vec (m + p) → ℝ)
    (hF : ∀ x, F x = dot (QuadraticGauge.left x) (Q *ᵥ QuadraticGauge.left x) / 2 +
      γ (QuadraticGauge.right x)) :
    F = QuadraticGauge.objective Q γ := funext fun x => by rw [hF]; rfl

/-- The lower gauge bound $\mu\|v\|\le\gamma(v)$ in the library's `sqNorm` form. -/
theorem sqrt_form_lower {p : ℕ} {γ : Vec p → ℝ} {μ : ℝ}
    (hlow : ∀ v, μ * ‖euclideanVector v‖ ≤ γ v) : ∀ v, μ * Real.sqrt (sqNorm v) ≤ γ v := by
  simpa only [QuadraticGauge.sqrt_sqNorm_eq_euclidean_norm] using hlow

/-- The upper gauge bound $\gamma(v)\le\Lambda\|v\|$ in the library's `sqNorm` form. -/
theorem sqrt_form_upper {p : ℕ} {γ : Vec p → ℝ} {Λ : ℝ}
    (hup : ∀ v, γ v ≤ Λ * ‖euclideanVector v‖) : ∀ v, γ v ≤ Λ * Real.sqrt (sqNorm v) := by
  simpa only [QuadraticGauge.sqrt_sqNorm_eq_euclidean_norm] using hup

/-- Item `C/06_F/disp/015` (`companion/chapters/06_F.tex:137-140`): "For $F(u,v)=u^TQu/2+\gamma(v)$,
$Q\succ0$, let $\mu\|v\|\le\gamma(v)\le\Lambda\|v\|$. Split $t=a+b$ with
\[ a=\delta u^TQ\delta u,\quad b=(h'-h)^T\delta v,\quad \xi=(Q\delta u)^Tu',\quad
   \zeta=(h'-h)^Tv', \]
where $h\in\partial\gamma(v)$ and $h'\in\partial\gamma(v')$."

Under the standing assumptions, for the accepted pair $x=(u,v)=x_k$, $x'=(u',v')=x_{k+1}$:
$\delta u=u'-u$, $\delta v=v'-v$, and $h$, $h'$ are the $v$-components of the gradients $g_k$,
$g_{k+1}$ (variables with defining equations). The theorem states the claims:
$h\in\partial\gamma(v)$, $h'\in\partial\gamma(v')$, $t_k=a+b$, and $y_k^Tx'=\xi+\zeta$ (the
numerator of $R_k$ with $x_*=0$). -/
theorem quadGauge_split {m p : ℕ} (Q : Mat m) (hQ : Q.PosDef) (γ : Vec p → ℝ)
    (_hγ : ConvexOn ℝ univ γ) (_hγh : Homogeneous.PositiveDegreeOne γ) (μ Λ : ℝ) (_hμ : 0 < μ)
    (_hlow : ∀ v, μ * ‖euclideanVector v‖ ≤ γ v) (_hup : ∀ v, γ v ≤ Λ * ‖euclideanVector v‖)
    (F : Vec (m + p) → ℝ)
    (hF : ∀ x, F x = dot (QuadraticGauge.left x) (Q *ᵥ QuadraticGauge.left x) / 2 +
      γ (QuadraticGauge.right x))
    (R : AdmissibleBFGSRun (m + p) F) (k : ℕ)
    (δu : Vec m) (hδu : δu = QuadraticGauge.left (R.x (k + 1)) - QuadraticGauge.left (R.x k))
    (δv : Vec p) (hδv : δv = QuadraticGauge.right (R.x (k + 1)) - QuadraticGauge.right (R.x k))
    (h h' : Vec p) (hh : h = QuadraticGauge.right (R.g k))
    (hh' : h' = QuadraticGauge.right (R.g (k + 1)))
    (a b ξ ζ : ℝ) (ha : a = dot δu (Q *ᵥ δu)) (hb : b = dot (h' - h) δv)
    (hξ : ξ = dot (Q *ᵥ δu) (QuadraticGauge.left (R.x (k + 1))))
    (hζ : ζ = dot (h' - h) (QuadraticGauge.right (R.x (k + 1)))) :
    Homogeneous.Supports γ (QuadraticGauge.right (R.x k)) h ∧
      Homogeneous.Supports γ (QuadraticGauge.right (R.x (k + 1))) h' ∧
      R.curvature k = a + b ∧ dot (R.gradientChange k) (R.x (k + 1)) = ξ + ζ := by
  have hFe := quadGauge_objective_eq Q γ F hF
  subst hFe
  have hsym : Q.IsSymm := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hQ.isHermitian.eq
  have hs0 := convex_supporting_inequality R.convex (R.hasGradient k)
  have hs1 := convex_supporting_inequality R.convex (R.hasGradient (k + 1))
  have hl0 := QuadraticGauge.supports_left_eq Q hsym γ _ _ hs0
  have hl1 := QuadraticGauge.supports_left_eq Q hsym γ _ _ hs1
  have hy : QuadraticGauge.left (R.gradientChange k) = Q *ᵥ δu := by
    rw [AdmissibleBFGSRun.gradientChange, QuadraticGauge.left_sub, hl0, hl1, hδu,
      Matrix.mulVec_sub]
  have hyr : QuadraticGauge.right (R.gradientChange k) = h' - h := by
    rw [AdmissibleBFGSRun.gradientChange, QuadraticGauge.right_sub, hh, hh']
  refine ⟨hh ▸ QuadraticGauge.supports_right Q γ _ _ hs0,
    hh' ▸ QuadraticGauge.supports_right Q γ _ _ hs1, ?_, ?_⟩
  · rw [AdmissibleBFGSRun.curvature, displacement_eq, QuadraticGauge.dot_split, hy, hyr,
      QuadraticGauge.left_sub, QuadraticGauge.right_sub, ← hδu, ← hδv, ha, hb]
    congr 1
    exact dotProduct_comm _ _
  · rw [QuadraticGauge.dot_split, hy, hyr, hξ, hζ]

/-- Item `C/06_F/disp/016` (`companion/chapters/06_F.tex:142-145`): "Then
\[ \xi^2/a\le u'^TQu',\qquad0\le\zeta\le b,\qquad\zeta\le(1+\Lambda/\mu)\gamma(v'). \]"
Under the standing assumptions and the notation of display `disp/015` (Lean's $\xi^2/0=0$ for
the case $a=0$, where also $\xi=0$). -/
theorem quadGauge_split_bounds {m p : ℕ} (Q : Mat m) (hQ : Q.PosDef) (γ : Vec p → ℝ)
    (hγ : ConvexOn ℝ univ γ) (hγh : Homogeneous.PositiveDegreeOne γ) (μ Λ : ℝ) (hμ : 0 < μ)
    (hlow : ∀ v, μ * ‖euclideanVector v‖ ≤ γ v) (hup : ∀ v, γ v ≤ Λ * ‖euclideanVector v‖)
    (F : Vec (m + p) → ℝ)
    (hF : ∀ x, F x = dot (QuadraticGauge.left x) (Q *ᵥ QuadraticGauge.left x) / 2 +
      γ (QuadraticGauge.right x))
    (R : AdmissibleBFGSRun (m + p) F) (k : ℕ)
    (δu : Vec m) (hδu : δu = QuadraticGauge.left (R.x (k + 1)) - QuadraticGauge.left (R.x k))
    (δv : Vec p) (hδv : δv = QuadraticGauge.right (R.x (k + 1)) - QuadraticGauge.right (R.x k))
    (h h' : Vec p) (hh : h = QuadraticGauge.right (R.g k))
    (hh' : h' = QuadraticGauge.right (R.g (k + 1)))
    (a b ξ ζ : ℝ) (ha : a = dot δu (Q *ᵥ δu)) (hb : b = dot (h' - h) δv)
    (hξ : ξ = dot (Q *ᵥ δu) (QuadraticGauge.left (R.x (k + 1))))
    (hζ : ζ = dot (h' - h) (QuadraticGauge.right (R.x (k + 1)))) :
    ξ ^ 2 / a ≤ dot (QuadraticGauge.left (R.x (k + 1))) (Q *ᵥ QuadraticGauge.left (R.x (k + 1))) ∧
      0 ≤ ζ ∧ ζ ≤ b ∧ ζ ≤ (1 + Λ / μ) * γ (QuadraticGauge.right (R.x (k + 1))) := by
  obtain ⟨hsh, hsh', -, -⟩ := quadGauge_split Q hQ γ hγ hγh μ Λ hμ hlow hup F hF R k δu hδu δv hδv
    h h' hh hh' a b ξ ζ ha hb hξ hζ
  set u' := QuadraticGauge.left (R.x (k + 1))
  set v := QuadraticGauge.right (R.x k)
  set v' := QuadraticGauge.right (R.x (k + 1))
  have hcs := QuadraticGauge.metric_cauchy_schwarz hQ.posSemidef δu u'
  have ha0 : 0 ≤ a := by rw [ha]; exact QuadraticGauge.metricEnergy_nonneg hQ.posSemidef δu
  have hU0 : 0 ≤ dot u' (Q *ᵥ u') := QuadraticGauge.metricEnergy_nonneg hQ.posSemidef u'
  have hfirst : ξ ^ 2 / a ≤ dot u' (Q *ᵥ u') := by
    rcases ha0.eq_or_lt with h0 | h0
    · rw [← h0, div_zero]; exact hU0
    · rw [div_le_iff₀ h0, hξ]
      have : metricEnergy Q δu = a := by rw [ha]; rfl
      rw [this] at hcs
      change dot (Q *ᵥ δu) u' ^ 2 ≤ a * dot u' (Q *ᵥ u') at hcs
      linarith
  obtain ⟨hz0, hzb, -⟩ := QuadraticGauge.gauge_pairing_bounds hγh μ Λ hμ (sqrt_form_lower hlow)
    (sqrt_form_upper hup) v v' h h' hsh hsh'
  refine ⟨hfirst, hζ ▸ hz0, by rw [hζ, hb, hδv]; exact hzb, ?_⟩
  -- ζ = γ(v') - hᵀv' and -hᵀv' ≤ γ(-v') ≤ Λ‖v'‖ ≤ (Λ/μ)γ(v')
  have heul := Homogeneous.supporting_euler hγh hsh'
  have hneg := (Homogeneous.supporting_linear_le hγh hsh (-v')).trans (hup (-v'))
  have hnorm : ‖euclideanVector (-v')‖ = ‖euclideanVector v'‖ := by
    rw [show euclideanVector (-v') = -euclideanVector v' from rfl, norm_neg]
  rw [hnorm] at hneg
  have hdn : dot h (-v') = -dot h v' := dotProduct_neg _ _
  rw [hdn] at hneg
  have hzeq : ζ = γ v' - dot h v' := by
    rw [hζ, dot_sub_left, heul]
  have hlv := hlow v'
  have hγv : 0 ≤ γ v' := (mul_nonneg hμ.le (norm_nonneg _)).trans hlv
  have hkey : Λ * ‖euclideanVector v'‖ ≤ Λ / μ * γ v' := by
    rcases (norm_nonneg (euclideanVector v')).eq_or_lt with h0 | h0
    · have hγ0 : γ v' = 0 := le_antisymm (by have := hup v'; rw [← h0] at this; linarith) hγv
      rw [← h0, mul_zero, hγ0, mul_zero]
    · have hΛ : μ ≤ Λ := by
        have := hlv.trans (hup v')
        nlinarith
      rw [div_mul_eq_mul_div, le_div_iff₀ hμ]
      have := mul_le_mul_of_nonneg_left hlv (by linarith : (0 : ℝ) ≤ Λ)
      linarith
  rw [hzeq]
  nlinarith

/-- Item `C/06_F/disp/017` (`companion/chapters/06_F.tex:147-150`): "Thus
\[ R_k\le C_\gamma F(x_{k+1}),\qquad C_\gamma=\max\{2,1+\Lambda/\mu\}." \]
Under the standing assumptions, with $R_k=(y_k^Tx_{k+1})^2/t_k$ (reference point $x_*=0$) and
$C_\gamma$ a variable with its defining equation (library
`AdmissibleBFGSRun.quadraticGauge_referenceCorrection`). -/
theorem quadGauge_correction {m p : ℕ} (Q : Mat m) (hQ : Q.PosDef) (γ : Vec p → ℝ)
    (_hγ : ConvexOn ℝ univ γ) (hγh : Homogeneous.PositiveDegreeOne γ) (μ Λ : ℝ) (hμ : 0 < μ)
    (hlow : ∀ v, μ * ‖euclideanVector v‖ ≤ γ v) (hup : ∀ v, γ v ≤ Λ * ‖euclideanVector v‖)
    (F : Vec (m + p) → ℝ)
    (hF : ∀ x, F x = dot (QuadraticGauge.left x) (Q *ᵥ QuadraticGauge.left x) / 2 +
      γ (QuadraticGauge.right x))
    (R : AdmissibleBFGSRun (m + p) F) (Cγ : ℝ) (hCγ : Cγ = max 2 (1 + Λ / μ)) (k : ℕ) :
    dot (R.gradientChange k) (R.x (k + 1)) ^ 2 / R.curvature k ≤ Cγ * F (R.x (k + 1)) := by
  have hFe := quadGauge_objective_eq Q γ F hF
  subst hFe hCγ
  have h := R.quadraticGauge_referenceCorrection Q hQ.posSemidef γ hγh μ Λ hμ
    (sqrt_form_lower hlow) (sqrt_form_upper hup) k
  simpa only [AdmissibleBFGSRun.referenceCorrection, sub_zero] using h

/-- Superquadratic growth on the quadratic-plus-gauge objective (compact sublevels). -/
theorem quadGauge_superquadratic_aux {m p : ℕ} (Q : Mat m) (hQ : Q.PosDef) (γ : Vec p → ℝ)
    (hγh : Homogeneous.PositiveDegreeOne γ) (μ : ℝ) (hμ : 0 < μ)
    (hlow : ∀ v, μ * ‖euclideanVector v‖ ≤ γ v)
    (R : AdmissibleBFGSRun (m + p) (QuadraticGauge.objective Q γ)) :
    Tendsto (fun N : ℕ => (∑ k ∈ Finset.range N, (R.q k)⁻¹) / (N : ℝ) ^ 2) atTop atTop := by
  have hmin : ∀ x, QuadraticGauge.objective Q γ 0 ≤ QuadraticGauge.objective Q γ x := by
    simpa only [QuadraticGauge.objective_zero Q γ hγh] using
      QuadraticGauge.objective_nonneg Q hQ.posSemidef γ μ hμ (sqrt_form_lower hlow)
  exact superquadratic_of_bounded R 0 hmin (bounded_of_compact R
    (R.quadraticGauge_initialSublevel_compact Q hQ γ hγh μ hμ (sqrt_form_lower hlow)))

/-- Item `C/06_F/prose/034` (`companion/chapters/06_F.tex:151`): "Choose $a_0>0,N_0$ with
$S_N\ge a_0N^2$ for $N\ge N_0$". Under the standing assumptions (compact sublevels, hence
bounded gradients and $\sum d_k<\infty$): $S_N/N^2\to\infty$, so such $a_0,N_0$ exist (for every
$a_0>0$). -/
theorem quadGauge_choose {m p : ℕ} (Q : Mat m) (hQ : Q.PosDef) (γ : Vec p → ℝ)
    (_hγ : ConvexOn ℝ univ γ) (hγh : Homogeneous.PositiveDegreeOne γ) (μ Λ : ℝ) (hμ : 0 < μ)
    (hlow : ∀ v, μ * ‖euclideanVector v‖ ≤ γ v) (_hup : ∀ v, γ v ≤ Λ * ‖euclideanVector v‖)
    (F : Vec (m + p) → ℝ)
    (hF : ∀ x, F x = dot (QuadraticGauge.left x) (Q *ᵥ QuadraticGauge.left x) / 2 +
      γ (QuadraticGauge.right x))
    (R : AdmissibleBFGSRun (m + p) F) (S : ℕ → ℝ)
    (hS : ∀ N, S N = ∑ k ∈ Finset.range N, (R.q k)⁻¹) :
    Tendsto (fun N : ℕ => S N / (N : ℝ) ^ 2) atTop atTop ∧
      (∃ a0 : ℝ, 0 < a0 ∧ ∃ N0 : ℕ, ∀ N, N0 ≤ N → a0 * (N : ℝ) ^ 2 ≤ S N) ∧
      ∀ a0 : ℝ, 0 < a0 → ∃ N0 : ℕ, ∀ N, N0 ≤ N → a0 * (N : ℝ) ^ 2 ≤ S N := by
  have hFe := quadGauge_objective_eq Q γ F hF
  subst hFe
  have hSf : S = fun N => ∑ k ∈ Finset.range N, (R.q k)⁻¹ := funext hS
  have hsup : Tendsto (fun N : ℕ => S N / (N : ℝ) ^ 2) atTop atTop := by
    rw [hSf]; exact quadGauge_superquadratic_aux Q hQ γ hγh μ hμ hlow R
  have hall : ∀ a0 : ℝ, 0 < a0 → ∃ N0 : ℕ, ∀ N, N0 ≤ N → a0 * (N : ℝ) ^ 2 ≤ S N := by
    intro a0 _
    obtain ⟨N0, hN0⟩ := eventually_atTop.mp ((hsup.eventually (eventually_ge_atTop a0)).and
      (eventually_gt_atTop 0))
    refine ⟨N0, fun N hN => ?_⟩
    obtain ⟨h1, h2⟩ := hN0 N hN
    have hpos : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
    rw [le_div_iff₀ hpos] at h1
    linarith
  exact ⟨hsup, ⟨1, one_pos, hall 1 one_pos⟩, hall⟩

/-- Item `C/06_F/disp/018` (`companion/chapters/06_F.tex:152-154`): the budget
\[ A_N=E_0+C_\gamma\sum_{j=1}^NF(x_j). \]
$A$ is a variable with its defining equation (the sum written as $\sum_{k<N}F(x_{k+1})$),
$E_0=x_0^TH_0^{-1}x_0$ and $C_\gamma=\max\{2,1+\Lambda/\mu\}$. Under the standing assumptions it
is the library's `valueCorrectionBudget 0 Cγ`, satisfies $A_{N+1}=A_N+C_\gamma F(x_{N+1})$,
$F(x_N)^2S_N\le A_N$ (from \eqref{M:energybound} and display `disp/017`), and $A_N\ge E_0>0$. -/
theorem quadGauge_budget {m p : ℕ} (Q : Mat m) (hQ : Q.PosDef) (γ : Vec p → ℝ)
    (hγ : ConvexOn ℝ univ γ) (hγh : Homogeneous.PositiveDegreeOne γ) (μ Λ : ℝ) (hμ : 0 < μ)
    (hlow : ∀ v, μ * ‖euclideanVector v‖ ≤ γ v) (hup : ∀ v, γ v ≤ Λ * ‖euclideanVector v‖)
    (F : Vec (m + p) → ℝ)
    (hF : ∀ x, F x = dot (QuadraticGauge.left x) (Q *ᵥ QuadraticGauge.left x) / 2 +
      γ (QuadraticGauge.right x))
    (R : AdmissibleBFGSRun (m + p) F) (S : ℕ → ℝ)
    (hS : ∀ N, S N = ∑ k ∈ Finset.range N, (R.q k)⁻¹)
    (E0 : ℝ) (hE0 : E0 = dot (R.x 0) ((R.H 0)⁻¹ *ᵥ R.x 0))
    (Cγ : ℝ) (hCγ : Cγ = max 2 (1 + Λ / μ))
    (A : ℕ → ℝ) (hA : ∀ N, A N = E0 + Cγ * ∑ k ∈ Finset.range N, F (R.x (k + 1))) :
    (∀ N, A N = R.valueCorrectionBudget 0 Cγ N) ∧ (∀ N, A (N + 1) = A N + Cγ * F (R.x (N + 1))) ∧
      (∀ N, F (R.x N) ^ 2 * S N ≤ A N) ∧ 0 < E0 ∧ ∀ N, E0 ≤ A N := by
  have hcorr := quadGauge_correction Q hQ γ hγ hγh μ Λ hμ hlow hup F hF R Cγ hCγ
  have hFe := quadGauge_objective_eq Q γ F hF
  subst hFe
  have hF0 : QuadraticGauge.objective Q γ 0 = 0 := QuadraticGauge.objective_zero Q γ hγh
  have hnn : ∀ x, 0 ≤ QuadraticGauge.objective Q γ x :=
    QuadraticGauge.objective_nonneg Q hQ.posSemidef γ μ hμ (sqrt_form_lower hlow)
  have hmin : ∀ x, QuadraticGauge.objective Q γ 0 ≤ QuadraticGauge.objective Q γ x := by
    rw [hF0]; exact hnn
  have hC0 : 0 ≤ Cγ := by rw [hCγ]; exact le_max_of_le_left (by norm_num)
  have hlib : ∀ N, A N = R.valueCorrectionBudget 0 Cγ N := by
    intro N
    rw [hA, AdmissibleBFGSRun.valueCorrectionBudget, hE0, hF0, referenceEnergy_zero_eq]
    simp only [sub_zero]
  have hE0pos : 0 < E0 := by
    have hx0 : R.x 0 ≠ 0 := by
      intro h0
      have := BfgsCoverage.Article.Global.initial_value_gt R 0 hmin
      rw [h0] at this
      exact lt_irrefl _ this
    have hp := (R.hessian_posDef 0).2 (R.x 0) hx0
    rw [hE0]
    simpa [dot, dotProduct, AdmissibleBFGSRun.hessian] using hp
  refine ⟨hlib, fun N => ?_, fun N => ?_, hE0pos, fun N => ?_⟩
  · rw [hlib, hlib, R.valueCorrectionBudget_step, hF0, sub_zero]
  · rw [hlib, hS]
    have h := R.reference_value_budget_bound 0 hmin Cγ (fun k => by
      have := hcorr k
      simpa only [AdmissibleBFGSRun.referenceCorrection, sub_zero, hF0] using this) N
    simpa only [hF0, sub_zero] using h
  · rw [hA]
    have : 0 ≤ Cγ * ∑ k ∈ Finset.range N, QuadraticGauge.objective Q γ (R.x (k + 1)) :=
      mul_nonneg hC0 (Finset.sum_nonneg fun k _ => hnn _)
    linarith

/-- Item `C/06_F/disp/019` (`companion/chapters/06_F.tex:156-160`), and the preceding claim,
Item `C/06_F/prose/035` (`companion/chapters/06_F.tex:155`): "Then
$F(x_N)\le\sqrt{A_N}/(\sqrt{a_0}N)$, and
\[ \sqrt{A_N}-\sqrt{A_{N-1}}=\frac{C_\gamma F(x_N)}{\sqrt{A_N}+\sqrt{A_{N-1}}}
   \le\frac{C_\gamma}{\sqrt{a_0}N}." \]
Under the standing assumptions, the notation of display `disp/018`, and $a_0>0$, $N_0$ with
$S_N\ge a_0N^2$ for $N\ge N_0$: for every $N\ge\max\{N_0,1\}$. -/
theorem quadGauge_increment {m p : ℕ} (Q : Mat m) (hQ : Q.PosDef) (γ : Vec p → ℝ)
    (hγ : ConvexOn ℝ univ γ) (hγh : Homogeneous.PositiveDegreeOne γ) (μ Λ : ℝ) (hμ : 0 < μ)
    (hlow : ∀ v, μ * ‖euclideanVector v‖ ≤ γ v) (hup : ∀ v, γ v ≤ Λ * ‖euclideanVector v‖)
    (F : Vec (m + p) → ℝ)
    (hF : ∀ x, F x = dot (QuadraticGauge.left x) (Q *ᵥ QuadraticGauge.left x) / 2 +
      γ (QuadraticGauge.right x))
    (R : AdmissibleBFGSRun (m + p) F) (S : ℕ → ℝ)
    (hS : ∀ N, S N = ∑ k ∈ Finset.range N, (R.q k)⁻¹)
    (E0 : ℝ) (hE0 : E0 = dot (R.x 0) ((R.H 0)⁻¹ *ᵥ R.x 0))
    (Cγ : ℝ) (hCγ : Cγ = max 2 (1 + Λ / μ))
    (A : ℕ → ℝ) (hA : ∀ N, A N = E0 + Cγ * ∑ k ∈ Finset.range N, F (R.x (k + 1)))
    (a0 : ℝ) (ha0 : 0 < a0) (N0 : ℕ) (hN0 : ∀ N, N0 ≤ N → a0 * (N : ℝ) ^ 2 ≤ S N)
    (N : ℕ) (hN : N0 ≤ N) (hN1 : 1 ≤ N) :
    F (R.x N) ≤ Real.sqrt (A N) / (Real.sqrt a0 * N) ∧
      Real.sqrt (A N) - Real.sqrt (A (N - 1)) =
        Cγ * F (R.x N) / (Real.sqrt (A N) + Real.sqrt (A (N - 1))) ∧
      Cγ * F (R.x N) / (Real.sqrt (A N) + Real.sqrt (A (N - 1))) ≤ Cγ / (Real.sqrt a0 * N) := by
  obtain ⟨-, hstep, hbound, hE0pos, hEA⟩ := quadGauge_budget Q hQ γ hγ hγh μ Λ hμ hlow hup F hF R
    S hS E0 hE0 Cγ hCγ A hA
  have hnn : ∀ x, 0 ≤ F x := fun x => by
    rw [quadGauge_objective_eq Q γ F hF]
    exact QuadraticGauge.objective_nonneg Q hQ.posSemidef γ μ hμ (sqrt_form_lower hlow) x
  have hC0 : 0 ≤ Cγ := by rw [hCγ]; exact le_max_of_le_left (by norm_num)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hSN : a0 * (N : ℝ) ^ 2 ≤ S N := hN0 N hN
  have hSpos : 0 < S N := lt_of_lt_of_le (by positivity) hSN
  have hAN : 0 < A N := hE0pos.trans_le (hEA N)
  have hAN1 : 0 < A (N - 1) := hE0pos.trans_le (hEA (N - 1))
  have hsa : 0 < Real.sqrt a0 * N := by positivity
  -- F(x_N) ≤ √A_N/(√a₀N)
  have hfirst : F (R.x N) ≤ Real.sqrt (A N) / (Real.sqrt a0 * N) := by
    rw [le_div_iff₀ hsa]
    have h1 : (F (R.x N) * (Real.sqrt a0 * N)) ^ 2 ≤ (Real.sqrt (A N)) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt ha0.le, Real.sq_sqrt hAN.le]
      have := hbound N
      have h2 : F (R.x N) ^ 2 * (a0 * (N : ℝ) ^ 2) ≤ F (R.x N) ^ 2 * S N :=
        mul_le_mul_of_nonneg_left hSN (sq_nonneg _)
      nlinarith
    have := Real.sqrt_nonneg (A N)
    nlinarith [mul_nonneg (hnn (R.x N)) hsa.le]
  -- the exact increment
  have hrec : A N = A (N - 1) + Cγ * F (R.x N) := by
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    simpa using hstep M
  have hden : 0 < Real.sqrt (A N) + Real.sqrt (A (N - 1)) := by positivity
  have hid : Real.sqrt (A N) - Real.sqrt (A (N - 1)) =
      Cγ * F (R.x N) / (Real.sqrt (A N) + Real.sqrt (A (N - 1))) := by
    rw [eq_div_iff hden.ne']
    have h1 := Real.sq_sqrt hAN.le
    have h2 := Real.sq_sqrt hAN1.le
    nlinarith
  refine ⟨hfirst, hid, ?_⟩
  have hsq : 0 < Real.sqrt (A N) := Real.sqrt_pos.mpr hAN
  calc Cγ * F (R.x N) / (Real.sqrt (A N) + Real.sqrt (A (N - 1)))
      ≤ Cγ * F (R.x N) / Real.sqrt (A N) := by
        apply div_le_div_of_nonneg_left (mul_nonneg hC0 (hnn _)) hsq
        linarith [Real.sqrt_nonneg (A (N - 1))]
    _ ≤ Cγ * (Real.sqrt (A N) / (Real.sqrt a0 * N)) / Real.sqrt (A N) := by
        apply div_le_div_of_nonneg_right _ hsq.le
        exact mul_le_mul_of_nonneg_left hfirst hC0
    _ = Cγ / (Real.sqrt a0 * N) := by field_simp; ring

/-- Item `C/06_F/prose/036` (`companion/chapters/06_F.tex:161`): "Summing first gives the bounds
$\sqrt{A_N}=O(\log N)$ and $F(x_N)=O(\log N/N)$." (Wording point W25 applied on 15 October 2026;
before "recovers the source bounds".) Under the standing assumptions and the
notation of display `disp/018` (library `quadraticGauge_sqrt_budget_log_rate`, which proves the
stronger $o(\log N)$, and `quadraticGauge_euclidean_value_log_orders`). -/
theorem quadGauge_bigO {m p : ℕ} (Q : Mat m) (hQ : Q.PosDef) (γ : Vec p → ℝ)
    (_hγ : ConvexOn ℝ univ γ) (hγh : Homogeneous.PositiveDegreeOne γ) (μ Λ : ℝ) (hμ : 0 < μ)
    (hlow : ∀ v, μ * ‖euclideanVector v‖ ≤ γ v) (hup : ∀ v, γ v ≤ Λ * ‖euclideanVector v‖)
    (F : Vec (m + p) → ℝ)
    (hF : ∀ x, F x = dot (QuadraticGauge.left x) (Q *ᵥ QuadraticGauge.left x) / 2 +
      γ (QuadraticGauge.right x))
    (R : AdmissibleBFGSRun (m + p) F)
    (E0 : ℝ) (hE0 : E0 = dot (R.x 0) ((R.H 0)⁻¹ *ᵥ R.x 0))
    (Cγ : ℝ) (hCγ : Cγ = max 2 (1 + Λ / μ))
    (A : ℕ → ℝ) (hA : ∀ N, A N = E0 + Cγ * ∑ k ∈ Finset.range N, F (R.x (k + 1))) :
    (fun N => Real.sqrt (A N)) =O[atTop] (fun N : ℕ => Real.log (N : ℝ)) ∧
      (fun N => F (R.x N)) =O[atTop] (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ)) := by
  have hFe := quadGauge_objective_eq Q γ F hF
  subst hFe hCγ
  have hAN : ∀ N, R.referenceEnergy 0 0 + QuadraticGauge.correctionConstant μ Λ *
      ∑ k ∈ Finset.range N, QuadraticGauge.objective Q γ (R.x (k + 1)) = A N := fun N => by
    rw [hA, hE0, referenceEnergy_zero_eq]
    rfl
  have hlog := R.quadraticGauge_sqrt_budget_log_rate Q hQ γ hγh μ Λ hμ (sqrt_form_lower hlow)
    (sqrt_form_upper hup)
  simp only [hAN] at hlog
  refine ⟨?_, (R.quadraticGauge_euclidean_value_log_orders Q hQ γ hγh μ Λ hμ hlow hup).2⟩
  refine (Asymptotics.isLittleO_of_tendsto' ?_ hlog).isBigO
  filter_upwards [HarmonicRates.log_nat_tendsto.eventually (eventually_gt_atTop (0 : ℝ))]
    with N hN
  exact fun he => False.elim (hN.ne' he)

/-- Item `C/06_F/disp/020` (`companion/chapters/06_F.tex:162-164`): "For the strengthened
conclusion, keep the exact denominator:
\[ \sqrt{A_N}-\sqrt{A_{N-1}}\le \frac{C_\gamma}{\sqrt{S_N}}=o(N^{-1})." \]
Under the standing assumptions and the notation of display `disp/018`: for every $N\ge1$, and
$N\cdot C_\gamma/\sqrt{S_N}\to0$. -/
theorem quadGauge_increment_exact {m p : ℕ} (Q : Mat m) (hQ : Q.PosDef) (γ : Vec p → ℝ)
    (hγ : ConvexOn ℝ univ γ) (hγh : Homogeneous.PositiveDegreeOne γ) (μ Λ : ℝ) (hμ : 0 < μ)
    (hlow : ∀ v, μ * ‖euclideanVector v‖ ≤ γ v) (hup : ∀ v, γ v ≤ Λ * ‖euclideanVector v‖)
    (F : Vec (m + p) → ℝ)
    (hF : ∀ x, F x = dot (QuadraticGauge.left x) (Q *ᵥ QuadraticGauge.left x) / 2 +
      γ (QuadraticGauge.right x))
    (R : AdmissibleBFGSRun (m + p) F) (S : ℕ → ℝ)
    (hS : ∀ N, S N = ∑ k ∈ Finset.range N, (R.q k)⁻¹)
    (E0 : ℝ) (hE0 : E0 = dot (R.x 0) ((R.H 0)⁻¹ *ᵥ R.x 0))
    (Cγ : ℝ) (hCγ : Cγ = max 2 (1 + Λ / μ))
    (A : ℕ → ℝ) (hA : ∀ N, A N = E0 + Cγ * ∑ k ∈ Finset.range N, F (R.x (k + 1))) :
    (∀ N, 1 ≤ N → Real.sqrt (A N) - Real.sqrt (A (N - 1)) ≤ Cγ / Real.sqrt (S N)) ∧
      Tendsto (fun N : ℕ => (N : ℝ) * (Cγ / Real.sqrt (S N))) atTop (𝓝 0) := by
  obtain ⟨-, hstep, hbound, hE0pos, hEA⟩ := quadGauge_budget Q hQ γ hγ hγh μ Λ hμ hlow hup F hF R
    S hS E0 hE0 Cγ hCγ A hA
  have hnn : ∀ x, 0 ≤ F x := fun x => by
    rw [quadGauge_objective_eq Q γ F hF]
    exact QuadraticGauge.objective_nonneg Q hQ.posSemidef γ μ hμ (sqrt_form_lower hlow) x
  have hC0 : 0 ≤ Cγ := by rw [hCγ]; exact le_max_of_le_left (by norm_num)
  refine ⟨fun N hN1 => ?_, ?_⟩
  · obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    have hSpos : 0 < S (M + 1) := by
      rw [hS, Finset.sum_range_succ]
      have := Finset.sum_nonneg (fun k (_ : k ∈ Finset.range M) => (inv_pos.mpr (R.q_pos k)).le)
      have := inv_pos.mpr (R.q_pos M)
      linarith
    simpa using (HarmonicRates.sqrt_increment_bound (hE0pos.le.trans (hEA M)) (hnn _) hC0 hSpos
      (hstep M) (hbound (M + 1))).2
  · have hFe := quadGauge_objective_eq Q γ F hF
    subst hFe
    have hSf : S = fun N => ∑ k ∈ Finset.range N, (R.q k)⁻¹ := funext hS
    have hsup : Tendsto (fun N : ℕ => S N / (N : ℝ) ^ 2) atTop atTop := by
      rw [hSf]; exact quadGauge_superquadratic_aux Q hQ γ hγh μ hμ hlow R
    have h := (HarmonicRates.inverse_sqrt_scale_tendsto hsup).const_mul Cγ
    rw [mul_zero] at h
    refine h.congr fun N => ?_
    ring

/-- Item `C/06_F/prose/037` (`companion/chapters/06_F.tex:165`): "A sum of $o(1/N)$ increments is
$o(\log N)$: for any fixed $\epsilon>0$, bound the sufficiently late increments by $\epsilon/N$,
then divide their sum by $\log N$ and let $\epsilon\downarrow0$." For a real sequence $a$ with
$(N+1)(a_{N+1}-a_N)\to0$: $a_N/\log N\to0$ (library
`HarmonicRates.log_rate_of_harmonic_increments`). -/
theorem littleO_increments_log (a : ℕ → ℝ)
    (hinc : Tendsto (fun N : ℕ => ((N : ℝ) + 1) * (a (N + 1) - a N)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => a N / Real.log (N : ℝ)) atTop (𝓝 0) :=
  HarmonicRates.log_rate_of_harmonic_increments hinc

/-- Item `C/06_F/prose/038` (`companion/chapters/06_F.tex:165`): "Thus $\sqrt{A_N}=o(\log N)$."
Under the standing assumptions and the notation of display `disp/018`
(library `AdmissibleBFGSRun.quadraticGauge_sqrt_budget_log_rate`). -/
theorem quadGauge_sqrt_budget {m p : ℕ} (Q : Mat m) (hQ : Q.PosDef) (γ : Vec p → ℝ)
    (_hγ : ConvexOn ℝ univ γ) (hγh : Homogeneous.PositiveDegreeOne γ) (μ Λ : ℝ) (hμ : 0 < μ)
    (hlow : ∀ v, μ * ‖euclideanVector v‖ ≤ γ v) (hup : ∀ v, γ v ≤ Λ * ‖euclideanVector v‖)
    (F : Vec (m + p) → ℝ)
    (hF : ∀ x, F x = dot (QuadraticGauge.left x) (Q *ᵥ QuadraticGauge.left x) / 2 +
      γ (QuadraticGauge.right x))
    (R : AdmissibleBFGSRun (m + p) F)
    (E0 : ℝ) (hE0 : E0 = dot (R.x 0) ((R.H 0)⁻¹ *ᵥ R.x 0))
    (Cγ : ℝ) (hCγ : Cγ = max 2 (1 + Λ / μ))
    (A : ℕ → ℝ) (hA : ∀ N, A N = E0 + Cγ * ∑ k ∈ Finset.range N, F (R.x (k + 1))) :
    Tendsto (fun N : ℕ => Real.sqrt (A N) / Real.log (N : ℝ)) atTop (𝓝 0) := by
  have hFe := quadGauge_objective_eq Q γ F hF
  subst hFe hCγ
  have hAN : ∀ N, R.referenceEnergy 0 0 + QuadraticGauge.correctionConstant μ Λ *
      ∑ k ∈ Finset.range N, QuadraticGauge.objective Q γ (R.x (k + 1)) = A N := fun N => by
    rw [hA, hE0, referenceEnergy_zero_eq]
    rfl
  have hlog := R.quadraticGauge_sqrt_budget_log_rate Q hQ γ hγh μ Λ hμ (sqrt_form_lower hlow)
    (sqrt_form_upper hup)
  simpa only [hAN] using hlog

/-- Item `C/06_F/disp/021` (`companion/chapters/06_F.tex:166-168`): "Dividing by
$\sqrt{S_N}=N\sqrt{S_N/N^2}$ yields
\[ \boxed{F(x_N)=o(\log N/N).} \]"
Under the standing assumptions (library `quadraticGauge_euclidean_value_log_orders`). -/
theorem quadGauge_rate {m p : ℕ} (Q : Mat m) (hQ : Q.PosDef) (γ : Vec p → ℝ)
    (_hγ : ConvexOn ℝ univ γ) (hγh : Homogeneous.PositiveDegreeOne γ) (μ Λ : ℝ) (hμ : 0 < μ)
    (hlow : ∀ v, μ * ‖euclideanVector v‖ ≤ γ v) (hup : ∀ v, γ v ≤ Λ * ‖euclideanVector v‖)
    (F : Vec (m + p) → ℝ)
    (hF : ∀ x, F x = dot (QuadraticGauge.left x) (Q *ᵥ QuadraticGauge.left x) / 2 +
      γ (QuadraticGauge.right x))
    (R : AdmissibleBFGSRun (m + p) F) :
    (fun N => F (R.x N)) =o[atTop] (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ)) := by
  have hFe := quadGauge_objective_eq Q γ F hF
  subst hFe
  exact (R.quadraticGauge_euclidean_value_log_orders Q hQ γ hγh μ Λ hμ hlow hup).1

/-! ### Matrix limits and line-search existence (`06_F.tex:175-203`) -/

/-- The library's `UnexcitedMetric.diagonal A B` is $\operatorname{diag}(A,B)$. -/
theorem unexcited_diagonal (A B : ℝ) : UnexcitedMetric.diagonal A B = !![A, 0; 0, B] := rfl

/-- The iterates and matrices of the library's run in closed form. -/
theorem unexcited_closed_form (ρ v₀ : ℝ) (k : ℕ) :
    UnexcitedMetric.point (UnexcitedMetric.sign k) (UnexcitedMetric.radius ρ v₀ k) =
      ![0, (-ρ) ^ k * v₀] ∧ UnexcitedMetric.radius ρ v₀ k = ρ ^ k * v₀ :=
  ⟨UnexcitedMetric.literal_point_formula ρ v₀ k, rfl⟩

/-- Item `C/06_F/disp/023` (`companion/chapters/06_F.tex:183-186`), with its data display
`C/06_F/disp/022` (lines 178-181): "For $u^2+|v|$, choose $A>0$, $v_0>0$ and
$0<\rho<(1-c_1)/(1+c_1)$. With
\[ x_0=(0,v_0),\quad H_0=\operatorname{diag}\left(A,\frac{1+\rho}{2\rho}v_0\right),\quad
   \alpha_k=2\rho, \]
ordinary BFGS gives
\[ x_k=(0,(-\rho)^kv_0),\quad
   H_k=\operatorname{diag}\left(A,\frac{1+\rho}{2\rho}\rho^kv_0\right). \]"

For fixed $0<c_1<c_2<1$: an admissible run with these data exists (it is accepted by the
line-search tests, `unexcited_ratios`; library `UnexcitedMetric.run`), and every admissible run
with $x_0$, $H_0$ and $\alpha_k=2\rho$ as displayed has the displayed $x_k$ and $H_k$ (ordinary BFGS
is deterministic once the lengths are fixed). $(u,v)$ is `x : Vec 2` with $u=x_0$, $v=x_1$. -/
theorem unexcited_run (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc : c₁ < c₂) (hc₂ : c₂ < 1)
    (F : Vec 2 → ℝ) (hF : ∀ x, F x = (x 0) ^ 2 + |x 1|)
    (A v₀ ρ : ℝ) (hA : 0 < A) (hv : 0 < v₀) (hρ : 0 < ρ) (hr : ρ < (1 - c₁) / (1 + c₁)) :
    (∃ R : AdmissibleBFGSRun 2 F, R.c₁ = c₁ ∧ R.c₂ = c₂ ∧ R.x 0 = ![0, v₀] ∧
      R.H 0 = !![A, 0; 0, (1 + ρ) / (2 * ρ) * v₀] ∧ ∀ k, R.α k = 2 * ρ) ∧
    ∀ R : AdmissibleBFGSRun 2 F, R.x 0 = ![0, v₀] → R.H 0 = !![A, 0; 0, (1 + ρ) / (2 * ρ) * v₀] →
      (∀ k, R.α k = 2 * ρ) →
      ∀ k, R.x k = ![0, (-ρ) ^ k * v₀] ∧ R.H k = !![A, 0; 0, (1 + ρ) / (2 * ρ) * (ρ ^ k * v₀)] := by
  obtain rfl : F = UnexcitedMetric.objective := funext hF
  refine ⟨⟨UnexcitedMetric.run A v₀ ρ c₁ c₂ hA hv hρ hc₁ hc hc₂ hr, rfl, rfl, ?_, ?_,
    fun k => rfl⟩, ?_⟩
  · change UnexcitedMetric.point (UnexcitedMetric.sign 0) (UnexcitedMetric.radius ρ v₀ 0) = _
    rw [(unexcited_closed_form ρ v₀ 0).1]
    simp
  · change UnexcitedMetric.diagonal A ((1 + ρ) / (2 * ρ) * UnexcitedMetric.radius ρ v₀ 0) = _
    simp [UnexcitedMetric.diagonal, UnexcitedMetric.radius]
  intro R hx0 hH0 hα
  -- the iterates and matrices of the library run
  have key : ∀ k, R.x k = UnexcitedMetric.point (UnexcitedMetric.sign k)
      (UnexcitedMetric.radius ρ v₀ k) ∧
      R.H k = UnexcitedMetric.diagonal A ((1 + ρ) / (2 * ρ) * UnexcitedMetric.radius ρ v₀ k) := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [hx0, (unexcited_closed_form ρ v₀ 0).1]; simp
      · rw [hH0]; simp [UnexcitedMetric.diagonal, UnexcitedMetric.radius]
    | succ k ih =>
      have hgk : R.g k = UnexcitedMetric.gradient (UnexcitedMetric.sign k) := by
        apply gradient_unique (R.hasGradient k)
        rw [ih.1]
        exact UnexcitedMetric.actual_gradient (UnexcitedMetric.sign_sq k)
          (UnexcitedMetric.radius_pos hρ hv k)
      have hxk1 : R.x (k + 1) = UnexcitedMetric.point (UnexcitedMetric.sign (k + 1))
          (UnexcitedMetric.radius ρ v₀ (k + 1)) := by
        rw [R.step k, ih.1, ih.2, hgk, hα k, UnexcitedMetric.sign_succ,
          UnexcitedMetric.radius_succ]
        exact (UnexcitedMetric.point_step A _ _ ρ hρ.ne').symm
      have hgk1 : R.g (k + 1) = UnexcitedMetric.gradient (UnexcitedMetric.sign (k + 1)) := by
        apply gradient_unique (R.hasGradient (k + 1))
        rw [hxk1]
        exact UnexcitedMetric.actual_gradient (UnexcitedMetric.sign_sq (k + 1))
          (UnexcitedMetric.radius_pos hρ hv (k + 1))
      refine ⟨hxk1, ?_⟩
      rw [R.update k, ih.2, hgk, hgk1, hα k, UnexcitedMetric.sign_succ,
        UnexcitedMetric.radius_succ]
      exact UnexcitedMetric.actual_update A (UnexcitedMetric.sign_sq k)
        (UnexcitedMetric.radius_pos hρ hv k) hρ
  intro k
  obtain ⟨h1, h2⟩ := key k
  refine ⟨by rw [h1, (unexcited_closed_form ρ v₀ k).1], ?_⟩
  rw [h2, unexcited_diagonal, (unexcited_closed_form ρ v₀ k).2]

/-- Item `C/06_F/prose/041` (`companion/chapters/06_F.tex:187`): "The Armijo ratio is
$(1-\rho)/(1+\rho)>c_1$ and the weak-Wolfe ratio is $-1$." For the run of `unexcited_run`, for
every $k$: $\Delta_k/(-g_k^Ts_k)=(1-\rho)/(1+\rho)$, this exceeds $c_1$, and
$g_{k+1}^Ts_k/g_k^Ts_k=-1$. -/
theorem unexcited_ratios (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc : c₁ < c₂) (hc₂ : c₂ < 1)
    (A v₀ ρ : ℝ) (hA : 0 < A) (hv : 0 < v₀) (hρ : 0 < ρ) (hr : ρ < (1 - c₁) / (1 + c₁))
    (k : ℕ) :
    let R := UnexcitedMetric.run A v₀ ρ c₁ c₂ hA hv hρ hc₁ hc hc₂ hr
    (UnexcitedMetric.objective (R.x k) - UnexcitedMetric.objective (R.x (k + 1))) /
        (-dot (R.g k) (R.displacement k)) = (1 - ρ) / (1 + ρ) ∧
      c₁ < (1 - ρ) / (1 + ρ) ∧
      dot (R.g (k + 1)) (R.displacement k) / dot (R.g k) (R.displacement k) = -1 := by
  intro R
  have h := UnexcitedMetric.acceptance_ratios A (UnexcitedMetric.sign_sq k)
    (UnexcitedMetric.radius_pos hρ hv k) hρ
  have hsr := UnexcitedMetric.source_ratio hc₁ hρ hr
  have hc1 : c₁ < (1 - ρ) / (1 + ρ) := by
    rw [lt_div_iff₀ (by linarith)]
    linarith [hsr.2]
  have hs : R.x (k + 1) = UnexcitedMetric.point (-UnexcitedMetric.sign k)
      (ρ * UnexcitedMetric.radius ρ v₀ k) := by
    change UnexcitedMetric.point (UnexcitedMetric.sign (k + 1))
      (UnexcitedMetric.radius ρ v₀ (k + 1)) = _
    rw [UnexcitedMetric.sign_succ, UnexcitedMetric.radius_succ]
  have hg1 : R.g (k + 1) = UnexcitedMetric.gradient (-UnexcitedMetric.sign k) := by
    change UnexcitedMetric.gradient (UnexcitedMetric.sign (k + 1)) = _
    rw [UnexcitedMetric.sign_succ]
  refine ⟨?_, hc1, ?_⟩
  · rw [hs]
    exact h.1
  · rw [hg1]
    exact h.2

/-- Item `C/06_F/prose/042` (`companion/chapters/06_F.tex:187`): "The unexcited tangential entry
tends to its arbitrary initial value $A$, not necessarily the inverse true tangential
curvature." For the run of `unexcited_run` (every $A>0$): $H_k\to\operatorname{diag}(A,0)$ and
$(H_k)_{11}=A$ for all $k$, while the true tangential second derivative of $F$ is $2$ (the
derivative of $u\mapsto F(u,0)$ is $2u$, whose derivative is $2$); so the limit entry is $A$, not
$1/2$ unless $A=1/2$. -/
theorem unexcited_limit (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc : c₁ < c₂) (hc₂ : c₂ < 1)
    (A v₀ ρ : ℝ) (hA : 0 < A) (hv : 0 < v₀) (hρ : 0 < ρ) (hr : ρ < (1 - c₁) / (1 + c₁)) :
    let R := UnexcitedMetric.run A v₀ ρ c₁ c₂ hA hv hρ hc₁ hc hc₂ hr
    Tendsto R.H atTop (𝓝 !![A, 0; 0, 0]) ∧ (∀ k, R.H k 0 0 = A) ∧
      (∀ u : ℝ, HasDerivAt (fun t : ℝ => UnexcitedMetric.objective ![t, 0]) (2 * u) u ∧
        HasDerivAt (fun t : ℝ => 2 * t) 2 u) := by
  intro R
  obtain ⟨-, -, hH, h00, -⟩ := UnexcitedMetric.run_limits A v₀ ρ c₁ c₂ hA hv hρ hc₁ hc hc₂ hr
  exact ⟨hH, h00, UnexcitedMetric.tangential_second_derivative⟩

/-! #### The tilted-minimum line-search construction (`06_F.tex:189-197`)

Standing assumptions: $\varphi:\R\to\R$ convex (a finite convex line restriction), bounded below
on $[0,\infty)$, with derivative $a<0$ at $0$; fixed $0<c_1<c_2<1$; $\sigma=(c_1+c_2)/2$ and
$\psi(t)=\varphi(t)-\sigma at$ (variables with defining equations). -/

/-- Item `C/06_F/prose/043` (`companion/chapters/06_F.tex:189`): "Choose $\sigma=(c_1+c_2)/2$ and
set $\psi(t)=\varphi(t)-\sigma at$. Its derivative at zero is $(1-\sigma)a<0$, while the lower
bound on $\varphi$ makes $\psi(t)\to+\infty$ as $t\to+\infty$. Choose a compact interval $[0,M]$
whose interior contains a minimizer $z>0$ of $\psi$, with $\psi(z)<\psi(0)$." -/
theorem tilted_setup (φ : ℝ → ℝ) (hφ : ConvexOn ℝ univ φ) (L : ℝ) (hL : ∀ t, 0 ≤ t → L ≤ φ t)
    (a : ℝ) (hd : HasDerivAt φ a 0) (ha : a < 0) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc : c₁ < c₂)
    (hc₂ : c₂ < 1) (σ : ℝ) (hσ : σ = (c₁ + c₂) / 2) (ψ : ℝ → ℝ)
    (hψ : ∀ t, ψ t = φ t - σ * a * t) :
    HasDerivAt ψ ((1 - σ) * a) 0 ∧ (1 - σ) * a < 0 ∧ Tendsto ψ atTop atTop ∧
      ∃ M z : ℝ, 0 < z ∧ z < M ∧ (∀ t ∈ Icc 0 M, ψ z ≤ ψ t) ∧ ψ z < ψ 0 := by
  have hψe : ψ = fun t => φ t - σ * a * t := funext hψ
  have hσ1 : σ < 1 := by rw [hσ]; linarith
  have hσ0 : 0 < σ := by rw [hσ]; linarith
  have hder : HasDerivAt ψ ((1 - σ) * a) 0 := by
    rw [hψe]
    have := hd.sub ((hasDerivAt_id (0 : ℝ)).const_mul (σ * a))
    convert this using 1
    simp only [mul_one]
    ring
  have hneg : (1 - σ) * a < 0 := mul_neg_of_pos_of_neg (by linarith) ha
  have hq : 0 < -σ * a := by nlinarith
  have htend : Tendsto ψ atTop atTop := by
    have hline : Tendsto (fun t : ℝ => L + (-σ * a) * t) atTop atTop :=
      tendsto_atTop_add_const_left _ L (Tendsto.const_mul_atTop hq tendsto_id)
    refine tendsto_atTop_mono' atTop ?_ hline
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [hψ]
    have := hL t ht
    linarith
  refine ⟨hder, hneg, htend, ?_⟩
  -- a point below ψ(0), then a far point above it, then a minimizer on the compact interval
  obtain ⟨v, hv, hdesc⟩ := FiniteRayLineSearch.negative_derivative_descends hder hneg
  obtain ⟨M, hM⟩ := (htend.eventually (eventually_gt_atTop (ψ 0))).and
    (eventually_gt_atTop v) |>.exists
  have hM0 : 0 < M := hv.trans hM.2
  have hcont : Continuous ψ := by
    rw [hψe]
    exact (continuous_iff_continuousOn_univ.mpr (hφ.continuousOn isOpen_univ)).sub
      (continuous_const.mul continuous_id)
  obtain ⟨z, hz, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hM0.le) hcont.continuousOn
  have hzv : ψ z ≤ ψ v := hmin ⟨hv.le, hM.2.le⟩
  have hz0 : ψ z < ψ 0 := hzv.trans_lt hdesc
  refine ⟨M, z, ?_, ?_, fun t ht => hmin ht, hz0⟩
  · rcases hz.1.eq_or_lt with h | h
    · rw [← h] at hz0; exact absurd hz0 (lt_irrefl _)
    · exact h
  · rcases hz.2.eq_or_lt with h | h
    · rw [h] at hz0; exact absurd (hz0.trans hM.1) (lt_irrefl _)
    · exact h

/-- Item `C/06_F/disp/024` (`companion/chapters/06_F.tex:190-192`): "Then
\[ \varphi(z)<\varphi(0)+\sigma az<\varphi(0)+c_1az." \]
Under the standing assumptions, for $0<z<M$ with $z$ a minimizer of $\psi$ on $[0,M]$ and
$\psi(z)<\psi(0)$ (the choice of `tilted_setup`). -/
theorem tilted_armijo (φ : ℝ → ℝ) (_hφ : ConvexOn ℝ univ φ) (L : ℝ) (_hL : ∀ t, 0 ≤ t → L ≤ φ t)
    (a : ℝ) (_hd : HasDerivAt φ a 0) (ha : a < 0) (c₁ c₂ : ℝ) (_hc₁ : 0 < c₁) (hc : c₁ < c₂)
    (_hc₂ : c₂ < 1) (σ : ℝ) (hσ : σ = (c₁ + c₂) / 2) (ψ : ℝ → ℝ)
    (hψ : ∀ t, ψ t = φ t - σ * a * t) (M z : ℝ) (hz : 0 < z) (_hzM : z < M)
    (_hmin : ∀ t ∈ Icc 0 M, ψ z ≤ ψ t) (hz0 : ψ z < ψ 0) :
    φ z < φ 0 + σ * a * z ∧ φ 0 + σ * a * z < φ 0 + c₁ * a * z := by
  rw [hψ, hψ] at hz0
  refine ⟨by linarith, ?_⟩
  have h1 : σ * a < c₁ * a := mul_lt_mul_of_neg_right (by rw [hσ]; linarith) ha
  have := mul_lt_mul_of_pos_right h1 hz
  linarith

/-- Item `C/06_F/prose/044` (`companion/chapters/06_F.tex:193`): "Continuity preserves strict
Armijo on an interval immediately to the right of $z$." Under the assumptions of `tilted_armijo`:
some $\varepsilon>0$ gives $\varphi(t)<\varphi(0)+c_1at$ for all $t\in(z,z+\varepsilon)$. -/
theorem tilted_armijo_interval (φ : ℝ → ℝ) (hφ : ConvexOn ℝ univ φ) (L : ℝ)
    (hL : ∀ t, 0 ≤ t → L ≤ φ t) (a : ℝ) (hd : HasDerivAt φ a 0) (ha : a < 0) (c₁ c₂ : ℝ)
    (hc₁ : 0 < c₁) (hc : c₁ < c₂) (hc₂ : c₂ < 1) (σ : ℝ) (hσ : σ = (c₁ + c₂) / 2) (ψ : ℝ → ℝ)
    (hψ : ∀ t, ψ t = φ t - σ * a * t) (M z : ℝ) (hz : 0 < z) (hzM : z < M)
    (hmin : ∀ t ∈ Icc 0 M, ψ z ≤ ψ t) (hz0 : ψ z < ψ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Ioo z (z + ε), φ t < φ 0 + c₁ * a * t := by
  have harm := (tilted_armijo φ hφ L hL a hd ha c₁ c₂ hc₁ hc hc₂ σ hσ ψ hψ M z hz hzM hmin
    hz0)
  have hcont : Continuous φ := continuous_iff_continuousOn_univ.mpr (hφ.continuousOn isOpen_univ)
  have hopen : IsOpen {t : ℝ | φ t < φ 0 + c₁ * a * t} :=
    isOpen_lt hcont (continuous_const.add (continuous_const.mul continuous_id))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds (show φ z < φ 0 + c₁ * a * z by
    linarith [harm.1, harm.2]))
  refine ⟨ε, hε, fun t ht => hball ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr ht.1)]
  linarith [ht.2]

/-- Item `C/06_F/disp/025` (`companion/chapters/06_F.tex:194-196`): "For each $t$ in a
sufficiently small such interval, minimality and convexity give
\[ \varphi'(t)\ge\frac{\varphi(t)-\varphi(z)}{t-z}\ge\sigma a>c_2a \]
whenever the scalar derivative exists." Under the assumptions of `tilted_armijo`, for every
$t\in(z,M]$ and every derivative $b$ of $\varphi$ at $t$. -/
theorem tilted_wolfe (φ : ℝ → ℝ) (hφ : ConvexOn ℝ univ φ) (L : ℝ) (_hL : ∀ t, 0 ≤ t → L ≤ φ t)
    (a : ℝ) (_hd : HasDerivAt φ a 0) (ha : a < 0) (c₁ c₂ : ℝ) (_hc₁ : 0 < c₁) (hc : c₁ < c₂)
    (_hc₂ : c₂ < 1) (σ : ℝ) (hσ : σ = (c₁ + c₂) / 2) (ψ : ℝ → ℝ)
    (hψ : ∀ t, ψ t = φ t - σ * a * t) (M z : ℝ) (hz : 0 < z) (_hzM : z < M)
    (hmin : ∀ t ∈ Icc 0 M, ψ z ≤ ψ t) (_hz0 : ψ z < ψ 0)
    (t : ℝ) (ht : t ∈ Ioc z M) (b : ℝ) (hb : HasDerivAt φ b t) :
    (φ t - φ z) / (t - z) ≤ b ∧ σ * a ≤ (φ t - φ z) / (t - z) ∧ c₂ * a < σ * a := by
  have hzt : z < t := ht.1
  refine ⟨?_, ?_, mul_lt_mul_of_neg_right (by rw [hσ]; linarith) ha⟩
  · have h := hφ.slope_le_of_hasDerivAt (mem_univ z) (mem_univ t) hzt hb
    rwa [slope_def_field] at h
  · have hm := hmin t ⟨hz.le.trans hzt.le, ht.2⟩
    rw [hψ, hψ] at hm
    rw [le_div_iff₀ (sub_pos.mpr hzt)]
    linarith

/-- Item `C/06_F/prose/045` (`companion/chapters/06_F.tex:197`): "Thus there is a nonempty open
interval of strict Armijo points whose actual scalar derivatives satisfy strict weak Wolfe."
Under the standing assumptions (library `FiniteRayLineSearch.acceptable_interval`, the
tilted-minimum construction). -/
theorem tilted_interval (φ : ℝ → ℝ) (hφ : ConvexOn ℝ univ φ) (L : ℝ) (hL : ∀ t, 0 ≤ t → L ≤ φ t)
    (a : ℝ) (hd : HasDerivAt φ a 0) (ha : a < 0) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc : c₁ < c₂)
    (hc₂ : c₂ < 1) :
    ∃ l u : ℝ, 0 < l ∧ l < u ∧ ∀ t ∈ Ioo l u,
      φ t < φ 0 + c₁ * a * t ∧ ∀ b : ℝ, HasDerivAt φ b t → c₂ * a < b :=
  FiniteRayLineSearch.acceptable_interval hφ hd ha hc₁ hc hc₂ L hL

/-- Item `C/06_F/prose/046` (`companion/chapters/06_F.tex:197`): "If full-space
nondifferentiability occurs at only finitely many positive ray times, choose a point in that
interval outside this finite set; its actual full gradient gives a differentiable acceptable
step." For finite convex $F$, a differentiable $x$ with gradient $g\ne0$, $H\succ0$, $F$ bounded
below on the BFGS ray $x-tHg$ ($t\ge0$) and finitely many $t>0$ where $F$ is not differentiable
at $x-tHg$: some $\alpha>0$ gives a differentiable point $x+s$, $s=-\alpha Hg$, with strict
Armijo and strict weak Wolfe (library `FiniteRayLineSearch.fullBFGS_step_exists`). -/
theorem finite_bad_ray_step {n : ℕ} (F : Vec n → ℝ) (hF : ConvexOn ℝ univ F) (x g : Vec n)
    (H : Mat n) (hH : H.PosDef) (hg0 : g ≠ 0) (hg : HasFDerivAt F (gradientFunctional g) x)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc : c₁ < c₂) (hc₂ : c₂ < 1)
    (L : ℝ) (hL : ∀ t, 0 ≤ t → L ≤ F (x + bfgsStep H g t))
    (hfin : {t | 0 < t ∧ ¬ DifferentiableAt ℝ F (x + bfgsStep H g t)}.Finite) :
    ∃ α h : _, 0 < α ∧ HasFDerivAt F (gradientFunctional h) (x + bfgsStep H g α) ∧
      F (x + bfgsStep H g α) < F x + c₁ * dot g (bfgsStep H g α) ∧
      c₂ * dot g (bfgsStep H g α) < dot h (bfgsStep H g α) :=
  FiniteRayLineSearch.fullBFGS_step_exists hF x g H hH hg0 hg hc₁ hc hc₂ L hL hfin

/-- Item `C/06_F/prose/048` (`companion/chapters/06_F.tex:197`): "It applies to finite affine
absolute-value/hinge sums and suitable Euclidean residual sums through their proved full-space
bad-ray-set finiteness." For $F=\psi+\sum_i|a_i^Tz-b_i|$ and for $F=\psi+\sum_i\max\{0,a_i^Tz-b_i\}$
with $\psi$ differentiable and $F$ convex, and every differentiable $x$ with $g\ne0$, $H\succ0$
and $F$ bounded below on the ray, a differentiable strict Armijo--weak-Wolfe step exists
(libraries `AffineKinks.absolute_fullBFGS_step_exists`, `hinge_fullBFGS_step_exists`); the
Euclidean residual sums $\psi+\sum_i\|A_iz-b_i\|$ are `euclidean_residual_step`. -/
theorem abs_hinge_step {n : ℕ} {ι : Type*} [Fintype ι] (F ψ : Vec n → ℝ)
    (hψ : Differentiable ℝ ψ) (a : ι → Vec n) (b : ι → ℝ) (hF : ConvexOn ℝ univ F)
    (x g : Vec n) (H : Mat n) (hH : H.PosDef) (hg0 : g ≠ 0)
    (hg : HasFDerivAt F (gradientFunctional g) x) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc : c₁ < c₂)
    (hc₂ : c₂ < 1) (L : ℝ) (hL : ∀ t, 0 ≤ t → L ≤ F (x + bfgsStep H g t)) :
    ((∀ z, F z = ψ z + ∑ i, |dot (a i) z - b i|) →
      ∃ α h : _, 0 < α ∧ HasFDerivAt F (gradientFunctional h) (x + bfgsStep H g α) ∧
        F (x + bfgsStep H g α) < F x + c₁ * dot g (bfgsStep H g α) ∧
        c₂ * dot g (bfgsStep H g α) < dot h (bfgsStep H g α)) ∧
    ((∀ z, F z = ψ z + ∑ i, max 0 (dot (a i) z - b i)) →
      ∃ α h : _, 0 < α ∧ HasFDerivAt F (gradientFunctional h) (x + bfgsStep H g α) ∧
        F (x + bfgsStep H g α) < F x + c₁ * dot g (bfgsStep H g α) ∧
        c₂ * dot g (bfgsStep H g α) < dot h (bfgsStep H g α)) :=
  ⟨fun hrep => AffineKinks.absolute_fullBFGS_step_exists hψ a b hrep hF x g H hH hg0 hg hc₁ hc
      hc₂ L hL,
    fun hrep => AffineKinks.hinge_fullBFGS_step_exists hψ a b hrep hF x g H hH hg0 hg hc₁ hc
      hc₂ L hL⟩

/-- Item `C/06_F/prose/048` (`companion/chapters/06_F.tex:197`), mixed sums: for
$F=\psi+\sum_i|a_i^Tz-b_i|+\sum_j\max\{0,c_j^Tz-d_j\}$ (absolute-value and hinge terms together)
with $\psi$ differentiable and $F$ convex, the same existence (library
`AffineKinks.fullBFGS_step_of_representation`, with the kinks of both kinds). -/
theorem mixed_kink_step {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ] (F ψ : Vec n → ℝ)
    (hψ : Differentiable ℝ ψ) (a : ι → Vec n) (b : ι → ℝ) (c : κ → Vec n) (d : κ → ℝ)
    (hrep : ∀ z, F z = ψ z + ∑ i, |dot (a i) z - b i| + ∑ j, max 0 (dot (c j) z - d j))
    (hF : ConvexOn ℝ univ F)
    (x g : Vec n) (H : Mat n) (hH : H.PosDef) (hg0 : g ≠ 0)
    (hg : HasFDerivAt F (gradientFunctional g) x) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc : c₁ < c₂)
    (hc₂ : c₂ < 1) (L : ℝ) (hL : ∀ t, 0 ≤ t → L ≤ F (x + bfgsStep H g t)) :
    ∃ α h : _, 0 < α ∧ HasFDerivAt F (gradientFunctional h) (x + bfgsStep H g α) ∧
      F (x + bfgsStep H g α) < F x + c₁ * dot g (bfgsStep H g α) ∧
      c₂ * dot g (bfgsStep H g α) < dot h (bfgsStep H g α) := by
  let P : ι ⊕ κ → AffineKinks.Kink n :=
    Sum.elim (fun i => AffineKinks.Kink.absolute (a i) (b i))
      (fun j => AffineKinks.Kink.hinge (c j) (d j))
  have hpen : ∀ z, AffineKinks.penalty P z =
      ∑ i, |dot (a i) z - b i| + ∑ j, max 0 (dot (c j) z - d j) := by
    intro z
    simp only [AffineKinks.penalty, Fintype.sum_sum_type, P, Sum.elim_inl, Sum.elim_inr,
      AffineKinks.Kink.absolute_value, AffineKinks.Kink.hinge_value]
  exact AffineKinks.fullBFGS_step_of_representation hψ P
    (fun z => by rw [hrep z, hpen, add_assoc]) hF x g H hH hg0 hg hc₁ hc hc₂ L hL

/-- Item `C/06_F/prose/048` (`companion/chapters/06_F.tex:197`), Euclidean residual sums: for
$F=\psi+\sum_i\|A_iz-b_i\|$ (Euclidean norms, $A_i$ rectangular) with $\psi$ differentiable and
$F$ convex, the same existence (library
`EuclideanResidual.matrix_euclidean_residual_fullBFGS_step_exists`). -/
theorem euclidean_residual_step {n : ℕ} {ι : Type*} [Fintype ι] {m : ι → ℕ} (F ψ : Vec n → ℝ)
    (hψ : Differentiable ℝ ψ) (A : ∀ i, Matrix (Fin (m i)) (Fin n) ℝ) (b : ∀ i, Vec (m i))
    (hrep : ∀ z, F z = ψ z + ∑ i, ‖euclideanVector (A i *ᵥ z - b i)‖) (hF : ConvexOn ℝ univ F)
    (x g : Vec n) (H : Mat n) (hH : H.PosDef) (hg0 : g ≠ 0)
    (hg : HasFDerivAt F (gradientFunctional g) x) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc : c₁ < c₂)
    (hc₂ : c₂ < 1) (L : ℝ) (hL : ∀ t, 0 ≤ t → L ≤ F (x + bfgsStep H g t)) :
    ∃ α h : _, 0 < α ∧ HasFDerivAt F (gradientFunctional h) (x + bfgsStep H g α) ∧
      F (x + bfgsStep H g α) < F x + c₁ * dot g (bfgsStep H g α) ∧
      c₂ * dot g (bfgsStep H g α) < dot h (bfgsStep H g α) :=
  EuclideanResidual.matrix_euclidean_residual_fullBFGS_step_exists hψ A b hrep hF x g H hH hg0 hg
    hc₁ hc hc₂ L hL

/-! #### The five-piece finite obstruction (`06_F.tex:199-203`) -/

/-- The five branch values of $h$. -/
theorem five_piece_branches (w : Vec 3) :
    (FivePieceObstruction.family.branch 0 w = -w 0) ∧
      (FivePieceObstruction.family.branch 1 w = w 1 + w 2) ∧
      (FivePieceObstruction.family.branch 2 w = -w 1 + w 2) ∧
      (FivePieceObstruction.family.branch 3 w = w 0 / 4) ∧
      (FivePieceObstruction.family.branch 4 w = -w 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [FivePieceObstruction.family, MaxAffine.Family.branch, dot, Fin.sum_univ_succ]
  all_goals ring

/-- Item `C/06_F/disp/026` (`companion/chapters/06_F.tex:200-202`): the function
\[ h(x,y,z)=\max\{-x,y+z,-y+z,x/4,-z\}. \]
The library's `FivePieceObstruction.objective` (the maximum of the five affine pieces of
`FivePieceObstruction.family`) is this formula, with $(x,y,z)=(w_0,w_1,w_2)$. -/
theorem five_piece_def (w : Vec 3) :
    FivePieceObstruction.objective w =
      max (max (max (max (-w 0) (w 1 + w 2)) (-w 1 + w 2)) (w 0 / 4)) (-w 2) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := five_piece_branches w
  have hle := fun i => FivePieceObstruction.family.branch_le i w
  apply le_antisymm
  · unfold FivePieceObstruction.objective MaxAffine.Family.objective
    apply Finset.sup'_le
    intro i _
    fin_cases i
    · simp only [Fin.zero_eta] at *; rw [h0]
      exact le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_left _ _)))
    · simp only [Fin.mk_one] at *; rw [h1]
      exact le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_right _ _)))
    · change FivePieceObstruction.family.branch 2 w ≤ _; rw [h2]
      exact le_max_of_le_left (le_max_of_le_left (le_max_right _ _))
    · change FivePieceObstruction.family.branch 3 w ≤ _; rw [h3]
      exact le_max_of_le_left (le_max_right _ _)
    · change FivePieceObstruction.family.branch 4 w ≤ _; rw [h4]
      exact le_max_right _ _
  · have e0 := hle 0; have e1 := hle 1; have e2 := hle 2; have e3 := hle 3; have e4 := hle 4
    rw [h0] at e0; rw [h1] at e1; rw [h2] at e2; rw [h3] at e3; rw [h4] at e4
    exact max_le (max_le (max_le (max_le e0 e1) e2) e3) e4

/-- Item `C/06_F/prose/051` (`companion/chapters/06_F.tex:199-203`): "The coercive function [$h$]
has unique minimizer zero." -/
theorem five_piece_minimizer :
    (∀ w, FivePieceObstruction.objective 0 ≤ FivePieceObstruction.objective w) ∧
      (∀ w, FivePieceObstruction.objective w = FivePieceObstruction.objective 0 → w = 0) ∧
      Tendsto FivePieceObstruction.objective (cocompact (Vec 3)) atTop ∧
      ConvexOn ℝ univ FivePieceObstruction.objective := by
  refine ⟨fun w => ?_, fun w hw => ?_, FivePieceObstruction.objective_coercive,
    FivePieceObstruction.objective_convex⟩
  · rw [FivePieceObstruction.objective_zero]; exact FivePieceObstruction.objective_nonneg w
  · rw [FivePieceObstruction.objective_zero] at hw; exact FivePieceObstruction.unique_minimum hw

/-- The obstruction's starting point, matrix and direction in the library's scaled form
($\tau=1$). -/
theorem five_piece_data (α : ℝ) :
    FivePieceObstruction.ray 1 α = ![-2, 0, 1] + α • ![1, 0, 0] ∧
      FivePieceObstruction.initialMetric 1 = 1 ∧
      bfgsStep (1 : Mat 3) ![-1, 0, 0] α = α • ![1, 0, 0] ∧
      FivePieceObstruction.initialGradient = ![-1, 0, 0] := by
  refine ⟨?_, by simp [FivePieceObstruction.initialMetric], ?_, rfl⟩
  · ext i
    fin_cases i
    all_goals simp [FivePieceObstruction.ray]
    all_goals ring
  · ext i; fin_cases i <;> simp [bfgsStep]

/-- Item `C/06_F/prose/052` (`companion/chapters/06_F.tex:203`): "At $(-2,0,1)$ with $H_0=I$,
the direction is $(1,0,0)$ and the ray function is $\max\{2-\alpha,1,(\alpha-2)/4\}$." The
gradient at $(-2,0,1)$ is $g_0=(-1,0,0)$, the direction is $-H_0g_0=(1,0,0)$, and for every real
$\alpha$, $h((-2,0,1)+\alpha(1,0,0))=\max\{2-\alpha,1,(\alpha-2)/4\}$. -/
theorem five_piece_ray :
    HasFDerivAt FivePieceObstruction.objective (gradientFunctional ![-1, 0, 0]) ![-2, 0, 1] ∧
      -((1 : Mat 3) *ᵥ ![-1, 0, 0]) = ![1, 0, 0] ∧
      ∀ α : ℝ, FivePieceObstruction.objective (![-2, 0, 1] + α • ![1, 0, 0]) =
        max (max (2 - α) 1) ((α - 2) / 4) := by
  refine ⟨?_, by ext i; fin_cases i <;> simp, fun α => ?_⟩
  · have h := FivePieceObstruction.ray_gradient_before (τ := 1) (α := 0) one_pos (by norm_num)
    rw [(five_piece_data 0).1] at h
    simpa [FivePieceObstruction.initialGradient] using h
  · rw [five_piece_def]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    have e1 : (-(-2 + α * 1)) = 2 - α := by ring
    have e2 : (0 + α * 0 + (1 + α * 0)) = 1 := by ring
    have e3 : (-(0 + α * 0) + (1 + α * 0)) = 1 := by ring
    have e4 : (-2 + α * 1) / 4 = (α - 2) / 4 := by ring
    have e5 : (-(1 + α * 0)) = -1 := by ring
    rw [e1, e2, e3, e4, e5, max_assoc (2 - α) 1 1, max_self]
    apply max_eq_left
    exact le_max_of_le_left (le_max_of_le_right (by norm_num))

/-- Item `C/06_F/prose/053` (`companion/chapters/06_F.tex:203`): "For $(c_1,c_2)=(1/4,1/2)$, times
$0<\alpha<1$ fail weak Wolfe; $1\le\alpha\le6$ are full-space nondifferentiable; and $\alpha>6$
fails Armijo, which would require $\alpha\le5$." With $x_0=(-2,0,1)$, $g_0=(-1,0,0)$, $H_0=I$,
$s=-\alpha H_0g_0$: for $0<\alpha<1$, $h$ is differentiable at $x_0+s$ with gradient $g_0$ and
$g_0^Ts<c_2g_0^Ts$; for $1\le\alpha\le6$, $h$ is not differentiable at $x_0+s$; for $\alpha\ge6$,
Armijo $h(x_0+s)\le h(x_0)+c_1g_0^Ts$ holds exactly when $\alpha\le5$ (so it fails for
$\alpha>6$); hence no $\alpha>0$ gives a differentiable Armijo--weak-Wolfe point (library
`FivePieceObstruction.no_differentiable_armijo_wolfe`). -/
theorem five_piece_obstruction :
    (∀ α : ℝ, 0 < α → α < 1 →
      HasFDerivAt FivePieceObstruction.objective (gradientFunctional ![-1, 0, 0])
        (![-2, 0, 1] + bfgsStep 1 ![-1, 0, 0] α) ∧
      dot ![-1, 0, 0] (bfgsStep 1 ![-1, 0, 0] α) <
        1 / 2 * dot ![-1, 0, 0] (bfgsStep 1 ![-1, 0, 0] α)) ∧
    (∀ α : ℝ, 1 ≤ α → α ≤ 6 →
      ¬ DifferentiableAt ℝ FivePieceObstruction.objective
        (![-2, 0, 1] + bfgsStep 1 ![-1, 0, 0] α)) ∧
    (∀ α : ℝ, 6 ≤ α →
      (FivePieceObstruction.objective (![-2, 0, 1] + bfgsStep 1 ![-1, 0, 0] α) ≤
          FivePieceObstruction.objective ![-2, 0, 1] +
            1 / 4 * dot ![-1, 0, 0] (bfgsStep 1 ![-1, 0, 0] α) ↔ α ≤ 5)) ∧
    (∀ α : ℝ, 0 < α → ∀ g : Vec 3,
      HasFDerivAt FivePieceObstruction.objective (gradientFunctional g)
        (![-2, 0, 1] + bfgsStep 1 ![-1, 0, 0] α) →
      ¬ (FivePieceObstruction.objective (![-2, 0, 1] + bfgsStep 1 ![-1, 0, 0] α) ≤
          FivePieceObstruction.objective ![-2, 0, 1] +
            1 / 4 * dot ![-1, 0, 0] (bfgsStep 1 ![-1, 0, 0] α) ∧
        1 / 2 * dot ![-1, 0, 0] (bfgsStep 1 ![-1, 0, 0] α) ≤
          dot g (bfgsStep 1 ![-1, 0, 0] α))) := by
  have hpt : ∀ α : ℝ, ![-2, 0, 1] + bfgsStep (1 : Mat 3) ![-1, 0, 0] α =
      FivePieceObstruction.ray 1 α := fun α => by
    rw [(five_piece_data α).1, (five_piece_data α).2.2.1]
  have hx0 : (![-2, 0, 1] : Vec 3) = FivePieceObstruction.ray 1 0 := by
    rw [(five_piece_data 0).1]; simp
  have hdot : ∀ α : ℝ, dot ![-1, 0, 0] (bfgsStep (1 : Mat 3) ![-1, 0, 0] α) = -α := fun α => by
    rw [(five_piece_data α).2.2.1]; simp [dot, Fin.sum_univ_succ]
  refine ⟨fun α h0 h1 => ⟨?_, ?_⟩, fun α h1 h6 => ?_, fun α h6 => ?_, fun α h0 g hg => ?_⟩
  · rw [hpt]
    simpa [FivePieceObstruction.initialGradient] using
      FivePieceObstruction.ray_gradient_before (τ := 1) one_pos h1
  · rw [hdot]; linarith
  · rw [hpt]; exact FivePieceObstruction.ray_not_differentiable_middle one_pos h1 h6
  · rw [hpt, hx0, hdot, FivePieceObstruction.ray_value_after one_pos h6,
      FivePieceObstruction.ray_value_before one_pos (by norm_num : (0 : ℝ) ≤ 1)]
    constructor <;> intro h <;> linarith
  · have hm := FivePieceObstruction.no_differentiable_armijo_wolfe (τ := 1) one_pos h0 g
    rw [(five_piece_data α).2.1, (five_piece_data α).2.2.2] at hm
    rw [hpt, hx0] at *
    exact fun hacc => hm hg hacc.1 hacc.2

/-- Item `C/06_F/prose/054` (`companion/chapters/06_F.tex:203`): "Scaling the point and matrix
places the same finite obstruction arbitrarily close to the minimizer." For every neighborhood
$K$ of $0$ some $\tau>0$ gives the point $\tau(-2,0,1)\in K$, the SPD matrix $\tau I$, gradient
$(-1,0,0)$ there, and no $\alpha>0$ with a differentiable Armijo--weak-Wolfe point for
$(c_1,c_2)=(1/4,1/2)$ (library `FivePieceObstruction.obstruction_in_every_neighborhood`). -/
theorem five_piece_every_neighborhood (K : Set (Vec 3)) (hK : K ∈ 𝓝 0) :
    ∃ τ : ℝ, 0 < τ ∧ FivePieceObstruction.ray τ 0 ∈ K ∧
      (FivePieceObstruction.initialMetric τ).PosDef ∧
      HasFDerivAt FivePieceObstruction.objective
        (gradientFunctional FivePieceObstruction.initialGradient) (FivePieceObstruction.ray τ 0) ∧
      ∀ α : ℝ, 0 < α → ∀ g : Vec 3,
        HasFDerivAt FivePieceObstruction.objective (gradientFunctional g)
          (FivePieceObstruction.ray τ α) →
        ¬ (FivePieceObstruction.objective (FivePieceObstruction.ray τ α) ≤
            FivePieceObstruction.objective (FivePieceObstruction.ray τ 0) +
              1 / 4 * dot FivePieceObstruction.initialGradient
                (bfgsStep (FivePieceObstruction.initialMetric τ)
                  FivePieceObstruction.initialGradient α) ∧
          1 / 2 * dot FivePieceObstruction.initialGradient
              (bfgsStep (FivePieceObstruction.initialMetric τ)
                FivePieceObstruction.initialGradient α) ≤
            dot g (bfgsStep (FivePieceObstruction.initialMetric τ)
              FivePieceObstruction.initialGradient α)) :=
  FivePieceObstruction.obstruction_in_every_neighborhood K hK

/-- Item `C/06_F/prose/066` (`companion/chapters/06_F.tex:216`): "Differentiability of the
restriction to a ray does not imply full-space differentiability at acceptance." On the ray of the
five-piece obstruction, $\varphi(\alpha)=h((-2,0,1)+\alpha(1,0,0))$ has $\varphi'(0)=-1$ and is
differentiable at $\alpha=3$ with $\varphi'(3)=0$; $\alpha=3$ satisfies the scalar Armijo and
weak-Wolfe tests for $(c_1,c_2)=(1/4,1/2)$, but $h$ is not differentiable at the point. -/
theorem ray_differentiability_not_full :
    let φ := fun α : ℝ => FivePieceObstruction.objective (![-2, 0, 1] + α • ![1, 0, 0])
    HasDerivAt φ (-1) 0 ∧ HasDerivAt φ 0 3 ∧ φ 3 ≤ φ 0 + 1 / 4 * (-1) * 3 ∧
      1 / 2 * (-1 : ℝ) ≤ 0 ∧
      ¬ DifferentiableAt ℝ FivePieceObstruction.objective (![-2, 0, 1] + (3 : ℝ) • ![1, 0, 0]) := by
  intro φ
  obtain ⟨hg, -, hray⟩ := five_piece_ray
  have hφ : ∀ α, φ α = max (max (2 - α) 1) ((α - 2) / 4) := hray
  refine ⟨?_, ?_, ?_, by norm_num, ?_⟩
  · have h := FiniteRayLineSearch.ray_hasDerivAt (![-2, 0, 1] : Vec 3) ![1, 0, 0] 0
      (g := ![-1, 0, 0]) (by simpa using hg)
    have hd : dot ![-1, 0, 0] (![1, 0, 0] : Vec 3) = -1 := by simp [dot, Fin.sum_univ_succ]
    rw [hd] at h
    exact h
  · have heq : φ =ᶠ[𝓝 3] fun _ => (1 : ℝ) := by
      filter_upwards [Ioo_mem_nhds (by norm_num : (1 : ℝ) < 3) (by norm_num : (3 : ℝ) < 6)] with
        α hα
      rw [hφ, max_eq_right (show 2 - α ≤ 1 by linarith [hα.1]),
        max_eq_left (show (α - 2) / 4 ≤ 1 by linarith [hα.2])]
    exact (hasDerivAt_const (3 : ℝ) (1 : ℝ)).congr_of_eventuallyEq heq
  · rw [hφ, hφ]; norm_num
  · have h := (five_piece_obstruction).2.1 3 (by norm_num) (by norm_num)
    rwa [(five_piece_data 3).2.2.1] at h

/-! ### Relation to earlier work (`06_F.tex:207-216`) -/

/-- Item `C/06_F/prose/058` (`companion/chapters/06_F.tex:210`): "The theorem in this chapter
gives full convergence for that example within its centered family." Theorem `F:centered` with
$\psi(u,v)=u^2$, $\gamma(u,v)=|v|$, $x_*=0$, $U=\R^2$ gives, for $F(u,v)=u^2+|v|$ and every
infinite admissible run, $F(x_k)\to0$ and $x_k\to0$ (full sequence convergence). -/
theorem mixed_full_convergence (F : Vec 2 → ℝ) (hF : ∀ x, F x = (x 0) ^ 2 + |x 1|)
    (R : AdmissibleBFGSRun 2 F) :
    Tendsto (fun k => F (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0) := by
  obtain ⟨-, hmin, hunique, hK, hψ, hψ11, hγ, hγh, hrep⟩ :=
    BfgsCoverage.Article.Global.mixed_hypotheses F hF
  have hF0 : F 0 = 0 := by simp [hF]
  obtain ⟨hv, hi⟩ := centered 0 (fun x : Vec 2 => (x 0) ^ 2) (fun x : Vec 2 => |x 1|) hrep univ
    isOpen_univ convex_univ (hψ.subset (subset_univ _) convex_univ) hψ11 hγ hγh hmin R (hK _)
    (subset_univ _)
  exact ⟨by rwa [hF0] at hv, hi hunique⟩

/-- Item `C/06_F/prose/059` (`companion/chapters/06_F.tex:210`): "Its smooth secant estimate uses
established cocoercivity~\cite[Theorem~2.5]{WW}: local regularity is used on an open convex
neighborhood, with compact buffers and, where needed, an enlarged constant." The cocoercivity
estimate used in the proof of Theorem `F:centered`: for $\psi$ convex and locally $C^{1,1}$ on an
open convex $U$ and compact $K\subset U$, some $L>0$ gives
$\|\nabla\psi(y)-\nabla\psi(x)\|^2\le L(\nabla\psi(y)-\nabla\psi(x))^T(y-x)$ for all $x,y\in K$
(library `CenteredSmoothSublinear.exists_cocoercivity_constant_on_compact`, proved with compact
buffers and the Bregman estimate `bregman_lower_of_descent`). -/
theorem cocoercivity_on_compact {n : ℕ} (ψ : Vec n → ℝ) (U K : Set (Vec n)) (hU : IsOpen U)
    (_hUc : Convex ℝ U) (hψ : ConvexOn ℝ U ψ) (hψ11 : CenteredSmoothSublinear.LocallyC11On U ψ)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ L : ℝ, 0 < L ∧ ∀ x ∈ K, ∀ y ∈ K,
      ‖euclideanVector (coordinateGradient ψ y - coordinateGradient ψ x)‖ ^ 2 ≤
        L * dot (coordinateGradient ψ y - coordinateGradient ψ x) (y - x) := by
  obtain ⟨L, hL, h⟩ := CenteredSmoothSublinear.exists_cocoercivity_constant_on_compact hU hψ hψ11
    hK hKU
  exact ⟨L, hL, fun x hx y hy => by rw [norm_sq]; exact h x hx y hy⟩

/-- The gradient of a differentiable function is its coordinate gradient. -/
theorem coordinateGradient_of_hasFDerivAt {n : ℕ} {f : Vec n → ℝ} {x g : Vec n}
    (hg : HasFDerivAt f (gradientFunctional g) x) : coordinateGradient f x = g :=
  gradient_unique (hasFDerivAt_coordinateGradient hg.differentiableAt) hg

/-- Item `C/06_F/prose/060` (`companion/chapters/06_F.tex:210`): "It does not require a globally
Lipschitz gradient or minimization of each original summand at the center." For
$F(x)=x^4+|x|$ on $\R$ with $\psi(x)=x^4$, $\gamma(r)=|r|$, $x_*=0$, $U=\R$: every hypothesis of
Theorem `F:centered` holds (all sublevels compact), so every admissible run converges, while
$\nabla\psi(x)=4x^3$ has no global Lipschitz constant. The summands need not be minimized at the
center: `BfgsCoverage.Article.Global.centered_summands_not_minimized`. -/
theorem centered_no_global_lipschitz (F : Vec 1 → ℝ) (hF : ∀ x, F x = (x 0) ^ 4 + |x 0|) :
    (ConvexOn ℝ univ (fun x : Vec 1 => (x 0) ^ 4) ∧
      CenteredSmoothSublinear.LocallyC11On univ (fun x : Vec 1 => (x 0) ^ 4) ∧
      ConvexOn ℝ univ (fun x : Vec 1 => |x 0|) ∧
      Homogeneous.PositiveDegreeOne (fun x : Vec 1 => |x 0|) ∧
      (∀ x, F x = (x 0) ^ 4 + |(x - 0) 0|) ∧ (∀ x, F 0 ≤ F x) ∧
      (∀ b : ℝ, IsCompact {x | F x ≤ b})) ∧
    (∀ R : AdmissibleBFGSRun 1 F,
      Tendsto (fun k => F (R.x k)) atTop (𝓝 (F 0)) ∧ Tendsto R.x atTop (𝓝 0)) ∧
    ¬ ∃ L : ℝ, ∀ x y : Vec 1,
      sqNorm (coordinateGradient (fun x : Vec 1 => (x 0) ^ 4) y -
        coordinateGradient (fun x : Vec 1 => (x 0) ^ 4) x) ≤ L ^ 2 * sqNorm (y - x) := by
  have hψc : ConvexOn ℝ univ (fun x : Vec 1 => (x 0) ^ 4) := by
    have h := (Even.convexOn_pow (𝕜 := ℝ) (show Even 4 by decide)).comp_linearMap
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)
    simpa using h
  have hψ11 : CenteredSmoothSublinear.LocallyC11On univ (fun x : Vec 1 => (x 0) ^ 4) :=
    ConvexCellRadial.contDiffOn_two_locallyC11 isOpen_univ
      (by fun_prop : ContDiff ℝ 2 (fun x : Vec 1 => (x 0) ^ 4)).contDiffOn
  have hγc : ConvexOn ℝ univ (fun x : Vec 1 => |x 0|) :=
    BfgsCoverage.Article.Global.abs_coord_convex
  have hγh : Homogeneous.PositiveDegreeOne (fun x : Vec 1 => |x 0|) := by
    intro t ht x
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg ht]
  have hrep : ∀ x, F x = (x 0) ^ 4 + |(x - 0) 0| := fun x => by rw [hF, sub_zero]
  have hF0 : F 0 = 0 := by simp [hF]
  have hmin : ∀ x, F 0 ≤ F x := fun x => by rw [hF0, hF]; positivity
  have huniq : ∀ x, F x = F 0 → x = 0 := by
    intro x hx
    rw [hF, hF0] at hx
    have h0 : x 0 = 0 := by
      have := abs_nonneg (x 0)
      have := pow_nonneg (sq_nonneg (x 0)) 2
      have habs : |x 0| = 0 := by nlinarith [pow_two_nonneg ((x 0) ^ 2)]
      exact abs_eq_zero.mp habs
    ext i
    fin_cases i
    exact h0
  have hconv : ConvexOn ℝ univ F := (hψc.add hγc).congr (fun x _ => (hF x).symm)
  have hK := Localization.sublevel_compact hconv 0 hmin huniq
  refine ⟨⟨hψc, hψ11, hγc, hγh, hrep, hmin, hK⟩, fun R => ?_, ?_⟩
  · obtain ⟨hv, hi⟩ := centered 0 (fun x : Vec 1 => (x 0) ^ 4) (fun x : Vec 1 => |x 0|) hrep univ
      isOpen_univ convex_univ (hψc.subset (subset_univ _) convex_univ) hψ11 hγc hγh hmin R (hK _)
      (subset_univ _)
    exact ⟨hv, hi fun y hy => huniq y (le_antisymm (hy 0) (hmin y))⟩
  · rintro ⟨L, hL⟩
    have hgrad : ∀ x : Vec 1,
        coordinateGradient (fun x : Vec 1 => (x 0) ^ 4) x = ![4 * (x 0) ^ 3] := by
      intro x
      apply coordinateGradient_of_hasFDerivAt
      have h := ((hasDerivAt_pow 4 (x 0)).comp_hasFDerivAt x
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).hasFDerivAt)
      convert h using 1
      ext v
      simp [gradientFunctional_apply, dot]
    set t : ℝ := |L| + 2 with ht
    have ht1 : 1 ≤ t := by rw [ht]; linarith [abs_nonneg L]
    have h := hL 0 ![t]
    rw [hgrad, hgrad] at h
    simp [sqNorm] at h
    have hL2 : L ^ 2 = |L| ^ 2 := (sq_abs L).symm
    have hLt : L ^ 2 ≤ t ^ 2 := by
      rw [hL2]; exact pow_le_pow_left₀ (abs_nonneg L) (by rw [ht]; linarith) 2
    have e1 : (4 * t ^ 3) ^ 2 = 16 * t ^ 6 := by ring
    have e2 : L ^ 2 * t ^ 2 ≤ t ^ 2 * t ^ 2 := mul_le_mul_of_nonneg_right hLt (sq_nonneg t)
    have e3 : t ^ 4 ≤ t ^ 6 := pow_le_pow_right₀ ht1 (by norm_num)
    have e4 : 0 < t ^ 4 := by positivity
    have e5 : t ^ 2 * t ^ 2 = t ^ 4 := by ring
    linarith

/-! ### Non-vacuity -/

/-- The run on $u^2+|v|$ used in the examples ($A=1$, $v_0=1$, $\rho=1/4$, $c_1=1/4$,
$c_2=1/2$). -/
def mixedRun : AdmissibleBFGSRun 2 UnexcitedMetric.objective :=
  UnexcitedMetric.run 1 1 (1 / 4) (1 / 4) (1 / 2) one_pos one_pos (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- The standing assumptions of Theorem `F:centered` and of the displays of its proof
(`centered_split_notation`, `centered_split_bounds`, `centered_secant_bound`) can all hold: the
benchmark $u^2+|v|$ with $\psi(u,v)=u^2$, $\gamma(u,v)=|v|$, $x_*=0$, $U=\R^2$, the explicit run
`mixedRun`, a radius of its compact initial sublevel, a cocoercivity constant and a subgradient
bound. The same run shows that the "every run" conclusions of `centered` and
`mixed_full_convergence` are not vacuous. -/
example : ∃ (F ψ γ : Vec 2 → ℝ) (xstar : Vec 2) (U : Set (Vec 2)) (R : AdmissibleBFGSRun 2 F)
    (Rad L Gγ : ℝ),
    (∀ x, F x = ψ x + γ (x - xstar)) ∧ IsOpen U ∧ Convex ℝ U ∧ ConvexOn ℝ U ψ ∧
      CenteredSmoothSublinear.LocallyC11On U ψ ∧ ConvexOn ℝ univ γ ∧
      Homogeneous.PositiveDegreeOne γ ∧ (∀ x, F xstar ≤ F x) ∧
      IsCompact {x | F x ≤ F (R.x 0)} ∧ {x | F x ≤ F (R.x 0)} ⊆ U ∧
      (∀ x ∈ {x | F x ≤ F (R.x 0)}, ‖euclideanVector (x - xstar)‖ ≤ Rad) ∧ 0 < L ∧
      (∀ x ∈ {x | F x ≤ F (R.x 0)}, ∀ y ∈ {x | F x ≤ F (R.x 0)},
        ‖euclideanVector (coordinateGradient ψ y - coordinateGradient ψ x)‖ ^ 2 ≤
          L * dot (coordinateGradient ψ y - coordinateGradient ψ x) (y - x)) ∧
      (∀ x h, Homogeneous.Supports γ x h → ‖euclideanVector h‖ ≤ Gγ) := by
  obtain ⟨-, hmin, -, hK, hψ, hψ11, hγ, hγh, hrep⟩ :=
    BfgsCoverage.Article.Global.mixed_hypotheses UnexcitedMetric.objective (fun _ => rfl)
  obtain ⟨Rad, hRad0, hRad⟩ := compact_sqNorm_radius (hK (UnexcitedMetric.objective
    (mixedRun.x 0))) (0 : Vec 2)
  obtain ⟨L, hL0, hL⟩ := cocoercivity_on_compact (fun x : Vec 2 => (x 0) ^ 2) univ
    {x | UnexcitedMetric.objective x ≤ UnexcitedMetric.objective (mixedRun.x 0)} isOpen_univ
    convex_univ hψ hψ11 (hK _) (subset_univ _)
  obtain ⟨G, hG0, hG⟩ := Homogeneous.global_supporting_bound hγ hγh
  exact ⟨_, _, _, 0, univ, mixedRun, Rad, L, G, hrep, isOpen_univ, convex_univ, hψ, hψ11, hγ,
    hγh, hmin, hK _, subset_univ _,
    fun x hx => BfgsCoverage.Article.Global.norm_le_of_sqNorm_le hRad0.le (hRad x hx), hL0, hL,
    fun x h hs => BfgsCoverage.Article.Global.norm_le_of_sqNorm_le hG0.le (hG x h hs)⟩

/-- $|x|$ on $\R$ is convex, positively homogeneous and coercive. -/
theorem abs_facts : ConvexOn ℝ univ (fun x : Vec 1 => |x 0|) ∧
    Homogeneous.PositiveDegreeOne (fun x : Vec 1 => |x 0|) ∧
    Tendsto (fun x : Vec 1 => |x 0|) (cocompact (Vec 1)) atTop := by
  have hhom : Homogeneous.PositiveDegreeOne (fun x : Vec 1 => |x 0|) := by
    intro t ht x
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg ht]
  have hpos : ∀ x : Vec 1, x ≠ 0 → 0 < |x 0| := by
    intro x hx
    refine abs_pos.mpr fun h0 => hx ?_
    ext i
    rw [Subsingleton.elim i 0]
    exact h0
  exact ⟨BfgsCoverage.Article.Global.abs_coord_convex, hhom,
    BfgsCoverage.Article.Global.coercive_of_positive le_rfl
      BfgsCoverage.Article.Global.abs_coord_convex hhom hpos⟩

/-- The hypotheses of Theorem `F:transform` can hold, with an admissible run: $\Phi=\mathrm{id}$,
$\gamma(x)=|x|$ on $\R$, $x_*=0$, $F(x)=|x|$ and the article's run `absRun`. (The displays of
its proof are stated without the proof's contradiction hypothesis $F_k\ge L>0$ for all $k$,
which the theorem shows cannot hold; see the example after `transform_correction_annulus`.) -/
example : ∃ (γ : Vec 1 → ℝ) (Φ : ℝ → ℝ) (F : Vec 1 → ℝ) (xstar : Vec 1),
    ConvexOn ℝ univ γ ∧ Homogeneous.PositiveDegreeOne γ ∧ Tendsto γ (cocompact (Vec 1)) atTop ∧
      ContinuousOn Φ (Ici 0) ∧ ConvexOn ℝ (Ici 0) Φ ∧ StrictMonoOn Φ (Ici 0) ∧ Φ 0 = 0 ∧
      ContDiffOn ℝ 2 Φ (Ioi 0) ∧ (∀ r, 0 < r → 0 < deriv Φ r) ∧
      (∀ x, F x = Φ (γ (x - xstar))) ∧ Nonempty (AdmissibleBFGSRun 1 F) := by
  obtain ⟨h1, h2, h3⟩ := abs_facts
  refine ⟨fun x => |x 0|, id, fun x => |x 0|, 0, h1, h2, h3, continuousOn_id,
    convexOn_id (convex_Ici 0), strictMonoOn_id, rfl, contDiffOn_id, fun r _ => by simp,
    fun x => by simp, ⟨BfgsCoverage.Article.Global.absRun _ fun _ => rfl⟩⟩

/-- Every admissible run on $|x|$ converges to $0$ (Theorem `F:transform` with $\Phi=\mathrm{id}$).
-/
theorem abs_run_tendsto (R : AdmissibleBFGSRun 1 (fun x : Vec 1 => |x 0|)) :
    Tendsto R.x atTop (𝓝 0) := by
  obtain ⟨h1, h2, h3⟩ := abs_facts
  exact transform (fun x : Vec 1 => |x 0|) h1 h2 h3 id continuousOn_id (convexOn_id (convex_Ici 0))
    strictMonoOn_id rfl contDiffOn_id (fun r _ => by simp) 0 _ (fun x => by simp) R

/-- The standing assumptions of the max-affine paragraph (`maxAffine_active` and the threshold
theorems) can hold with an admissible run below the threshold: $p(x)=\max\{x,-x\}$ on $\R$,
$\psi=0$, $F=p$, $x_*=0$, $I_*=\{0,1\}$, $q(z)=|z|$, $\tau_*=+\infty$ (no inactive piece) and
`absRun`. -/
example : ∃ (a : Fin 2 → Vec 1) (b : Fin 2 → ℝ) (p ψ F : Vec 1 → ℝ) (xstar : Vec 1)
    (I : Finset (Fin 2)) (q : Vec 1 → ℝ) (τ : EReal) (R : AdmissibleBFGSRun 1 F),
    (∀ x, IsGreatest (Set.range fun i => dot (a i) x + b i) (p x)) ∧ ConvexOn ℝ univ ψ ∧
      CenteredSmoothSublinear.LocallyC11On univ ψ ∧ (∀ x, F x = ψ x + p x) ∧
      (∀ x, F xstar ≤ F x) ∧ (∀ x, F x = F xstar → x = xstar) ∧
      (∀ i, i ∈ I ↔ dot (a i) xstar + b i = p xstar) ∧
      (∀ z, IsGreatest ((fun i => dot (a i) z) '' I) (q z)) ∧
      (τ = ⨅ j : {j : Fin 2 // j ∉ I},
        sInf ((fun x => (F x : EReal)) '' {x | dot (a j.1) x + b j.1 = p x})) ∧
      (F (R.x 0) : EReal) < τ := by
  have hgr : ∀ x : Vec 1, IsGreatest (Set.range fun i =>
      dot (![![1], ![-1]] i) x + (0 : Fin 2 → ℝ) i) (|x 0|) := by
    intro x
    have h0 : dot ![1] x = x 0 := by simp [dot]
    have h1 : dot ![-1] x = -x 0 := by simp [dot]
    refine ⟨?_, ?_⟩
    · rcases abs_choice (x 0) with h | h
      · exact ⟨0, by simp [h0, h]⟩
      · exact ⟨1, by simp [h1, h]⟩
    · rintro _ ⟨i, rfl⟩
      fin_cases i
      · simp [h0, le_abs_self]
      · simp [h1, neg_le_abs]
  have hq : ∀ z : Vec 1, IsGreatest ((fun i => dot (![![1], ![-1]] i) z) '' (Finset.univ :
      Finset (Fin 2))) (|z 0|) := by
    intro z
    simpa using hgr z
  refine ⟨![![1], ![-1]], 0, fun x => |x 0|, fun _ => 0, fun x => |x 0|, 0, Finset.univ,
    fun z => |z 0|, ⊤, BfgsCoverage.Article.Global.absRun _ fun _ => rfl, hgr,
    convexOn_const 0 convex_univ, ?_, fun x => by simp, fun x => by simp,
    fun x hx => ?_, fun i => ?_, hq, ?_, EReal.coe_lt_top _⟩
  · exact ConvexCellRadial.contDiffOn_two_locallyC11 isOpen_univ contDiffOn_const
  · ext i
    rw [Subsingleton.elim i 0]
    simpa using hx
  · fin_cases i <;> simp [dot]
  · haveI : IsEmpty {j : Fin 2 // j ∉ (Finset.univ : Finset (Fin 2))} :=
      ⟨fun j => j.2 (Finset.mem_univ _)⟩
    exact (iInf_of_empty _).symm

/-- The hypotheses of Theorem `F:lifting` can hold: $A=I_1$ (full row rank), $\bar F(z)=|z|$,
$F=\bar F\circ A$, the unique optimizer $z_*=0$ of $\bar F$, and `absRun`, whose iterates converge
to $0$. -/
example : ∃ (A : Matrix (Fin 1) (Fin 1) ℝ) (Fbar F : Vec 1 → ℝ) (R : AdmissibleBFGSRun 1 F)
    (zstar : Vec 1), Function.Injective Aᵀ.mulVec ∧ (∀ x, F x = Fbar (A *ᵥ x)) ∧
      (∀ z, Fbar zstar ≤ Fbar z) ∧ (∀ z, Fbar z = Fbar zstar → z = zstar) ∧
      Tendsto (fun k => A *ᵥ R.x k) atTop (𝓝 zstar) := by
  let R := BfgsCoverage.Article.Global.absRun (fun x : Vec 1 => |x 0|) fun _ => rfl
  refine ⟨1, fun z => |z 0|, fun x => |x 0|, R, 0, ?_, fun x => by simp, fun z => by simp,
    fun z hz => ?_, ?_⟩
  · intro u v h; simpa using h
  · ext i; rw [Subsingleton.elim i 0]; simpa using hz
  · simpa using abs_run_tendsto R

/-- The standing assumptions of the rate statements `linear_budget_rate` and
`bounded_correction_rate` can hold: `mixedRun` on $u^2+|v|$ with $x_*=0$ has bounded gradients
(compact initial sublevel) and uniformly bounded corrections $R_k\le\bar R$ (the centered
estimate). -/
example : ∃ (F : Vec 2 → ℝ) (R : AdmissibleBFGSRun 2 F) (xstar : Vec 2) (Rbar : ℝ),
    (∀ x, F xstar ≤ F x) ∧ (∃ G : ℝ, ∀ k, ‖euclideanVector (R.g k)‖ ≤ G) ∧
      ∀ k, dot (R.gradientChange k) (R.x (k + 1) - xstar) ^ 2 / R.curvature k ≤ Rbar := by
  obtain ⟨-, hmin, -, hK, hψ, hψ11, hγ, hγh, hrep⟩ :=
    BfgsCoverage.Article.Global.mixed_hypotheses UnexcitedMetric.objective (fun _ => rfl)
  obtain ⟨L, G, Rr, -, -, -, hbound⟩ := mixedRun.centered_uniform_correction 0 isOpen_univ
    (hψ.subset (subset_univ _) convex_univ) hψ11 hγ hγh (fun x _ => hrep x) (hK _)
    (subset_univ _)
  exact ⟨_, mixedRun, 0, _, hmin, bounded_of_compact mixedRun (hK _), fun k => hbound k⟩

/-- The standing assumptions of the homogeneous rate statements can hold: $F(x)=|x|$ is convex,
positively homogeneous of degree one, bounded below and coercive, with the run `absRun`. -/
example : ∃ (F : Vec 1 → ℝ), Homogeneous.PositiveDegreeOne F ∧ (∃ L : ℝ, ∀ x, L ≤ F x) ∧
    Tendsto F (cocompact (Vec 1)) atTop ∧ Nonempty (AdmissibleBFGSRun 1 F) := by
  obtain ⟨-, h2, h3⟩ := abs_facts
  exact ⟨fun x => |x 0|, h2, ⟨0, fun x => abs_nonneg _⟩, h3,
    ⟨BfgsCoverage.Article.Global.absRun _ fun _ => rfl⟩⟩

/-- The standing assumptions of the quadratic-plus-gauge paragraph can hold with an admissible
run: $m=p=1$, $Q=\operatorname{diag}(2)$, $\gamma(v)=|v|$, $\mu=\Lambda=1$, so that
$F(u,v)=u^2+|v|$, and `mixedRun`. -/
example : ∃ (Q : Mat 1) (γ : Vec 1 → ℝ) (μ Λ : ℝ) (F : Vec (1 + 1) → ℝ),
    Q.PosDef ∧ ConvexOn ℝ univ γ ∧ Homogeneous.PositiveDegreeOne γ ∧ 0 < μ ∧
      (∀ v, μ * ‖euclideanVector v‖ ≤ γ v) ∧ (∀ v, γ v ≤ Λ * ‖euclideanVector v‖) ∧
      (∀ x, F x = dot (QuadraticGauge.left x) (Q *ᵥ QuadraticGauge.left x) / 2 +
        γ (QuadraticGauge.right x)) ∧ Nonempty (AdmissibleBFGSRun (1 + 1) F) := by
  obtain ⟨h1, h2, -⟩ := abs_facts
  have hnorm : ∀ v : Vec 1, ‖euclideanVector v‖ = |v 0| := fun v => by
    rw [BfgsCoverage.Article.Global.norm_euclideanVector, ← Real.sqrt_sq_eq_abs]
    simp [sqNorm]
  refine ⟨Matrix.diagonal (fun _ => 2), fun v => |v 0|, 1, 1, UnexcitedMetric.objective,
    Matrix.PosDef.diagonal fun _ => by norm_num, h1, h2, one_pos,
    fun v => by rw [hnorm, one_mul], fun v => by rw [hnorm, one_mul], fun x => ?_, ⟨mixedRun⟩⟩
  simp [UnexcitedMetric.objective, QuadraticGauge.left, QuadraticGauge.right, dot,
    Matrix.mulVec, dotProduct]
  ring

/-- The standing assumptions of the tilted-minimum construction can hold, with the choice of
`tilted_setup`: $\varphi(t)=(t-1)^2$, bounded below by $0$, $\varphi'(0)=-2$, $c_1=1/4$,
$c_2=1/2$, $\sigma=3/8$. -/
example : ∃ (φ : ℝ → ℝ) (L a c₁ c₂ σ : ℝ) (ψ : ℝ → ℝ) (M z : ℝ),
    ConvexOn ℝ univ φ ∧ (∀ t, 0 ≤ t → L ≤ φ t) ∧ HasDerivAt φ a 0 ∧ a < 0 ∧ 0 < c₁ ∧ c₁ < c₂ ∧
      c₂ < 1 ∧ σ = (c₁ + c₂) / 2 ∧ (∀ t, ψ t = φ t - σ * a * t) ∧ 0 < z ∧ z < M ∧
      (∀ t ∈ Icc 0 M, ψ z ≤ ψ t) ∧ ψ z < ψ 0 := by
  have hφ : ConvexOn ℝ univ (fun t : ℝ => (t - 1) ^ 2) := by
    have h := (Even.convexOn_pow (𝕜 := ℝ) (show Even 2 by decide)).comp_affineMap
      (AffineMap.id ℝ ℝ - AffineMap.const ℝ ℝ (1 : ℝ))
    simpa using h
  have hd : HasDerivAt (fun t : ℝ => (t - 1) ^ 2) (-2) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).sub_const 1).pow 2
    simpa using this
  obtain ⟨-, -, -, M, z, hz, hzM, hmin, hz0⟩ := tilted_setup (fun t : ℝ => (t - 1) ^ 2) hφ 0
    (fun t _ => sq_nonneg _) (-2) hd (by norm_num) (1 / 4) (1 / 2) (by norm_num) (by norm_num)
    (by norm_num) ((1 / 4 + 1 / 2) / 2) rfl (fun t => (t - 1) ^ 2 - (1 / 4 + 1 / 2) / 2 * (-2) * t)
    (fun t => rfl)
  exact ⟨_, 0, -2, 1 / 4, 1 / 2, _, _, M, z, hφ, fun t _ => sq_nonneg _, hd, by norm_num,
    by norm_num, by norm_num, by norm_num, rfl, fun t => rfl, hz, hzM, hmin, hz0⟩

/-- The hypotheses of the line-search existence statements (`finite_bad_ray_step`,
`abs_hinge_step`, `euclidean_residual_step`) can hold: $F(x)=x^2$ on $\R$ (with no residual
terms), $x=1$, $g=2$, $H=1$, bounded below by $0$, differentiable everywhere. -/
example : ∃ (F : Vec 1 → ℝ) (x g : Vec 1) (H : Mat 1), ConvexOn ℝ univ F ∧ Differentiable ℝ F ∧
    H.PosDef ∧ g ≠ 0 ∧ HasFDerivAt F (gradientFunctional g) x ∧
      (∀ t, 0 ≤ t → 0 ≤ F (x + bfgsStep H g t)) ∧
      {t | 0 < t ∧ ¬ DifferentiableAt ℝ F (x + bfgsStep H g t)}.Finite := by
  have hconv : ConvexOn ℝ univ (fun x : Vec 1 => (x 0) ^ 2) := by
    have h := (Even.convexOn_pow (𝕜 := ℝ) (show Even 2 by decide)).comp_linearMap
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)
    simpa using h
  have hdiff : Differentiable ℝ (fun x : Vec 1 => (x 0) ^ 2) := by fun_prop
  have hg : HasFDerivAt (fun x : Vec 1 => (x 0) ^ 2) (gradientFunctional ![2]) ![1] := by
    have h := ((hasDerivAt_pow 2 ((![1] : Vec 1) 0)).comp_hasFDerivAt (![1] : Vec 1)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).hasFDerivAt)
    convert h using 1
    ext v
    simp [gradientFunctional_apply, dot]
  refine ⟨fun x => (x 0) ^ 2, ![1], ![2], 1, hconv, hdiff, Matrix.PosDef.one, ?_, hg,
    fun t _ => sq_nonneg _, ?_⟩
  · intro h; have := congrFun h 0; simp at this
  · convert Set.finite_empty
    ext t
    simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and, not_not]
    exact fun _ => hdiff _

/-- The hypotheses of the inverse-route displays of the proof of Theorem `F:transform`
(`transform_euler`, `transform_theta_derivative`, `transform_secant_pairing`,
`transform_correction`) can hold together: $\Phi=\mathrm{id}$, $\gamma=|\cdot|$, $x_*=0$, `absRun`,
$\Phi^{-1}=\mathrm{id}$, $\Theta(t)=t$ (Lipschitz with $C=1$), $k=0$ and $L=F(x_1)>0$. -/
example : ∃ (Φ : ℝ → ℝ) (F : Vec 1 → ℝ) (R : AdmissibleBFGSRun 1 F) (L : ℝ) (Φinv Θ : ℝ → ℝ)
    (C : ℝ) (k : ℕ), (∀ x, F x = Φ (|(x - 0) 0|)) ∧ 0 < L ∧ L ≤ F (R.x (k + 1)) ∧
      (∀ t, 0 ≤ t → 0 ≤ Φinv t ∧ Φ (Φinv t) = t) ∧ (∀ t, Θ t = Φinv t * deriv Φ (Φinv t)) ∧
      0 ≤ C ∧ ∀ t ∈ Icc L (F (R.x 0)), ∀ u ∈ Icc L (F (R.x 0)), |Θ u - Θ t| ≤ C * |u - t| := by
  let R := BfgsCoverage.Article.Global.absRun (fun x : Vec 1 => |x 0|) fun _ => rfl
  have hpos : 0 < |R.x 1 0| := by
    have h1 : |R.x 2 0| < |R.x 1 0| := R.objective_strict_decrease 1
    exact lt_of_le_of_lt (abs_nonneg _) h1
  refine ⟨id, fun x => |x 0|, R, |R.x 1 0|, id, fun t => t, 1, 0, fun x => by simp, hpos,
    le_rfl, fun t ht => ⟨ht, rfl⟩, fun t => by simp, zero_le_one, fun t _ u _ => by simp⟩

/-- The runs on $u^2+|v|$ that start at the value $\delta$: `UnexcitedMetric.run` with $A=1$,
$v_0=\delta$, $\rho=1/4$, $c_1=1/4$, $c_2=1/2$. -/
def basinRun (δ : ℝ) (hδ : 0 < δ) : AdmissibleBFGSRun 2 UnexcitedMetric.objective :=
  UnexcitedMetric.run 1 δ (1 / 4) (1 / 4) (1 / 2) one_pos hδ (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- `basinRun δ` starts at the value $\delta=F(x_*)+\delta$ ($x_*=0$, $F(x_*)=0$). -/
theorem basinRun_start (δ : ℝ) (hδ : 0 < δ) :
    UnexcitedMetric.objective ((basinRun δ hδ).x 0) = UnexcitedMetric.objective 0 + δ := by
  change UnexcitedMetric.objective (UnexcitedMetric.point (UnexcitedMetric.sign 0)
    (UnexcitedMetric.radius (1 / 4) δ 0)) = _
  rw [UnexcitedMetric.point_value (UnexcitedMetric.sign_sq 0)
    (UnexcitedMetric.radius_pos (by norm_num) hδ 0).le]
  simp [UnexcitedMetric.radius, UnexcitedMetric.objective]

/-- The facts on $u^2+|v|$ used by the local non-vacuity examples: convexity, minimality and
uniqueness of $0$ (in the form of the local theorems), the smooth part $u^2$ and the gauge $|v|$. -/
theorem mixed_local_facts :
    ConvexOn ℝ univ UnexcitedMetric.objective ∧
      (∀ x, UnexcitedMetric.objective 0 ≤ UnexcitedMetric.objective x) ∧
      (∀ x, UnexcitedMetric.objective x = UnexcitedMetric.objective 0 → x = 0) ∧
      ConvexOn ℝ univ (fun x : Vec 2 => (x 0) ^ 2) ∧
      CenteredSmoothSublinear.LocallyC11On univ (fun x : Vec 2 => (x 0) ^ 2) ∧
      ConvexOn ℝ univ (fun x : Vec 2 => |x 1|) ∧
      Homogeneous.PositiveDegreeOne (fun x : Vec 2 => |x 1|) ∧
      (∀ x, UnexcitedMetric.objective x = (x 0) ^ 2 + |(x - 0) 1|) ∧
      ∀ b : ℝ, IsCompact {x | UnexcitedMetric.objective x ≤ b} := by
  obtain ⟨hconv, hmin, huniq', hK, hψ, hψ11, hγ, hγh, hrep⟩ :=
    BfgsCoverage.Article.Global.mixed_hypotheses UnexcitedMetric.objective (fun _ => rfl)
  refine ⟨hconv, hmin, fun x hx => huniq' x fun z => ?_, hψ, hψ11, hγ, hγh, hrep, hK⟩
  rw [hx]
  exact hmin z

/-- Theorem `F:centered`, last sentence (`centered_local`), is not vacuous: $u^2+|v|$ with
$\psi(u,v)=u^2$, $\gamma(u,v)=|v|$, $U=\R^2$ satisfies its hypotheses, and `basinRun` starts in the
basin $F(x_0)\le F(x_*)+\varepsilon$ it provides. -/
example : ∃ R : AdmissibleBFGSRun 2 UnexcitedMetric.objective, Tendsto R.x atTop (𝓝 0) := by
  obtain ⟨hconv, hmin, huniq, hψ, hψ11, hγ, hγh, hrep, -⟩ := mixed_local_facts
  obtain ⟨ε, hε, h⟩ := centered_local UnexcitedMetric.objective (fun x : Vec 2 => (x 0) ^ 2)
    (fun x : Vec 2 => |x 1|) hconv 0 hmin huniq univ isOpen_univ convex_univ (mem_univ _) hψ hψ11
    hγ hγh (fun x _ => hrep x)
  exact ⟨basinRun ε hε, (h _ (basinRun_start ε hε).le).2.2⟩

/-- `maxAffine_local_basin` is not vacuous: $u^2+|v|$ is $\psi+p$ with $\psi(u,v)=u^2$ and
$p=\max\{v,-v\}$, and `basinRun` starts in its basin. -/
example : ∃ R : AdmissibleBFGSRun 2 UnexcitedMetric.objective, Tendsto R.x atTop (𝓝 0) := by
  obtain ⟨-, hmin, huniq, hψ, hψ11, -, -, -, -⟩ := mixed_local_facts
  have hp : ∀ x : Vec 2, IsGreatest (Set.range fun i =>
      dot ((![![0, 1], ![0, -1]] : Fin 2 → Vec 2) i) x + (0 : Fin 2 → ℝ) i) (|x 1|) := by
    intro x
    have h0 : dot ![0, 1] x = x 1 := by simp [dot, Fin.sum_univ_two]
    have h1 : dot ![0, -1] x = -x 1 := by simp [dot, Fin.sum_univ_two]
    refine ⟨?_, ?_⟩
    · rcases abs_choice (x 1) with h | h
      · exact ⟨0, by simp [h0, h]⟩
      · exact ⟨1, by simp [h1, h]⟩
    · rintro _ ⟨i, rfl⟩
      fin_cases i
      · simp [h0, le_abs_self]
      · simp [h1, neg_le_abs]
  obtain ⟨δ, hδ, h⟩ := maxAffine_local_basin ![![0, 1], ![0, -1]] 0 ⟨0⟩ (fun x => |x 1|) hp
    (fun x : Vec 2 => (x 0) ^ 2) hψ hψ11 UnexcitedMetric.objective (fun _ => rfl) 0 hmin huniq
  exact ⟨basinRun δ hδ, (h _ (basinRun_start δ hδ).le).2⟩

/-- `kink_sums_basin` is not vacuous: $u^2+|v|$ is $\psi$ plus one absolute-value term
$|e_2^Tx-0|$ and no hinge term, and `basinRun` starts in its basin. -/
example : ∃ R : AdmissibleBFGSRun 2 UnexcitedMetric.objective, Tendsto R.x atTop (𝓝 0) := by
  obtain ⟨hconv, hmin, huniq, -, hψ11, -, -, -, -⟩ := mixed_local_facts
  obtain ⟨ε, hε, h⟩ := kink_sums_basin (ι := Fin 1) (κ := Fin 0) UnexcitedMetric.objective
    (fun x : Vec 2 => (x 0) ^ 2) hconv (fun _ => ![0, 1]) (fun _ => 0) (fun j => j.elim0)
    (fun j => j.elim0) univ isOpen_univ hψ11 0 (mem_univ _)
    (fun x _ => by simp [UnexcitedMetric.objective, dot, Fin.sum_univ_two]) hmin huniq
  exact ⟨basinRun ε hε, (h _ (basinRun_start ε hε).le).2.2⟩

/-- `residual_sums_basin` is not vacuous: $u^2+|v|$ is the loss $u^2$ plus one absolute-value
term, with no hinge and no Euclidean residual term, and `basinRun` starts in its basin. -/
example : ∃ R : AdmissibleBFGSRun 2 UnexcitedMetric.objective, Tendsto R.x atTop (𝓝 0) := by
  obtain ⟨-, hmin, huniq, hψ, hψ11, -, -, -, -⟩ := mixed_local_facts
  obtain ⟨U, -, -, ε, hε, h⟩ := residual_sums_basin (ι := Fin 1) (κ := Fin 0) (ν := Fin 0)
    (m := fun _ => 0) (fun x : Vec 2 => (x 0) ^ 2) hψ hψ11 (fun _ => ![0, 1]) (fun _ => 0)
    (fun j => j.elim0) (fun j => j.elim0) (fun l => l.elim0) (fun l => l.elim0)
    UnexcitedMetric.objective (fun x => by simp [UnexcitedMetric.objective, dot, Fin.sum_univ_two])
    0 hmin huniq
  exact ⟨basinRun ε hε, (h _ (basinRun_start ε hε).le).2.2⟩

/-- `powered_gauges_covered` is not vacuous: $u^2+|v|$ is $\psi(x)+\gamma(A(x-x_*))^p$ with
$\psi(u,v)=u^2$, $\gamma=|\cdot|$ on $\R$, $A(u,v)=v$, $p=1$, $U=\R^2$, and its hypotheses hold for
`mixedRun`. -/
example : Tendsto mixedRun.x atTop (𝓝 0) := by
  obtain ⟨-, hmin, huniq, -, hψ11, -, -, -, hK⟩ := mixed_local_facts
  obtain ⟨h1, h2, -⟩ := abs_facts
  have h := powered_gauges_covered (ι := Unit) (m := fun _ => 1) (ψ := fun x : Vec 2 => (x 0) ^ 2)
    mixedRun (fun _ x => |x 0|) (fun _ => h1) (fun _ => h2) (fun _ _ => abs_nonneg _)
    (fun _ => LinearMap.pi fun _ : Fin 1 => LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1)
    (fun _ => 1) (fun _ => le_rfl) 0 hmin univ isOpen_univ hψ11 (hK _) (subset_univ _)
    (fun x _ => by simp [UnexcitedMetric.objective])
  exact h.2.2 huniq

/-- Admissible runs on $x^4+|x|$ exist (`AdmissibleRunExistence.exists_admissible_run`): the
function is convex and bounded below, differentiable off $0$ (so at all but one point of every
line), and no point of differentiability has gradient zero (a zero gradient would make the point
the minimizer $0$, where $F$ touches $\ell(x)=x$ from above, forcing the gradient $1$). -/
theorem quarticAbs_run_exists :
    Nonempty (AdmissibleBFGSRun 1 (fun x : Vec 1 => (x 0) ^ 4 + |x 0|)) := by
  set F : Vec 1 → ℝ := fun x => (x 0) ^ 4 + |x 0| with hFdef
  have hψc : ConvexOn ℝ univ (fun x : Vec 1 => (x 0) ^ 4) := by
    have h := (Even.convexOn_pow (𝕜 := ℝ) (show Even 4 by decide)).comp_linearMap
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)
    simpa using h
  have hconv : ConvexOn ℝ univ F := hψc.add BfgsCoverage.Article.Global.abs_coord_convex
  have hnn : ∀ x, 0 ≤ F x := fun x => by simp only [hFdef]; positivity
  have hproj : ∀ y : Vec 1, HasFDerivAt (fun x : Vec 1 => x 0)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) y :=
    fun y => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).hasFDerivAt
  have hdiff : ∀ y : Vec 1, y 0 ≠ 0 → DifferentiableAt ℝ F y := by
    intro y hy
    have h0 := (hproj y).differentiableAt
    have habs := (differentiableAt_abs hy).comp y h0
    exact (h0.pow 4).add habs
  have hline : ∀ x p : Vec 1, DifferentiableAt ℝ F x → p ≠ 0 →
      {t : ℝ | ¬ DifferentiableAt ℝ F (x + t • p)}.Countable := by
    intro x p _ hp
    have hp0 : p 0 ≠ 0 := fun h => hp (by ext i; rw [Subsingleton.elim i 0]; simpa using h)
    apply Set.Subsingleton.countable
    intro s hs t ht
    have hs0 : x 0 + s * p 0 = 0 := by
      by_contra hne
      apply hs
      apply hdiff
      simpa using hne
    have ht0 : x 0 + t * p 0 = 0 := by
      by_contra hne
      apply ht
      apply hdiff
      simpa using hne
    have hst : (s - t) * p 0 = 0 := by linarith
    rcases mul_eq_zero.mp hst with h | h
    · linarith
    · exact absurd h hp0
  have hstat : ∀ y g, HasFDerivAt F (gradientFunctional g) y → g ≠ 0 := by
    rintro y g h rfl
    have hmin : ∀ z, F y ≤ F z := by
      intro z
      have hs := convex_supporting_inequality hconv h z
      simp [dot] at hs
      linarith
    have hy0 : y 0 = 0 := by
      have h1 := hmin 0
      simp only [hFdef] at h1
      simp at h1
      have := abs_nonneg (y 0)
      have := pow_nonneg (sq_nonneg (y 0)) 2
      have h4 : (y 0) ^ 4 = ((y 0) ^ 2) ^ 2 := by ring
      exact abs_eq_zero.mp (by linarith)
    have hy : y = 0 := by
      ext i
      rw [Subsingleton.elim i 0]
      exact hy0
    subst hy
    have hloc : IsLocalMin (fun z : Vec 1 => F z - z 0) 0 := by
      refine Filter.Eventually.of_forall fun z => ?_
      simp only [hFdef]
      simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        abs_zero, add_zero, sub_zero]
      have := le_abs_self (z 0)
      have := pow_nonneg (sq_nonneg (z 0)) 2
      have h4 : (z 0) ^ 4 = ((z 0) ^ 2) ^ 2 := by ring
      linarith
    have h0 := hloc.hasFDerivAt_eq_zero (h.sub (hproj 0))
    have he := congrArg (fun L : Vec 1 →L[ℝ] ℝ => L ![1]) h0
    simp [dot] at he
  have hx₀ : DifferentiableAt ℝ F ![1] := hdiff _ (by simp)
  obtain ⟨R, -⟩ := AdmissibleRunExistence.exists_admissible_run hconv
    ⟨0, by rintro _ ⟨x, rfl⟩; exact hnn x⟩ hline hstat (hasFDerivAt_coordinateGradient hx₀)
    Matrix.PosDef.one (c₁ := 1 / 4) (c₂ := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨R⟩

/-- `centered_no_global_lipschitz` is not vacuous: admissible runs on $x^4+|x|$ exist
(`quarticAbs_run_exists`), and each converges to $0$. -/
example : ∃ R : AdmissibleBFGSRun 1 (fun x : Vec 1 => (x 0) ^ 4 + |x 0|),
    Tendsto R.x atTop (𝓝 0) := by
  obtain ⟨R⟩ := quarticAbs_run_exists
  exact ⟨R, ((centered_no_global_lipschitz _ fun _ => rfl).2.1 R).2⟩

/-- The hypotheses of `maxAffine_inactive` can hold with an inactive piece: $p=\max\{x,-x,x-1\}$
on $\R$ ($=|x|$), $\psi=0$, $F=p$, $x_*=0$, $I_*=\{0,1\}$, $i_0=0$, the inactive piece $j=2$ with
$\delta_j=1$. -/
example : ∃ (a : Fin 3 → Vec 1) (b : Fin 3 → ℝ) (p ψ F : Vec 1 → ℝ) (xstar : Vec 1)
    (I : Finset (Fin 3)) (i₀ j : Fin 3) (δ : ℝ),
    (∀ x, IsGreatest (Set.range fun i => dot (a i) x + b i) (p x)) ∧ ConvexOn ℝ univ ψ ∧
      CenteredSmoothSublinear.LocallyC11On univ ψ ∧ (∀ x, F x = ψ x + p x) ∧
      (∀ x, F xstar ≤ F x) ∧ (∀ x, F x = F xstar → x = xstar) ∧
      (∀ i, i ∈ I ↔ dot (a i) xstar + b i = p xstar) ∧ i₀ ∈ I ∧ j ∉ I ∧
      δ = p xstar - (dot (a j) xstar + b j) ∧ 0 < δ := by
  have hd : ∀ (c : ℝ) (x : Vec 1), dot ![c] x = c * x 0 := fun c x => by simp [dot]
  have hgr : ∀ x : Vec 1, IsGreatest (Set.range fun i =>
      dot ((![![1], ![-1], ![1]] : Fin 3 → Vec 1) i) x + (![0, 0, -1] : Fin 3 → ℝ) i) (|x 0|) := by
    intro x
    refine ⟨?_, ?_⟩
    · rcases abs_choice (x 0) with h | h
      · exact ⟨0, by simp [hd, h]⟩
      · exact ⟨1, by simp [hd, h]⟩
    · rintro _ ⟨i, rfl⟩
      fin_cases i
      · simp [hd, le_abs_self]
      · simp [hd, neg_le_abs]
      · simp [hd, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
        linarith [le_abs_self (x 0)]
  refine ⟨![![1], ![-1], ![1]], ![0, 0, -1], fun x => |x 0|, fun _ => 0, fun x => |x 0|, 0,
    {0, 1}, 0, 2, 1, hgr, convexOn_const 0 convex_univ, ?_, fun x => by simp, fun x => by simp,
    fun x hx => ?_, fun i => ?_, by decide, by decide, ?_, one_pos⟩
  · exact ConvexCellRadial.contDiffOn_two_locallyC11 isOpen_univ contDiffOn_const
  · ext i
    rw [Subsingleton.elim i 0]
    simpa using hx
  · fin_cases i <;> simp [hd, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  · simp [hd, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

end BfgsCoverage.Companion.Ch06F
