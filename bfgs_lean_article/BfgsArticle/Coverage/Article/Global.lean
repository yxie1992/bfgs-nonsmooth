import BfgsVerification.InwardRadial
import BfgsVerification.RadialReverse
import BfgsVerification.TransportedCertificateVariants
import BfgsVerification.CenteredSmoothSublinear
import BfgsVerification.HomogeneousConsequences
import BfgsVerification.RadialSingularCurvature
import BfgsVerification.RadialHessian
import BfgsVerification.QuadraticCellRadial
import BfgsVerification.ConvexSubdifferential
import BfgsVerification.PlanarQuadraticSeparation
import MixedBenchmark
import ArticleGeometry

/-!
# Lean coverage: `paper/sections/global.tex`

Section `art:global` ("Global convergence: homogeneous and mixed geometry"): the radial and
inward conditions, Theorem `art:radial-equivalence`, Corollary `art:radial-convergence`,
Theorem `art:centered`, Corollary `art:mixed-benchmark`, Theorem `art:homogeneous`, Corollary
`art:homogeneous-examples`, their proofs, and the claims of the surrounding text. Register:
`editorial/lean_coverage/register/A_global.json`.

## Standing assumptions

The setting of lines 19-20 is written out in every theorem that uses it:

* `hF : ConvexOn ℝ univ F` with `F : Vec n → ℝ` is "$F$ finite and convex";
* `xstar` with `hmin : ∀ x, F xstar ≤ F x` is the fixed minimizer $x_*$, and $F_*$ is `F xstar`;
* `b` with `hb : F xstar < b`, and `K` with `hK_def : K = {x | F x ≤ b}` and
  `hK : IsCompact K`, is the compact sublevel $K=\{F\le b\}$, $b>F_*$.

A gradient $g=\nabla F(x)$ at a differentiable point is `HasFDerivAt F (gradientFunctional g) x`
(`gradientFunctional g v = dot g v`), and $r_x$ is `x - xstar`. An admissible run (Definition
`art:admissible`) is `AdmissibleBFGSRun n F`; its fields include $x_0$, $H_0\succ0$ and the
fixed constants $0<c_1<c_2<1$, so "every admissible run" is `∀ R : AdmissibleBFGSRun n F`.

The proof of Theorem `art:radial-equivalence` adds the constants `Λ R` (positive Euclidean
bounds on all subgradients at points of $K$ and on $\|x-x_*\|$ over $K$), the inward condition
`_hIR`, a band `η` with its constants `M θ` and their inward bounds `hMθ`, and a pair of
differentiable points `x z ∈ K` with gradients `g h` and $F_*+\eta\le F(z)\le F(x)$; $T$, $N$
and $D_F$ are variables with their defining equations. The proof of Theorem `art:centered` adds
an admissible run `R` whose initial sublevel is compact and contained in `U`, `K` with
`hK_def : K = {x | F x ≤ F (R.x 0)}`, and a uniform Euclidean Lipschitz constant `L` for
$\nabla\psi$ on $K$. A hypothesis whose name starts with `_` is a standing assumption that the
Lean proof does not use.

## Notation

* `Vec n` carries the sup norm; Euclidean norms are explicit: $\|v\|$ is `‖euclideanVector v‖`
  ($=\sqrt{\sum_iv_i^2}$, `norm_euclideanVector`), and $\operatorname{dist}(x,\arg\min F)$ is
  the library's `euclideanSolutionDistance F x`, literally
  `Metric.infDist (euclideanVector x) (euclideanVector '' argmin F)` with
  `argmin F = {x | ∀ y, F x ≤ F y}`;
* `coordinateGradient ψ x` is $\nabla\psi(x)$;
* "locally $C^{1,1}$ on $U$" is `CenteredSmoothSublinear.LocallyC11On U ψ` ($\psi$
  differentiable on $U$ with locally Lipschitz derivative); "positively homogeneous of degree
  one" is `Homogeneous.PositiveDegreeOne γ` ($\gamma(tx)=t\gamma(x)$ for $t\ge0$); "coercive"
  is `Tendsto F (cocompact (Vec n)) atTop`;
* a maximum $\max_iv_i$ is `IsGreatest (Set.range v)`; a norm on $\R^n$ is a `Seminorm` that
  vanishes only at zero.

## Items

| Item | Lines | Lean |
|---|---|---|
| `disp/001` | 22-27 | `secant_notation` (notation) |
| `disp/002` (`art:radial-condition`) | 29-35 | `RadialSecantCondition` |
| `disp/003` (`art:inward-condition`) | 38-45 | `InwardModelCondition` |
| `theorem/art:radial-equivalence` | 54-57 | `radial_equivalence` |
| `disp/004` | 63-65 | `supporting_plane_error` |
| `disp/005` | 73-75 | `inward_probe_at_z` |
| `disp/006` | 77-79 | `inward_probe_at_x` |
| `disp/007` (`art:inward-to-radial`) | 88-90 | `inward_to_radial` |
| `corollary/art:radial-convergence` | 98-102 | `radial_convergence` |
| `theorem/art:centered` (with `disp/008`) | 130-142 | `centered` |
| `disp/009` | 151-155 | `smooth_inward_remainder` |
| `corollary/art:mixed-benchmark` (with `disp/010`) | 175-181 | `mixed_benchmark` |
| `theorem/art:homogeneous` (with `disp/011`) | 200-209 | `homogeneous` |
| `disp/012` | 214-217 | `homogeneous_sphere_bound` |
| `corollary/art:homogeneous-examples` (with `disp/013`) | 224-233 | `homogeneous_examples_*` |

The theorem item `art:centered` also lists `centered_summands_not_minimized` (its last sentence);
the corollary `art:homogeneous-examples` is `homogeneous_examples_norm`,
`homogeneous_examples_gauge` and `homogeneous_examples_maxLinear`.

Claims of the text (prose items): `gradient_jump_large_correction` (`prose/003`),
`inward_point_mem` (`prose/010`), `inward_point_fraction` (`prose/011`),
`mixed_inward_condition` (`prose/013`), `radial_implies_inward` (`prose/014`),
`inward_remainder_second_derivative` (`prose/017`), `ae_curvature_misses_jump` (`prose/018`),
`nonradial_example_condition_fails` (`prose/019`), `homogeneous_sublinear` (`prose/020`),
`homogeneous_inward_remainder_zero` (`prose/021`), `centered_summands_not_minimized`
(`prose/024`), `initial_sublevel_traps` (`prose/025`), `centered_global` (`prose/026`),
`centered_weak_hypotheses` (`prose/027`), `homogeneous_inward_condition` (`prose/030`),
`coercive_homogeneous_positive` and `iterates_of_values` (`prose/031`),
`homogeneous_no_smoothness_or_pieces` (`prose/032`), `l1_norm_case` and `linf_norm_case`
(`prose/033`), `l1_nonsmooth` and `linf_nonsmooth` (`prose/034`),
`linf_tie_example` (`prose/035`), `euclidean_norm_case` (`prose/037`), `asymmetric_example`
(`prose/039`), `sublevels_compact_of_coercive` (`prose/040`), `homogeneous_value_dichotomy`
(`prose/041`).

The main theorems are proved along the paper's proofs, from the display theorems and the
undisplayed steps stated here (`exists_subgradient_and_radius_bounds`, `lipschitz_on_K`,
`curvature_eq_errors`, `radial_band_certificate`, `initial_value_gt`,
`uniform_lipschitz_gradient`, `homogeneous_part_at_differentiable`,
`centered_inward_condition`, `mixed_hypotheses`, `sphere_minimum`, `coercive_of_positive`,
`maxLinear_convex_homogeneous`; `homogeneous_via_radial` is the alternative proof in the last
sentence of the proof of Theorem `art:homogeneous`). Theorem `art:certificate` is the
library's `AdmissibleBFGSRun.transported_certificate_convergence_on_sublevel`.

## Non-vacuity

The examples at the end show that the standing assumptions of the theorems and of the displays
of their proofs can hold. Statements about every admissible run are shown non-vacuous by
explicit runs: the library's `UnexcitedMetric.run` on the benchmark $u^2+|v|$ (for
`radial_convergence`, `centered`, `centered_global` and `mixed_benchmark`), `absRun` on $|x|$
over $\R$ (for the coercive homogeneous statements `homogeneous`, `homogeneous_via_radial`,
`homogeneous_examples_*`, `l1_norm_case`, `linf_norm_case`, `euclidean_norm_case` and
`homogeneous_value_dichotomy`), and `asymRun` on $\max(x,-2x)$ (inside `asymmetric_example`).
The last two are built by `oneDimRun`, which reduces Definition `art:admissible` in dimension
one to scalar conditions (the inverse-BFGS update is then the secant ratio $s_k/y_k$). One
exception: no admissible run on the objective of Theorem `art:nonradial-example` is constructed
here, so the run part of `nonradial_example_condition_fails` (`prose/019`), which restates the
conclusion of that theorem, is not shown non-vacuous in this module.
-/

noncomputable section
open scoped Topology
open Set Filter Matrix BfgsVerification

namespace BfgsCoverage.Article.Global

/-! ### Euclidean norms -/

/-- `‖euclideanVector v‖` is the Euclidean norm $\|v\|$: its square is `sqNorm v`. -/
theorem norm_euclideanVector_sq {n : ℕ} (v : Vec n) : ‖euclideanVector v‖ ^ 2 = sqNorm v := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  simp [sqNorm, euclideanVector]

theorem norm_euclideanVector {n : ℕ} (v : Vec n) : ‖euclideanVector v‖ = Real.sqrt (sqNorm v) := by
  rw [← norm_euclideanVector_sq, Real.sqrt_sq (norm_nonneg _)]

theorem sqNorm_le_of_norm_le {n : ℕ} {v : Vec n} {A : ℝ} (h : ‖euclideanVector v‖ ≤ A) :
    sqNorm v ≤ A ^ 2 := by
  rw [← norm_euclideanVector_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

theorem norm_le_of_sqNorm_le {n : ℕ} {v : Vec n} {A : ℝ} (hA : 0 ≤ A) (h : sqNorm v ≤ A ^ 2) :
    ‖euclideanVector v‖ ≤ A := by
  rw [← norm_euclideanVector_sq] at h
  exact (sq_le_sq₀ (norm_nonneg _) hA).mp h

theorem norm_le_norm_euclideanVector {n : ℕ} (v : Vec n) : ‖v‖ ≤ ‖euclideanVector v‖ := by
  rw [norm_euclideanVector]
  exact Real.le_sqrt_of_sq_le (CenteredSmoothSublinear.pi_norm_sq_le_sqNorm v)

theorem norm_euclideanVector_smul {n : ℕ} (c : ℝ) (v : Vec n) :
    ‖euclideanVector (c • v)‖ = |c| * ‖euclideanVector v‖ := by
  rw [norm_euclideanVector, norm_euclideanVector, CenteredSmoothSublinear.sqNorm_smul,
    Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

theorem norm_euclideanVector_sub_comm {n : ℕ} (x z : Vec n) :
    ‖euclideanVector (x - z)‖ = ‖euclideanVector (z - x)‖ := by
  rw [norm_euclideanVector, norm_euclideanVector]
  congr 1
  simp only [sqNorm, Pi.sub_apply]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- Euclidean Cauchy--Schwarz, $|v^Tw|\le\|v\|\,\|w\|$. -/
theorem abs_dot_le_norm_mul_norm {n : ℕ} (v w : Vec n) :
    |dot v w| ≤ ‖euclideanVector v‖ * ‖euclideanVector w‖ := by
  have h := dot_sq_le_sqNorm_mul_sqNorm v w
  rw [← norm_euclideanVector_sq, ← norm_euclideanVector_sq, ← mul_pow, ← sq_abs] at h
  exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp h

theorem sublevel_convex {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F) (c : ℝ) :
    Convex ℝ {x | F x ≤ c} := by
  simpa using hF.convex_le c

/-! ### The setting, the radial and the inward conditions (lines 3-52) -/

/-- Item `A/global/prose/003` (`paper/sections/global.tex:11-12`): "A gradient jump can make
the positive correction in \eqref{art:energy-identity} large." The correction of an accepted
pair $(x,z)=(x_k,x_{k+1})$ is $R_k=N^2/T$ (energy.tex:78), and accepted pairs are eligible
(energy.tex:245). For the strongly convex $F(t)=(t+2)^2/2+|t|$ on $\R$, whose derivative jumps
from $1$ to $3$ at $t=0$ and whose minimizer is $x_*=-1$, there is a positive band on which
$N^2/T$ exceeds every constant $C$, over differentiable pairs $z<0<x$ across the jump with
$F_*+\eta\le F(z)\le F(x)\le3$ and $T>0$ that are eligible for $c_1=1/4$, $c_2=1/2$ (the
library's crossing pairs `ScalarCounterexamples.crossingX`/`crossingZ`, with
`crossing_eligible`). -/
theorem gradient_jump_large_correction (f : ℝ → ℝ) (hf : ∀ t, f t = (t + 2) ^ 2 / 2 + |t|)
    (F : Vec 1 → ℝ) (hF : ∀ x, F x = f (x 0)) (xstar : Vec 1) (hxstar : xstar = fun _ => -1) :
    (∀ x, F xstar ≤ F x) ∧
      (∀ t : ℝ, t < 0 → HasDerivAt f (t + 1) t) ∧ (∀ t : ℝ, 0 < t → HasDerivAt f (t + 3) t) ∧
      ∃ η : ℝ, 0 < η ∧ ∀ C : ℝ, ∃ x z g h : Vec 1, F x ≤ 3 ∧ F z ≤ 3 ∧
        HasFDerivAt F (gradientFunctional g) x ∧ HasFDerivAt F (gradientFunctional h) z ∧
        TransportedCertificate.EligiblePair F (1 / 4) (1 / 2) x z g h ∧ z 0 < 0 ∧ 0 < x 0 ∧
        F xstar + η ≤ F z ∧ F z ≤ F x ∧ 0 < dot (h - g) (z - x) ∧
        C * dot (h - g) (z - x) < (dot (h - g) (z - xstar)) ^ 2 := by
  obtain rfl : f = ScalarCounterexamples.shiftedAbs := funext hf
  obtain rfl : F = ScalarCounterexamples.shiftedObjective := funext hF
  obtain rfl : xstar = OneDimensional.embed (-1) := by rw [hxstar]; ext i; simp
  refine ⟨ScalarCounterexamples.shiftedObjective_minimum,
    fun t ht => ScalarCounterexamples.shiftedAbs_hasDerivAt_neg ht,
    fun t ht => ScalarCounterexamples.shiftedAbs_hasDerivAt_pos ht, 1 / 4, by norm_num,
    fun C => ?_⟩
  have hlim : Tendsto (fun k => C * (3 * ScalarCounterexamples.crossingScale k +
      9 / 4 * (ScalarCounterexamples.crossingScale k) ^ 2)) atTop (𝓝 0) := by
    simpa using ((ScalarCounterexamples.crossingScale_tendsto.const_mul 3).add
      ((ScalarCounterexamples.crossingScale_tendsto.pow 2).const_mul (9 / 4 : ℝ))).const_mul C
  obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds (one_pos : (0 : ℝ) < 1))).exists
  have hε : 0 < ScalarCounterexamples.crossingScale k := ScalarCounterexamples.crossingScale_pos k
  have hs : ScalarCounterexamples.crossingScale k ≤ 1 / 8 :=
    ScalarCounterexamples.crossingScale_le k
  set ε := ScalarCounterexamples.crossingScale k with hε_def
  have hb := ScalarCounterexamples.crossing_band hε hs
  have hv := ScalarCounterexamples.crossing_values hε
  have hgr := ScalarCounterexamples.crossing_gradients hε
  have hN := RadialSingularCurvature.crossing_radial_numerator ε
  have hT := RadialSingularCurvature.crossing_radial_curvature ε
  refine ⟨_, _, _, _, hb.1.1, hb.2.1, hgr.1, hgr.2, ScalarCounterexamples.crossing_eligible hε,
    ?_, ?_, hb.2.2, ?_, ?_, ?_⟩
  · simp only [ScalarCounterexamples.crossingZ, OneDimensional.embed_apply]
    linarith
  · simpa only [ScalarCounterexamples.crossingX, OneDimensional.embed_apply] using hε
  · rw [hv.1, hv.2]
    nlinarith [sq_nonneg ε]
  · change 0 < RadialCertificate.secantCurvature _ _ _ _
    rw [hT]
    positivity
  · change C * RadialCertificate.secantCurvature _ _ _ _ <
      (RadialCertificate.radialNumerator _ _ _ _) ^ 2
    rw [hT, hN]
    have he2 : ε ^ 2 ≤ ε / 8 := by nlinarith
    have hn : (1 - ε / 2 - (3 + ε)) * (1 - ε / 2) ≤ -1 := by nlinarith
    have hsq : (1 : ℝ) ≤ ((1 - ε / 2 - (3 + ε)) * (1 - ε / 2)) ^ 2 := by nlinarith
    linarith

/-- Item `A/global/disp/001` (`paper/sections/global.tex:22-27`): the notation
$r_x=x-x_*$, $g=\nabla F(x)$, $h=\nabla F(z)$, $T=(h-g)^T(z-x)$, $N=(h-g)^Tr_z$, for
differentiable $x,z\in K$. The coverage theorems write $r_x$ as `x - xstar` and $T$, $N$ as
the dot products themselves (or as variables with these defining equations); a gradient
$g=\nabla F(x)$ is `HasFDerivAt F (gradientFunctional g) x`, where
`gradientFunctional g v = dot g v`. The library's `secantCurvature x z g h` is $T$ and
`radialNumerator xstar z g h` is $N$. -/
theorem secant_notation {n : ℕ} (xstar x z g h : Vec n) :
    RadialCertificate.secantCurvature x z g h = dot (h - g) (z - x) ∧
      RadialCertificate.radialNumerator xstar z g h = dot (h - g) (z - xstar) ∧
      (∀ v, gradientFunctional g v = dot g v) :=
  ⟨rfl, rfl, gradientFunctional_apply g⟩

/-- Item `A/global/disp/002`, equation `art:radial-condition`
(`paper/sections/global.tex:29-35`): the radial secant condition on positive bands.
For every $\eta>0$ there is $C_\eta\ge0$ such that $N^2\le C_\eta T$ whenever
$F_*+\eta\le F(z)\le F(x)$ and $T>0$, for all differentiable $x,z\in K$ (eligible for the
line search or not, lines 36-37), with $g=\nabla F(x)$, $h=\nabla F(z)$, $T=(h-g)^T(z-x)$,
$N=(h-g)^Tr_z$, $r_z=z-x_*$, $F_*=F(x_*)$ (display `A/global/disp/001`). -/
def RadialSecantCondition {n : ℕ} (F : Vec n → ℝ) (xstar : Vec n) (K : Set (Vec n)) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧
    ∀ x z g h : Vec n, x ∈ K → z ∈ K →
      HasFDerivAt F (gradientFunctional g) x → HasFDerivAt F (gradientFunctional h) z →
      F xstar + η ≤ F z → F z ≤ F x → 0 < dot (h - g) (z - x) →
      (dot (h - g) (z - xstar)) ^ 2 ≤ C * dot (h - g) (z - x)

/-- Item `A/global/disp/003`, equation `art:inward-condition`
(`paper/sections/global.tex:38-45`): the inward model condition. For every $\eta>0$ there
are $M_\eta\ge0$, $\theta_\eta\in(0,1/2]$ such that
$0\le F(x-\tau r_x)-F(x)+\tau\nabla F(x)^Tr_x\le\frac{M_\eta}{2}\tau^2$ for
$0\le\tau\le\theta_\eta$, "at every differentiable $x\in K$ with $F(x)\ge F_*+\eta$"
(line 46). Differentiability is asked only at $x$, not at the inward point $x-\tau r_x$
(line 47); the constants depend on the band (lines 49-50). -/
def InwardModelCondition {n : ℕ} (F : Vec n → ℝ) (xstar : Vec n) (K : Set (Vec n)) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ M θ : ℝ, 0 ≤ M ∧ 0 < θ ∧ θ ≤ 1 / 2 ∧
    ∀ x g : Vec n, x ∈ K → HasFDerivAt F (gradientFunctional g) x → F xstar + η ≤ F x →
      ∀ τ : ℝ, 0 ≤ τ → τ ≤ θ →
        0 ≤ F (x - τ • (x - xstar)) - F x + τ * dot g (x - xstar) ∧
          F (x - τ • (x - xstar)) - F x + τ * dot g (x - xstar) ≤ M / 2 * τ ^ 2

/-- The radial secant condition is the library's `HasRadialSecantBounds` (which does not
ask $C_\eta\ge0$; a constant can always be replaced by $\max(C_\eta,0)$). -/
theorem radialSecantCondition_iff {n : ℕ} (F : Vec n → ℝ) (xstar : Vec n) (K : Set (Vec n)) :
    RadialSecantCondition F xstar K ↔ RadialCertificate.HasRadialSecantBounds F K xstar := by
  constructor
  · intro h η hη
    obtain ⟨C, -, hC⟩ := h η hη
    exact ⟨C, fun x z g h hx hz hb ho hg hh ht => hC x z g h hx hz hg hh hb ho ht⟩
  · intro h η hη
    obtain ⟨C, hC⟩ := h η hη
    refine ⟨max C 0, le_max_right _ _, fun x z g h hx hz hg hh hb ho ht => ?_⟩
    exact (hC x z g h hx hz hb ho hg hh ht).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) ht.le)

/-- The inward model condition is the library's `HasInwardTaylorBounds` (which does not ask
$M_\eta\ge0$; a constant can always be replaced by $\max(M_\eta,0)$). -/
theorem inwardModelCondition_iff {n : ℕ} (F : Vec n → ℝ) (xstar : Vec n) (K : Set (Vec n)) :
    InwardModelCondition F xstar K ↔ RadialCertificate.HasInwardTaylorBounds F K xstar := by
  constructor
  · intro h η hη
    obtain ⟨M, θ, -, hθ, hθ', hM⟩ := h η hη
    refine ⟨M, θ, hθ, hθ', fun x g hx hb hg τ h0 h1 => ?_⟩
    rw [RadialCertificate.inward_error_eq]
    exact hM x g hx hg hb τ h0 h1
  · intro h η hη
    obtain ⟨M, θ, hθ, hθ', hM⟩ := h η hη
    refine ⟨max M 0, θ, le_max_right _ _, hθ, hθ', fun x g hx hg hb τ h0 h1 => ?_⟩
    have h' := hM x g hx hb hg τ h0 h1
    rw [RadialCertificate.inward_error_eq] at h'
    exact ⟨h'.1, h'.2.trans (by
      have := mul_le_mul_of_nonneg_right (le_max_left M 0) (sq_nonneg τ)
      linarith)⟩

/-- Item `A/global/prose/010` (`paper/sections/global.tex:47`): "It remains in $K$ by
convexity." In the setting of the section, for $x\in K$ and $0\le\tau\le1$ the inward point
$x-\tau r_x=(1-\tau)x+\tau x_*$ lies in $K$. -/
theorem inward_point_mem {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (xstar : Vec n) (_hmin : ∀ x, F xstar ≤ F x) (b : ℝ) (hb : F xstar < b)
    (K : Set (Vec n)) (hK_def : K = {x | F x ≤ b}) (_hK : IsCompact K)
    {x : Vec n} (hx : x ∈ K) {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    x - τ • (x - xstar) ∈ K := by
  subst hK_def
  have he : x - τ • (x - xstar) = (1 - τ) • x + τ • xstar := by module
  rw [he]
  exact sublevel_convex hF b hx (show F xstar ≤ b from hb.le) (by linarith) hτ0 (by ring)

/-- Item `A/global/prose/011` (`paper/sections/global.tex:48-49`): "The parameter $\tau$ is a
fraction of the distance to $x_*$, rather than a Euclidean step length." The inward point
$x-\tau r_x$ is at Euclidean distance $\tau\|r_x\|$ from $x$ and $(1-\tau)\|r_x\|$ from
$x_*$. -/
theorem inward_point_fraction {n : ℕ} (xstar x : Vec n) {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    ‖euclideanVector (x - τ • (x - xstar) - x)‖ = τ * ‖euclideanVector (x - xstar)‖ ∧
      ‖euclideanVector (x - τ • (x - xstar) - xstar)‖ =
        (1 - τ) * ‖euclideanVector (x - xstar)‖ := by
  constructor
  · have he : x - τ • (x - xstar) - x = (-τ) • (x - xstar) := by module
    rw [he, norm_euclideanVector_smul, abs_neg, abs_of_nonneg hτ0]
  · have he : x - τ • (x - xstar) - xstar = (1 - τ) • (x - xstar) := by module
    rw [he, norm_euclideanVector_smul, abs_of_nonneg (by linarith)]

/-- The restriction of $u^2+|v|$ to the vertical line through $(u,0)$ is $u^2+|t|$, so the
benchmark is not differentiable on the line $v=0$. -/
theorem mixed_not_differentiable (F : Vec 2 → ℝ) (hF_def : ∀ x, F x = (x 0) ^ 2 + |x 1|)
    (u : ℝ) : ¬ DifferentiableAt ℝ F ![u, 0] := by
  intro hd
  have hl : DifferentiableAt ℝ (fun t : ℝ => (![u, 0] : Vec 2) + t • (![0, 1] : Vec 2)) 0 :=
    (differentiableAt_const _).add (differentiableAt_id.smul_const _)
  have hd' : DifferentiableAt ℝ F ((![u, 0] : Vec 2) + (0 : ℝ) • (![0, 1] : Vec 2)) := by
    simpa using hd
  have hc := (hd'.comp (0 : ℝ) hl).sub_const (u ^ 2)
  have hfun : (fun t : ℝ => (F ∘ fun t : ℝ => (![u, 0] : Vec 2) + t • (![0, 1] : Vec 2)) t - u ^ 2)
      = fun t : ℝ => |t| := by
    funext t
    simp [hF_def]
  rw [hfun] at hc
  exact not_differentiableAt_abs_zero hc

/-- Item `A/global/prose/013` (`paper/sections/global.tex:50-52`): "Thus nonsmoothness at
the solution is permitted, including the absolute-value term in the benchmark." The benchmark
$F(u,v)=u^2+|v|$ is minimized at $(0,0)$ and not differentiable there, yet satisfies
\eqref{art:inward-condition} on every compact sublevel $\{F\le b\}$, $b>F_*=0$ (the article
supplement's `ArticlePositive.mixed_inward_on_sublevel`). -/
theorem mixed_inward_condition (F : Vec 2 → ℝ) (hF_def : ∀ x, F x = (x 0) ^ 2 + |x 1|) :
    (∀ x, F 0 ≤ F x) ∧ ¬ DifferentiableAt ℝ F 0 ∧
      ∀ b : ℝ, 0 < b → IsCompact {x | F x ≤ b} ∧ InwardModelCondition F 0 {x | F x ≤ b} := by
  have hF0 : F 0 = 0 := by simp [hF_def]
  have hmin : ∀ x, F 0 ≤ F x := fun x => by rw [hF0, hF_def]; positivity
  have hnd : ¬ DifferentiableAt ℝ F 0 := by
    have h := mixed_not_differentiable F hF_def 0
    have he : (![0, 0] : Vec 2) = 0 := by ext i; fin_cases i <;> rfl
    rwa [he] at h
  obtain rfl : F = UnexcitedMetric.objective := funext hF_def
  refine ⟨hmin, hnd, fun b _ => ⟨?_, ?_⟩⟩
  · exact Localization.sublevel_compact UnexcitedMetric.objective_convex 0 hmin
      (fun y hy => UnexcitedMetric.unique_minimum hy) b
  · rw [inwardModelCondition_iff]
    exact ArticlePositive.mixed_inward_on_sublevel b

/-! ### Theorem `art:radial-equivalence` and its proof -/

/-- Proof of Theorem `art:radial-equivalence`, undisplayed claim of
`paper/sections/global.tex:59-60` (not a register item): constants $\Lambda,R>0$ bounding
the Euclidean norms of all subgradients at points of the compact set $K$ and $\|x-x_*\|$ on
$K$ exist. -/
theorem exists_subgradient_and_radius_bounds {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (xstar : Vec n) {K : Set (Vec n)} (hK : IsCompact K) :
    ∃ Λ R : ℝ, 0 < Λ ∧ 0 < R ∧
      (∀ x ∈ K, ∀ v : Vec n, (∀ y, F x + dot v (y - x) ≤ F y) → ‖euclideanVector v‖ ≤ Λ) ∧
      (∀ x ∈ K, ‖euclideanVector (x - xstar)‖ ≤ R) := by
  obtain ⟨G, hG, hg⟩ := convex_supporting_bound_on_compact hF hK
  obtain ⟨R, hR, hr⟩ := compact_sqNorm_radius hK xstar
  refine ⟨G, R, hG, hR, fun x hx v hv => norm_le_of_sqNorm_le hG.le (hg x hx v ?_),
    fun x hx => norm_le_of_sqNorm_le hR.le (hr x hx)⟩
  intro y
  linarith [hv y]

/-- Proof of Theorem `art:radial-equivalence`, undisplayed claim of
`paper/sections/global.tex:60-61` (not a register item): with $\Lambda$ bounding subgradient
norms on $K$, supporting inequalities give $|F(x)-F(z)|\le\Lambda\|x-z\|$ on $K$. -/
theorem lipschitz_on_K {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    {K : Set (Vec n)} (Λ : ℝ)
    (hΛK : ∀ x ∈ K, ∀ v : Vec n, (∀ y, F x + dot v (y - x) ≤ F y) → ‖euclideanVector v‖ ≤ Λ)
    {x z : Vec n} (hx : x ∈ K) (hz : z ∈ K) :
    |F x - F z| ≤ Λ * ‖euclideanVector (x - z)‖ := by
  obtain ⟨vx, hvx⟩ := ConvexSubdifferential.subdifferential_nonempty hF x
  obtain ⟨vz, hvz⟩ := ConvexSubdifferential.subdifferential_nonempty hF z
  have hbx : ‖euclideanVector vx‖ ≤ Λ := hΛK x hx vx (fun y => by have := hvx y; linarith)
  have hbz : ‖euclideanVector vz‖ ≤ Λ := hΛK z hz vz (fun y => by have := hvz y; linarith)
  have h1 : dot vx (z - x) ≤ F z - F x := hvx z
  have h2 : dot vz (x - z) ≤ F x - F z := hvz x
  have c1 := abs_dot_le_norm_mul_norm vx (z - x)
  have c2 := abs_dot_le_norm_mul_norm vz (x - z)
  rw [← norm_euclideanVector_sub_comm] at c1
  have hn := norm_nonneg (euclideanVector (x - z))
  have e1 := mul_le_mul_of_nonneg_right hbx hn
  have e2 := mul_le_mul_of_nonneg_right hbz hn
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (dot vz (x - z))]
  · linarith [neg_abs_le (dot vx (z - x))]

/-- Item `A/global/disp/004` (`paper/sections/global.tex:63-65`), in the proof of Theorem
`art:radial-equivalence`: the supporting-plane error
\[ D_F(z,x)=F(z)-F(x)-\nabla F(x)^T(z-x)\ge0. \]
Stated under the hypotheses of the theorem ($F$ finite convex, $x_*$ a minimizer,
$K=\{F\le b\}$ compact with $b>F_*$) and the constants $\Lambda,R$ chosen before the display;
$D$ is $D_F(z,x)$ with its defining equation. Only $x$ is differentiable ("only its
supporting endpoint needs to be differentiable"); $z$ is arbitrary. -/
theorem supporting_plane_error {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (xstar : Vec n) (_hmin : ∀ x, F xstar ≤ F x) (b : ℝ) (_hb : F xstar < b)
    (K : Set (Vec n)) (_hK_def : K = {x | F x ≤ b}) (_hK : IsCompact K)
    (Λ R : ℝ) (_hΛ : 0 < Λ) (_hR : 0 < R)
    (_hΛK : ∀ x ∈ K, ∀ v : Vec n, (∀ y, F x + dot v (y - x) ≤ F y) → ‖euclideanVector v‖ ≤ Λ)
    (_hRK : ∀ x ∈ K, ‖euclideanVector (x - xstar)‖ ≤ R)
    (x z g : Vec n) (hg : HasFDerivAt F (gradientFunctional g) x)
    (D : ℝ) (hD : D = F z - F x - dot g (z - x)) :
    0 ≤ D := by
  rw [hD]
  linarith [convex_supporting_inequality hF hg z]

/-- Proof of Theorem `art:radial-equivalence`, undisplayed claim of
`paper/sections/global.tex:67-68` (not a register item): at differentiable endpoints
$T=D_F(z,x)+D_F(x,z)$. -/
theorem curvature_eq_errors {n : ℕ} (F : Vec n → ℝ) (x z g h : Vec n) :
    dot (h - g) (z - x) = (F z - F x - dot g (z - x)) + (F x - F z - dot h (x - z)) :=
  RadialCertificate.secantCurvature_eq_errors F x z g h

/-- Item `A/global/disp/005` (`paper/sections/global.tex:73-75`), in the proof of Theorem
`art:radial-equivalence`: "If $N\ge0$, compare the supporting plane at $x$ with the inward
model at $z-\tau r_z$ to obtain
\[ \tau N\le D_F(z,x)+\tfrac12M\tau^2." \]
Stated under the hypotheses of the theorem, the constants $\Lambda,R$, the inward condition,
a fixed positive band $\eta>0$ with its constants $M\ge0$, $\theta\in(0,1/2]$ (hypothesis
`hMθ`, the inward condition on that band), a pair of differentiable $x,z\in K$ with
$F_*+\eta\le F(z)\le F(x)$, $T>0$, the case $N\ge0$, and $0\le\tau\le\theta$. -/
theorem inward_probe_at_z {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (xstar : Vec n) (_hmin : ∀ x, F xstar ≤ F x) (b : ℝ) (_hb : F xstar < b)
    (K : Set (Vec n)) (_hK_def : K = {x | F x ≤ b}) (_hK : IsCompact K)
    (Λ R : ℝ) (_hΛ : 0 < Λ) (_hR : 0 < R)
    (_hΛK : ∀ x ∈ K, ∀ v : Vec n, (∀ y, F x + dot v (y - x) ≤ F y) → ‖euclideanVector v‖ ≤ Λ)
    (_hRK : ∀ x ∈ K, ‖euclideanVector (x - xstar)‖ ≤ R)
    (_hIR : InwardModelCondition F xstar K)
    (η : ℝ) (_hη : 0 < η) (M θ : ℝ) (_hM : 0 ≤ M) (_hθ : 0 < θ) (_hθ' : θ ≤ 1 / 2)
    (hMθ : ∀ x g : Vec n, x ∈ K → HasFDerivAt F (gradientFunctional g) x → F xstar + η ≤ F x →
      ∀ τ : ℝ, 0 ≤ τ → τ ≤ θ →
        0 ≤ F (x - τ • (x - xstar)) - F x + τ * dot g (x - xstar) ∧
          F (x - τ • (x - xstar)) - F x + τ * dot g (x - xstar) ≤ M / 2 * τ ^ 2)
    (x z g h : Vec n) (_hx : x ∈ K) (hz : z ∈ K)
    (hg : HasFDerivAt F (gradientFunctional g) x) (hh : HasFDerivAt F (gradientFunctional h) z)
    (hzband : F xstar + η ≤ F z) (_horder : F z ≤ F x)
    (T N : ℝ) (_hT_def : T = dot (h - g) (z - x)) (hN_def : N = dot (h - g) (z - xstar))
    (_hT : 0 < T) (_hN : 0 ≤ N) (Dzx : ℝ) (hDzx : Dzx = F z - F x - dot g (z - x))
    (τ : ℝ) (hτ0 : 0 ≤ τ) (hτθ : τ ≤ θ) :
    τ * N ≤ Dzx + 1 / 2 * M * τ ^ 2 := by
  have hir : RadialCertificate.supportingError F z h (RadialCertificate.inwardPoint xstar z τ) ≤
      M / 2 * τ ^ 2 := by
    rw [RadialCertificate.inward_error_eq]
    exact (hMθ z h hz hh hzband τ hτ0 hτθ).2
  have hp := RadialCertificate.inward_probe hF xstar x z g h hg M τ hir
  rw [hN_def, hDzx]
  unfold RadialCertificate.radialNumerator RadialCertificate.supportingError at hp
  linarith

/-- Item `A/global/disp/006` (`paper/sections/global.tex:77-79`), in the proof of Theorem
`art:radial-equivalence`: "If $N<0$, reverse the endpoints and use the inward model at $x$:
\[ \tau(T-N)\le D_F(x,z)+\tfrac12M\tau^2." \]
Stated under the same assumptions as `inward_probe_at_z`, with the case $N<0$ and
$D_F(x,z)=F(x)-F(z)-\nabla F(z)^T(x-z)$. -/
theorem inward_probe_at_x {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (xstar : Vec n) (_hmin : ∀ x, F xstar ≤ F x) (b : ℝ) (_hb : F xstar < b)
    (K : Set (Vec n)) (_hK_def : K = {x | F x ≤ b}) (_hK : IsCompact K)
    (Λ R : ℝ) (_hΛ : 0 < Λ) (_hR : 0 < R)
    (_hΛK : ∀ x ∈ K, ∀ v : Vec n, (∀ y, F x + dot v (y - x) ≤ F y) → ‖euclideanVector v‖ ≤ Λ)
    (_hRK : ∀ x ∈ K, ‖euclideanVector (x - xstar)‖ ≤ R)
    (_hIR : InwardModelCondition F xstar K)
    (η : ℝ) (_hη : 0 < η) (M θ : ℝ) (_hM : 0 ≤ M) (_hθ : 0 < θ) (_hθ' : θ ≤ 1 / 2)
    (hMθ : ∀ x g : Vec n, x ∈ K → HasFDerivAt F (gradientFunctional g) x → F xstar + η ≤ F x →
      ∀ τ : ℝ, 0 ≤ τ → τ ≤ θ →
        0 ≤ F (x - τ • (x - xstar)) - F x + τ * dot g (x - xstar) ∧
          F (x - τ • (x - xstar)) - F x + τ * dot g (x - xstar) ≤ M / 2 * τ ^ 2)
    (x z g h : Vec n) (hx : x ∈ K) (_hz : z ∈ K)
    (hg : HasFDerivAt F (gradientFunctional g) x) (hh : HasFDerivAt F (gradientFunctional h) z)
    (hzband : F xstar + η ≤ F z) (horder : F z ≤ F x)
    (T N : ℝ) (hT_def : T = dot (h - g) (z - x)) (hN_def : N = dot (h - g) (z - xstar))
    (_hT : 0 < T) (_hN : N < 0) (Dxz : ℝ) (hDxz : Dxz = F x - F z - dot h (x - z))
    (τ : ℝ) (hτ0 : 0 ≤ τ) (hτθ : τ ≤ θ) :
    τ * (T - N) ≤ Dxz + 1 / 2 * M * τ ^ 2 := by
  have hir : RadialCertificate.supportingError F x g (RadialCertificate.inwardPoint xstar x τ) ≤
      M / 2 * τ ^ 2 := by
    rw [RadialCertificate.inward_error_eq]
    exact (hMθ x g hx hg (hzband.trans horder) τ hτ0 hτθ).2
  have hp := RadialCertificate.inward_probe hF xstar z x h g hh M τ hir
  rw [RadialCertificate.radialNumerator_swap xstar x z g h] at hp
  rw [hT_def, hN_def, hDxz]
  unfold RadialCertificate.secantCurvature RadialCertificate.radialNumerator
    RadialCertificate.supportingError at hp
  linarith

/-- Item `A/global/disp/007`, equation `art:inward-to-radial`
(`paper/sections/global.tex:88-90`), in the proof of Theorem `art:radial-equivalence`:
\[ N^2\le \max\{2M,4\Lambda R/\theta\}\,T. \]
Stated under the hypotheses of the theorem, the constants $\Lambda,R>0$ (Euclidean bounds on
subgradients at points of $K$ and on $\|x-x_*\|$ for $x\in K$), the inward condition, a
fixed positive band $\eta$ with its constants $M\ge0$, $\theta\in(0,1/2]$, and a pair of
differentiable $x,z\in K$ with $F_*+\eta\le F(z)\le F(x)$ and $T>0$. The proof is the
paper's: displays `inward_probe_at_z` ($N\ge0$) and `inward_probe_at_x` ($N<0$) give
$\tau A\le D+M\tau^2/2$ with $A\in[|N|,2\Lambda R]$, and the choice of $\tau$ is the library's
`RadialCertificate.inward_probe_quadratic_bound`. -/
theorem inward_to_radial {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (xstar : Vec n) (hmin : ∀ x, F xstar ≤ F x) (b : ℝ) (hb : F xstar < b)
    (K : Set (Vec n)) (hK_def : K = {x | F x ≤ b}) (hK : IsCompact K)
    (Λ R : ℝ) (hΛ : 0 < Λ) (hR : 0 < R)
    (hΛK : ∀ x ∈ K, ∀ v : Vec n, (∀ y, F x + dot v (y - x) ≤ F y) → ‖euclideanVector v‖ ≤ Λ)
    (hRK : ∀ x ∈ K, ‖euclideanVector (x - xstar)‖ ≤ R)
    (hIR : InwardModelCondition F xstar K)
    (η : ℝ) (hη : 0 < η) (M θ : ℝ) (hM : 0 ≤ M) (hθ : 0 < θ) (hθ' : θ ≤ 1 / 2)
    (hMθ : ∀ x g : Vec n, x ∈ K → HasFDerivAt F (gradientFunctional g) x → F xstar + η ≤ F x →
      ∀ τ : ℝ, 0 ≤ τ → τ ≤ θ →
        0 ≤ F (x - τ • (x - xstar)) - F x + τ * dot g (x - xstar) ∧
          F (x - τ • (x - xstar)) - F x + τ * dot g (x - xstar) ≤ M / 2 * τ ^ 2)
    (x z g h : Vec n) (hx : x ∈ K) (hz : z ∈ K)
    (hg : HasFDerivAt F (gradientFunctional g) x) (hh : HasFDerivAt F (gradientFunctional h) z)
    (hzband : F xstar + η ≤ F z) (horder : F z ≤ F x)
    (T N : ℝ) (hT_def : T = dot (h - g) (z - x)) (hN_def : N = dot (h - g) (z - xstar))
    (hT : 0 < T) :
    N ^ 2 ≤ max (2 * M) (4 * Λ * R / θ) * T := by
  have hsupp (w v : Vec n) (hv : HasFDerivAt F (gradientFunctional v) w) :
      ∀ y, F w + dot v (y - w) ≤ F y := fun y => by
    linarith [convex_supporting_inequality hF hv y]
  have hgΛ : sqNorm g ≤ Λ ^ 2 := sqNorm_le_of_norm_le (hΛK x hx g (hsupp x g hg))
  have hhΛ : sqNorm h ≤ Λ ^ 2 := sqNorm_le_of_norm_le (hΛK z hz h (hsupp z h hh))
  have hrz : sqNorm (z - xstar) ≤ R ^ 2 := sqNorm_le_of_norm_le (hRK z hz)
  have hrx : sqNorm (x - xstar) ≤ R ^ 2 := sqNorm_le_of_norm_le (hRK x hx)
  have hC : 0 ≤ max (2 * M) (4 * Λ * R / θ) := le_trans (by linarith) (le_max_left _ _)
  have hconst : max (2 * M) (2 * (2 * Λ * R) / θ) = max (2 * M) (4 * Λ * R / θ) := by ring_nf
  have hsplit := curvature_eq_errors F x z g h
  have hDzx0 : 0 ≤ F z - F x - dot g (z - x) :=
    supporting_plane_error hF xstar hmin b hb K hK_def hK Λ R hΛ hR hΛK hRK x z g hg _ rfl
  have hDxz0 : 0 ≤ F x - F z - dot h (x - z) :=
    supporting_plane_error hF xstar hmin b hb K hK_def hK Λ R hΛ hR hΛK hRK z x h hh _ rfl
  by_cases hN : 0 ≤ N
  · -- `A = N`, `D = D_F(z,x)`
    have hB : N ≤ 2 * Λ * R := by
      rw [hN_def]
      exact (le_abs_self _).trans (RadialCertificate.abs_radialNumerator_le_two_mul xstar z g h
        Λ R hΛ.le hR.le hgΛ hhΛ hrz)
    have hprobe : ∀ τ : ℝ, 0 ≤ τ → τ ≤ θ →
        τ * N ≤ (F z - F x - dot g (z - x)) + M / 2 * τ ^ 2 := fun τ h0 h1 => by
      have := inward_probe_at_z hF xstar hmin b hb K hK_def hK Λ R hΛ hR hΛK hRK hIR η hη M θ hM
        hθ hθ' hMθ x z g h hx hz hg hh hzband horder T N hT_def hN_def hT hN _ rfl τ h0 h1
      linarith
    have hq := RadialCertificate.inward_probe_quadratic_bound hN hB hDzx0 hM hθ hprobe
    rw [hconst] at hq
    have hDT : F z - F x - dot g (z - x) ≤ T := by rw [hT_def]; linarith
    exact hq.trans (mul_le_mul_of_nonneg_left hDT hC)
  · -- `A = T - N`, `D = D_F(x,z)`
    have hNneg : N < 0 := lt_of_not_ge hN
    have hA : 0 ≤ T - N := by linarith
    have hB : T - N ≤ 2 * Λ * R := by
      have hs := RadialCertificate.radialNumerator_swap xstar x z g h
      have hab := RadialCertificate.abs_radialNumerator_le_two_mul xstar x h g Λ R hΛ.le hR.le
        hhΛ hgΛ hrx
      unfold RadialCertificate.radialNumerator RadialCertificate.secantCurvature at hs
      unfold RadialCertificate.radialNumerator at hab
      rw [hT_def, hN_def, ← hs]
      exact (le_abs_self _).trans hab
    have hprobe : ∀ τ : ℝ, 0 ≤ τ → τ ≤ θ →
        τ * (T - N) ≤ (F x - F z - dot h (x - z)) + M / 2 * τ ^ 2 := fun τ h0 h1 => by
      have := inward_probe_at_x hF xstar hmin b hb K hK_def hK Λ R hΛ hR hΛK hRK hIR η hη M θ hM
        hθ hθ' hMθ x z g h hx hz hg hh hzband horder T N hT_def hN_def hT hNneg _ rfl τ h0 h1
      linarith
    have hq := RadialCertificate.inward_probe_quadratic_bound hA hB hDxz0 hM hθ hprobe
    rw [hconst] at hq
    have hDT : F x - F z - dot h (x - z) ≤ T := by rw [hT_def]; linarith
    have hNA : N ^ 2 ≤ (T - N) ^ 2 := by nlinarith
    exact hNA.trans (hq.trans (mul_le_mul_of_nonneg_left hDT hC))

/-- Item `A/global/theorem/art:radial-equivalence`, Theorem `art:radial-equivalence`
(`paper/sections/global.tex:54-57`): "For finite convex $F$ and the compact sublevel $K$
above, \eqref{art:inward-condition} implies \eqref{art:radial-condition}." The setting
(lines 19-20): $x_*$ a minimizer, $F_*=F(x_*)$, $K=\{x:F(x)\le b\}$ compact, $b>F_*$.

The proof is the paper's: `exists_subgradient_and_radius_bounds` chooses $\Lambda,R$, and
`inward_to_radial` (equation `art:inward-to-radial`) gives the constant
$C_\eta=\max\{2M,4\Lambda R/\theta\}$. The library proves the implication for every compact
`K` and every reference point as `RadialCertificate.radial_of_inward_on_compact`. -/
theorem radial_equivalence {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (xstar : Vec n) (hmin : ∀ x, F xstar ≤ F x) (b : ℝ) (hb : F xstar < b)
    (K : Set (Vec n)) (hK_def : K = {x | F x ≤ b}) (hK : IsCompact K) :
    InwardModelCondition F xstar K → RadialSecantCondition F xstar K := by
  intro hIR
  obtain ⟨Λ, R, hΛ, hR, hΛK, hRK⟩ := exists_subgradient_and_radius_bounds hF xstar hK
  intro η hη
  obtain ⟨M, θ, hM, hθ, hθ', hMθ⟩ := hIR η hη
  refine ⟨max (2 * M) (4 * Λ * R / θ), le_trans (by linarith) (le_max_left _ _), ?_⟩
  intro x z g h hx hz hg hh hzband horder hT
  exact inward_to_radial hF xstar hmin b hb K hK_def hK Λ R hΛ hR hΛK hRK hIR η hη M θ hM hθ hθ'
    hMθ x z g h hx hz hg hh hzband horder _ _ rfl rfl hT

/-- Item `A/global/prose/014` (`paper/sections/global.tex:93-94`): "The converse
implication, including inward samples that are not differentiable, is proved in Chapter~4 of
the complete companion." In the setting of the section, \eqref{art:radial-condition} implies
\eqref{art:inward-condition} on the same compact sublevel; the inward condition asks no
differentiability at $x-\tau r_x$ (the library's
`RadialCertificate.inward_of_radial_on_compact_sublevel`). -/
theorem radial_implies_inward {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (xstar : Vec n) (hmin : ∀ x, F xstar ≤ F x) (b : ℝ) (hb : F xstar < b)
    (K : Set (Vec n)) (hK_def : K = {x | F x ≤ b}) (hK : IsCompact K) :
    RadialSecantCondition F xstar K → InwardModelCondition F xstar K := by
  subst hK_def
  intro hRS
  rw [inwardModelCondition_iff]
  exact RadialCertificate.inward_of_radial_on_compact_sublevel hF xstar hmin b hb hK
    ((radialSecantCondition_iff F xstar _).mp hRS)

/-! ### Corollary `art:radial-convergence` -/

/-- Proof of Corollary `art:radial-convergence`, undisplayed claims of
`paper/sections/global.tex:104-108` (not a register item): "Take $W_\eta(x)=r_xr_x^T$.
Convexity gives $g^Tr_x\ge F(x)-F_*\ge\eta$, proving visibility with $m_\eta=\eta^2$.
Equation~\eqref{art:radial-condition} gives secant control on eligible pairs. Finally
$r_z=r_x+s$ implies $\Pi_sr_z=\Pi_sr_x$, so transport holds with $L_\eta=0$." Under the
radial condition, every positive band carries a band certificate (Definition
`art:band-certificate`: the library's `BandCertificate` with $C_\eta\ge0$) with field
$W(x)=r_xr_x^T$, $m=\eta^2$ and $L=0$, for every pair of line-search constants $0<c_1$,
$c_2<1$. -/
theorem radial_band_certificate {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (xstar : Vec n) (K : Set (Vec n)) (hRS : RadialSecantCondition F xstar K)
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : c₂ < 1) (η : ℝ) (hη : 0 < η) :
    ∃ W : TransportedCertificate.BandCertificate F K (F xstar) c₁ c₂ η,
      W.W = (fun x => outer (x - xstar) (x - xstar)) ∧ W.m = η ^ 2 ∧ 0 ≤ W.C ∧ W.L = 0 := by
  obtain ⟨C, hC0, hC⟩ := hRS η hη
  refine ⟨TransportedCertificate.rankOneCertificate (fun x => x - xstar) (η ^ 2) C 0 1
    (sq_pos_of_pos hη) (le_refl _) zero_lt_one ?_ ?_ ?_, rfl, rfl, hC0, rfl⟩
  · intro x hx g hg
    have hs := convex_supporting_inequality hF hg xstar
    have he : dot g (xstar - x) = -dot g (x - xstar) := by
      unfold dot
      simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
      ring
    rw [he] at hs
    have hgap : η ≤ dot g (x - xstar) := by linarith [hx.2]
    nlinarith
  · intro x z g h hx hz e _
    have hdec : F z ≤ F x := by
      have hp := mul_pos hc₁ e.decrease_pos
      linarith [e.armijo]
    exact hC x z g h hx.1 hz.1 e.gradient_x e.gradient_z hz.2 hdec
      (TransportedCertificate.eligible_curvature_pos e hc₂)
  · intro x z g h _ _ _ _
    refine ⟨1, 1, ?_, ?_⟩
    · simp only [one_smul, TransportedCertificate.pairStep]
      abel
    · simp

/-- Item `A/global/corollary/art:radial-convergence`, Corollary `art:radial-convergence`
(`paper/sections/global.tex:98-102`): "Under either condition, every admissible run starting
in $K$ converges in value to $F_*$ and in distance to $\arg\min F$. With a unique minimizer
it converges to $x_*$." In the setting of lines 19-20 ($x_*$ a minimizer, $F_*=F(x_*)$,
$K=\{F\le b\}$ compact, $b>F_*$); "either condition" is \eqref{art:radial-condition} or
\eqref{art:inward-condition}. The distance is the Euclidean one,
`euclideanSolutionDistance F x` $=\operatorname{dist}(x,\arg\min F)$.

The proof is the paper's: Theorem `art:radial-equivalence` reduces the inward condition to the
radial one, `radial_band_certificate` gives the band certificates, and Theorem
`art:certificate` is the library's
`AdmissibleBFGSRun.transported_certificate_convergence_on_sublevel`. -/
theorem radial_convergence {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (xstar : Vec n) (hmin : ∀ x, F xstar ≤ F x) (b : ℝ) (hb : F xstar < b)
    (K : Set (Vec n)) (hK_def : K = {x | F x ≤ b}) (hK : IsCompact K)
    (hcond : RadialSecantCondition F xstar K ∨ InwardModelCondition F xstar K)
    (R : AdmissibleBFGSRun n F) (hx0 : R.x 0 ∈ K) :
    Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) ∧
      Tendsto (fun k => euclideanSolutionDistance F (R.x k)) atTop (𝓝 0) ∧
      ((∀ y, (∀ x, F y ≤ F x) → y = xstar) → Tendsto R.x atTop (𝓝 xstar)) := by
  have hRS : RadialSecantCondition F xstar K :=
    hcond.elim id (radial_equivalence hF xstar hmin b hb K hK_def hK)
  have hcert : TransportedCertificate.HasBandCertificates F K (F xstar) R.c₁ R.c₂ := by
    intro η hη _
    obtain ⟨W, -⟩ := radial_band_certificate hF xstar K hRS R.c₁_pos R.c₂_lt_one η hη
    exact ⟨W⟩
  subst hK_def
  obtain ⟨hv, -, hi⟩ := R.transported_certificate_convergence_on_sublevel b hK xstar hmin hx0 hcert
  refine ⟨hv, euclidean_distance_to_argmin_of_values (convex_continuous hF) xstar hmin hK
    (fun k => (R.objective_le_initial k).trans hx0) hv, fun hu => hi (fun x hx => hu x ?_)⟩
  intro y
  rw [hx]
  exact hmin y

/-! ### Remarks on the inward condition (lines 111-117) -/

/-- Item `A/global/prose/017` (`paper/sections/global.tex:111-113`): "In a smooth region its
infinitesimal expression is $r_x^T\nabla^2F(x)r_x$, rather than the largest Hessian
eigenvalue." Where $F$ is $C^2$ at $x$, the second derivative at $\tau=0$ of the inward
remainder $\tau\mapsto F(x-\tau r_x)-F(x)+\tau\nabla F(x)^Tr_x$ is $r_x^T\nabla^2F(x)r_x$,
with $\nabla^2F(x)$ the library's `RadialHessian.matrix F x` (entries of the second Fréchet
derivative). -/
theorem inward_remainder_second_derivative {n : ℕ} {F : Vec n → ℝ} {x : Vec n}
    (hF2 : ContDiffAt ℝ 2 F x) (xstar g : Vec n)
    (_hg : HasFDerivAt F (gradientFunctional g) x) :
    deriv (deriv (fun τ : ℝ => F (x - τ • (x - xstar)) - F x + τ * dot g (x - xstar))) 0 =
      dot (x - xstar) (RadialHessian.matrix F x *ᵥ (x - xstar)) := by
  set r := x - xstar with hr
  have hE : (fun τ : ℝ => F (x - τ • r) - F x + τ * dot g r) =
      fun τ => F (RadialHessian.ray x (-r) τ) + (τ * dot g r - F x) := by
    funext τ
    simp only [RadialHessian.ray, smul_neg, ← sub_eq_add_neg]
    ring
  have hev : ∀ᶠ τ in 𝓝 (0 : ℝ), DifferentiableAt ℝ (fun τ => F (RadialHessian.ray x (-r) τ)) τ := by
    have h1 : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ F y :=
      (hF2.eventually (by simp)).mono (fun y hy => hy.differentiableAt (by norm_num))
    have hcont : Tendsto (RadialHessian.ray x (-r)) (𝓝 0) (𝓝 x) := by
      have := (RadialHessian.ray_hasDerivAt x (-r) 0).continuousAt.tendsto
      simpa [RadialHessian.ray] using this
    filter_upwards [hcont.eventually h1] with τ hτ
    exact hτ.comp τ (RadialHessian.ray_hasDerivAt x (-r) τ).differentiableAt
  have hderiv : deriv (fun τ : ℝ => F (x - τ • r) - F x + τ * dot g r) =ᶠ[𝓝 0]
      fun τ => deriv (fun τ => F (RadialHessian.ray x (-r) τ)) τ + dot g r := by
    filter_upwards [hev] with τ hτ
    rw [hE, deriv_add hτ (by fun_prop)]
    congr 1
    simp
  rw [hderiv.deriv_eq, deriv_add_const, RadialHessian.ray_second_derivative_matrix hF2 (-r)]
  change (-r) ⬝ᵥ (RadialHessian.matrix F x *ᵥ -r) = r ⬝ᵥ (RadialHessian.matrix F x *ᵥ r)
  rw [Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]

/-- Item `A/global/prose/018` (`paper/sections/global.tex:113-115`): "A bound almost
everywhere on that expression alone would miss a jump of the derivative along a ray; the
function-value condition \eqref{art:inward-condition} includes such jumps." For the strongly
convex $f(t)=(t+2)^2/2+|t|$ (derivative jump at $t=0$), $F(x)=f(x_0)$ on $\R^1$, minimizer
$x_*=-1$ and the compact sublevel $K=\{F\le3\}$: the radial expression
$r_t^T\nabla^2f(t)r_t=(t+1)^2f''(t)$ lies in $[0,3]$ for almost every $t$ with $f(t)\le3$, yet
\eqref{art:inward-condition} and \eqref{art:radial-condition} fail on $K$ (the library's
`RadialSingularCurvature.singular_curvature_counterexample`; the inward failure follows by
Theorem `art:radial-equivalence`). -/
theorem ae_curvature_misses_jump (f : ℝ → ℝ) (hf : ∀ t, f t = (t + 2) ^ 2 / 2 + |t|)
    (F : Vec 1 → ℝ) (hF : ∀ x, F x = f (x 0)) (xstar : Vec 1) (hxstar : xstar = fun _ => -1) :
    (∀ᵐ t : ℝ ∂MeasureTheory.volume, f t ≤ 3 →
      0 ≤ (t + 1) ^ 2 * deriv (deriv f) t ∧ (t + 1) ^ 2 * deriv (deriv f) t ≤ 3) ∧
      ¬ InwardModelCondition F xstar {x | F x ≤ 3} ∧
      ¬ RadialSecantCondition F xstar {x | F x ≤ 3} := by
  obtain rfl : f = ScalarCounterexamples.shiftedAbs := funext hf
  obtain rfl : F = ScalarCounterexamples.shiftedObjective := funext hF
  obtain rfl : xstar = OneDimensional.embed (-1) := by rw [hxstar]; ext i; simp
  have hrad : ¬ RadialSecantCondition ScalarCounterexamples.shiftedObjective
      (OneDimensional.embed (-1)) {x | ScalarCounterexamples.shiftedObjective x ≤ 3} :=
    fun h => RadialSingularCurvature.shifted_no_radial_secant_bounds
      ((radialSecantCondition_iff _ _ _).mp h)
  refine ⟨RadialSingularCurvature.shifted_radial_hessian_on_sublevel_ae, fun h => hrad ?_, hrad⟩
  have hb : ScalarCounterexamples.shiftedObjective (OneDimensional.embed (-1)) < 3 := by
    norm_num [ScalarCounterexamples.shiftedObjective, ScalarCounterexamples.shiftedAbs]
  exact radial_equivalence ScalarCounterexamples.shiftedObjective_convex _
    ScalarCounterexamples.shiftedObjective_minimum 3 hb _ rfl
    (ScalarCounterexamples.shiftedObjective_sublevel_compact 3) h

/-- Item `A/global/prose/019` (`paper/sections/global.tex:115-117`): "The condition is
sufficient; Theorem~\ref{art:nonradial-example} will exhibit convergence where it fails on
positive bands arbitrarily near the minimizer." For the objective $F=\max_if_i$ of Theorem
`art:nonradial-example` (`PlanarQuadraticExample.objective`, `paper/sections/local.tex:369-375`),
with minimizer $0$ and $F(0)=0$: on every sublevel $\{F\le b\}$, $b>0$, both
\eqref{art:inward-condition} and \eqref{art:radial-condition} fail (each on some positive
band), while every admissible run with $F(x_0)<1/100$ converges to $0$ in value and iterates
(the library's `PlanarQuadraticExample.not_radial_secant_on_sublevel` and
`PlanarQuadraticExample.converges_without_radial_secant`; the inward failure follows by
Theorem `art:radial-equivalence`). That the condition is sufficient is Corollary
`art:radial-convergence`. -/
theorem nonradial_example_condition_fails :
    (∀ b : ℝ, 0 < b →
      ¬ InwardModelCondition PlanarQuadraticExample.objective 0
          {x | PlanarQuadraticExample.objective x ≤ b} ∧
        ¬ RadialSecantCondition PlanarQuadraticExample.objective 0
          {x | PlanarQuadraticExample.objective x ≤ b}) ∧
      ∀ R : AdmissibleBFGSRun 2 PlanarQuadraticExample.objective,
        PlanarQuadraticExample.objective (R.x 0) < 1 / 100 →
        Tendsto (fun k => PlanarQuadraticExample.objective (R.x k)) atTop (𝓝 0) ∧
          Tendsto R.x atTop (𝓝 0) := by
  have hmin : ∀ x, PlanarQuadraticExample.objective 0 ≤ PlanarQuadraticExample.objective x :=
    fun x => by
      rw [PlanarQuadraticExample.objective_zero]
      exact PlanarQuadraticExample.objective_nonneg x
  have huniq : ∀ x, PlanarQuadraticExample.objective x = PlanarQuadraticExample.objective 0 →
      x = 0 := by
    intro x hx
    rw [PlanarQuadraticExample.objective_zero] at hx
    have hs : sqNorm x = 0 :=
      le_antisymm (hx ▸ PlanarQuadraticExample.objective_lower x) (sqNorm_nonneg x)
    ext i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (x j))).mp hs i
      (Finset.mem_univ i)
    simpa using hi
  refine ⟨fun b hb => ?_, fun R hR => ?_⟩
  · have hrad : ¬ RadialSecantCondition PlanarQuadraticExample.objective 0
        {x | PlanarQuadraticExample.objective x ≤ b} := fun h =>
      PlanarQuadraticExample.not_radial_secant_on_sublevel hb
        ((radialSecantCondition_iff _ _ _).mp h)
    refine ⟨fun h => hrad ?_, hrad⟩
    exact radial_equivalence PlanarQuadraticExample.objective_convex 0 hmin b
      (by rwa [PlanarQuadraticExample.objective_zero]) _ rfl
      (Localization.sublevel_compact PlanarQuadraticExample.objective_convex 0 hmin huniq b) h
  · obtain ⟨hv, hi, -⟩ := PlanarQuadraticExample.converges_without_radial_secant R hR
    exact ⟨hv, hi⟩

/-! ### Homogeneous terms (lines 121-128) -/

/-- Item `A/global/prose/020` (`paper/sections/global.tex:121-122`): "A finite convex
positively homogeneous function is sublinear: its value on $(1-\tau)r$ is exactly $(1-\tau)$
times its value on $r$." Sublinear: subadditive and positively homogeneous; the identity holds
for $\tau\le1$. -/
theorem homogeneous_sublinear {n : ℕ} {γ : Vec n → ℝ} (hγ : ConvexOn ℝ univ γ)
    (hγh : Homogeneous.PositiveDegreeOne γ) :
    (∀ x y, γ (x + y) ≤ γ x + γ y) ∧ (∀ t : ℝ, 0 ≤ t → ∀ x, γ (t • x) = t * γ x) ∧
      ∀ r : Vec n, ∀ τ : ℝ, τ ≤ 1 → γ ((1 - τ) • r) = (1 - τ) * γ r := by
  refine ⟨fun x y => ?_, hγh, fun r τ hτ => hγh (1 - τ) (by linarith) r⟩
  have h := hγ.2 (mem_univ x) (mem_univ y) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have he : x + y = (2 : ℝ) • ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) := by module
  rw [he, hγh 2 (by norm_num)]
  simp only [smul_eq_mul] at h
  linarith

/-- Item `A/global/prose/021` (`paper/sections/global.tex:122-123`): "Its angular
nonsmoothness consequently disappears from the inward remainder." For finite convex
positively homogeneous $\gamma$ (centered at $0$), at every point $r$ where $\gamma$ is
differentiable, the inward remainder vanishes:
$\gamma(r-\tau r)-\gamma(r)+\tau\nabla\gamma(r)^Tr=0$ for $\tau\le1$ (Euler's identity
$\nabla\gamma(r)^Tr=\gamma(r)$). -/
theorem homogeneous_inward_remainder_zero {n : ℕ} {γ : Vec n → ℝ} (hγ : ConvexOn ℝ univ γ)
    (hγh : Homogeneous.PositiveDegreeOne γ) {r p : Vec n}
    (hp : HasFDerivAt γ (gradientFunctional p) r) (τ : ℝ) (hτ : τ ≤ 1) :
    γ (r - τ • r) - γ r + τ * dot p r = 0 := by
  have he := Homogeneous.supporting_euler hγh (convex_supporting_inequality hγ hp)
  have hr : r - τ • r = (1 - τ) • r := by module
  rw [hr, hγh (1 - τ) (by linarith) r, he]
  ring

/-! ### Theorem `art:centered` and its proof -/

theorem eq_zero_of_gradientFunctional_eq_zero {n : ℕ} {g : Vec n}
    (h : gradientFunctional g = 0) : g = 0 := by
  ext i
  have h' := congrArg (fun l : Vec n →L[ℝ] ℝ => l (Pi.single i 1)) h
  simpa [gradientFunctional_apply, dot, Pi.single_apply] using h'

/-- Proof of Theorem `art:centered`, undisplayed claim of `paper/sections/global.tex:144-145`
(not a register item): "Since $g_0\ne0$, convexity implies $F(x_0)>F(x_*)$." -/
theorem initial_value_gt {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (xstar : Vec n) (hmin : ∀ x, F xstar ≤ F x) : F xstar < F (R.x 0) := by
  by_contra hle
  push_neg at hle
  have hloc : IsLocalMin F (R.x 0) := Filter.Eventually.of_forall (fun y => hle.trans (hmin y))
  exact R.gradient_nonzero 0
    (eq_zero_of_gradientFunctional_eq_zero (hloc.hasFDerivAt_eq_zero (R.hasGradient 0)))

/-- The Euclidean norm of the coordinate vector of a linear functional is at most its
operator norm (for the sup norm of `Vec n`). -/
theorem norm_euclideanVector_coords_le {n : ℕ} (l : Vec n →L[ℝ] ℝ) :
    ‖euclideanVector (fun i => l (Pi.single i 1))‖ ≤ ‖l‖ := by
  set p : Vec n := fun i => l (Pi.single i 1) with hp
  have hl : gradientFunctional p = l := gradientFunctional_coordinates l
  have hsq : ‖euclideanVector p‖ ^ 2 = l p := by
    rw [norm_euclideanVector_sq, ← hl, gradientFunctional_apply]
    simp only [sqNorm, dot, pow_two]
  have hle : l p ≤ ‖l‖ * ‖euclideanVector p‖ := by
    have h1 := l.le_opNorm p
    rw [Real.norm_eq_abs] at h1
    exact (le_abs_self _).trans (h1.trans
      (mul_le_mul_of_nonneg_left (norm_le_norm_euclideanVector p) (norm_nonneg _)))
  have h0 := norm_nonneg (euclideanVector p)
  have h0' := norm_nonneg l
  nlinarith

/-- Proof of Theorem `art:centered`, undisplayed claim of `paper/sections/global.tex:145-149`
(not a register item): "On compact convex $K\subset U$, local $C^{1,1}$ regularity provides a
uniform Lipschitz constant $L$ for $\nabla\psi$". The constant is Euclidean:
$\|\nabla\psi(y)-\nabla\psi(x)\|\le L\|y-x\|$ for $x,y\in K$; `coordinateGradient ψ x` is
$\nabla\psi(x)$. (The Lean proof uses one radius of uniform local Lipschitz continuity and the
gradient bound on $K$ instead of subdividing segments, so it needs no convexity of $K$.) -/
theorem uniform_lipschitz_gradient {n : ℕ} {ψ : Vec n → ℝ} {U K : Set (Vec n)}
    (hU : IsOpen U) (hψ : CenteredSmoothSublinear.LocallyC11On U ψ) (hK : IsCompact K)
    (hKU : K ⊆ U) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ K, ∀ y ∈ K,
      ‖euclideanVector (coordinateGradient ψ y - coordinateGradient ψ x)‖ ≤
        L * ‖euclideanVector (y - x)‖ := by
  obtain ⟨M, ρ, hρ, hballs⟩ :=
    CenteredSmoothSublinear.compact_uniform_local_lipschitz hU hK hKU hψ.2
  obtain ⟨G, hG, hbound⟩ := CenteredSmoothSublinear.compact_coordinateGradient_bound hψ.2 hK hKU
  refine ⟨max (M : ℝ) (2 * G / ρ), le_max_of_le_left M.coe_nonneg, ?_⟩
  intro x hx y hy
  have hdiff : coordinateGradient ψ y - coordinateGradient ψ x =
      fun i => (fderiv ℝ ψ y - fderiv ℝ ψ x) (Pi.single i 1) := by
    ext i
    simp [coordinateGradient]
  have hE := norm_le_norm_euclideanVector (y - x)
  have hEn := norm_nonneg (euclideanVector (y - x))
  by_cases hclose : ‖y - x‖ < ρ
  · have hyb : y ∈ Metric.ball x ρ := by
      rw [Metric.mem_ball, dist_eq_norm]
      exact hclose
    have hlip := (hballs x hx).2.norm_sub_le hyb (Metric.mem_ball_self hρ)
    calc ‖euclideanVector (coordinateGradient ψ y - coordinateGradient ψ x)‖
        ≤ ‖fderiv ℝ ψ y - fderiv ℝ ψ x‖ := by rw [hdiff]; exact norm_euclideanVector_coords_le _
      _ ≤ M * ‖y - x‖ := hlip
      _ ≤ M * ‖euclideanVector (y - x)‖ := mul_le_mul_of_nonneg_left hE M.coe_nonneg
      _ ≤ max (M : ℝ) (2 * G / ρ) * ‖euclideanVector (y - x)‖ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hEn
  · push_neg at hclose
    have h2G : ‖euclideanVector (coordinateGradient ψ y - coordinateGradient ψ x)‖ ≤ 2 * G :=
      norm_le_of_sqNorm_le (by positivity)
        (sqNorm_difference_le_four _ _ G (hbound y hy) (hbound x hx))
    calc ‖euclideanVector (coordinateGradient ψ y - coordinateGradient ψ x)‖
        ≤ 2 * G := h2G
      _ = 2 * G / ρ * ρ := by field_simp
      _ ≤ 2 * G / ρ * ‖euclideanVector (y - x)‖ :=
          mul_le_mul_of_nonneg_left (hclose.trans hE) (by positivity)
      _ ≤ max (M : ℝ) (2 * G / ρ) * ‖euclideanVector (y - x)‖ :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hEn

/-- Item `A/global/disp/009` (`paper/sections/global.tex:151-155`), in the proof of Theorem
`art:centered`: "Integrating the gradient along an inward segment consequently gives
\[ \left|\psi(x-\tau r_x)-\psi(x)+\tau\nabla\psi(x)^Tr_x\right|\le\tfrac12L\tau^2\|r_x\|^2." \]
Stated under the hypotheses of the theorem, for an admissible run whose initial sublevel is
compact and contained in $U$, with $K=\{F\le F(x_0)\}$ and a uniform Euclidean Lipschitz
constant $L\ge0$ for $\nabla\psi$ on $K$, at every $x\in K$ and every $0\le\tau\le1$ (the
whole inward segment from $x$ to $x_*$). `coordinateGradient ψ x` is $\nabla\psi(x)$. The Lean
proof bounds the derivative of the remainder along the segment by $L\tau\|r_x\|^2$ instead of
integrating. -/
theorem smooth_inward_remainder {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (xstar : Vec n) (hmin : ∀ x, F xstar ≤ F x)
    (U : Set (Vec n)) (hU : IsOpen U) (_hUc : Convex ℝ U)
    (ψ : Vec n → ℝ) (_hψ : ConvexOn ℝ U ψ) (hψ11 : CenteredSmoothSublinear.LocallyC11On U ψ)
    (γ : Vec n → ℝ) (_hγ : ConvexOn ℝ univ γ) (_hγh : Homogeneous.PositiveDegreeOne γ)
    (_hrep : ∀ x ∈ U, F x = ψ x + γ (x - xstar))
    (R : AdmissibleBFGSRun n F) (_hKc : IsCompact {x | F x ≤ F (R.x 0)})
    (hKU : {x | F x ≤ F (R.x 0)} ⊆ U)
    (K : Set (Vec n)) (hK_def : K = {x | F x ≤ F (R.x 0)})
    (L : ℝ) (_hL0 : 0 ≤ L)
    (hL : ∀ x ∈ K, ∀ y ∈ K,
      ‖euclideanVector (coordinateGradient ψ y - coordinateGradient ψ x)‖ ≤
        L * ‖euclideanVector (y - x)‖)
    (x : Vec n) (hx : x ∈ K) (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    |ψ (x - τ • (x - xstar)) - ψ x + τ * dot (coordinateGradient ψ x) (x - xstar)| ≤
      1 / 2 * L * τ ^ 2 * ‖euclideanVector (x - xstar)‖ ^ 2 := by
  have hKconv : Convex ℝ K := hK_def ▸ sublevel_convex hF _
  have hstarK : xstar ∈ K := by rw [hK_def]; exact hmin _
  set r := x - xstar with hr
  set c := dot (coordinateGradient ψ x) r with hc
  have hseg : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → x - s • r ∈ K := by
    intro s h0 h1
    have he : x - s • r = (1 - s) • x + s • xstar := by
      rw [hr]
      module
    rw [he]
    exact hKconv hx hstarK (by linarith) h0 (by ring)
  have hdiffU : ∀ p ∈ U, DifferentiableAt ℝ ψ p := fun p hp =>
    (hψ11.1 p hp).differentiableAt (hU.mem_nhds hp)
  have hder : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      HasDerivAt (fun s : ℝ => ψ (x - s • r) - ψ x + s * c)
        (-dot (coordinateGradient ψ (x - s • r)) r + c) s := by
    intro s h0 h1
    have hp : x - s • r ∈ U := hKU (hK_def ▸ hseg s h0 h1)
    have hψd := hasFDerivAt_coordinateGradient (hdiffU _ hp)
    have hpath : HasDerivAt (fun s : ℝ => x - s • r) (-r) s := by
      simpa using ((hasDerivAt_id s).smul_const r).const_sub x
    have hcomp := hψd.comp_hasDerivAt s hpath
    have hlin : HasDerivAt (fun s : ℝ => s * c) c s := by
      simpa using (hasDerivAt_id s).mul_const c
    have hall := (hcomp.sub_const (ψ x)).add hlin
    convert hall using 1
    rw [gradientFunctional_apply]
    change -(coordinateGradient ψ (x - s • r) ⬝ᵥ r) + c =
      coordinateGradient ψ (x - s • r) ⬝ᵥ (-r) + c
    rw [dotProduct_neg]
  have hbound : ∀ s ∈ Ico (0 : ℝ) τ,
      ‖-dot (coordinateGradient ψ (x - s • r)) r + c‖ ≤ L * s * ‖euclideanVector r‖ ^ 2 := by
    intro s hs
    have h0 := hs.1
    have h1 : s ≤ 1 := hs.2.le.trans hτ1
    have hlip := hL x hx (x - s • r) (hseg s h0 h1)
    have hnorm : ‖euclideanVector (x - s • r - x)‖ = s * ‖euclideanVector r‖ := by
      have he : x - s • r - x = (-s) • r := by module
      rw [he, norm_euclideanVector_smul, abs_neg, abs_of_nonneg h0]
    have hcs := abs_dot_le_norm_mul_norm
      (coordinateGradient ψ (x - s • r) - coordinateGradient ψ x) r
    have heq : -dot (coordinateGradient ψ (x - s • r)) r + c =
        -dot (coordinateGradient ψ (x - s • r) - coordinateGradient ψ x) r := by
      rw [dot_sub_left, hc]
      ring
    rw [Real.norm_eq_abs, heq, abs_neg]
    calc |dot (coordinateGradient ψ (x - s • r) - coordinateGradient ψ x) r|
        ≤ ‖euclideanVector (coordinateGradient ψ (x - s • r) - coordinateGradient ψ x)‖ *
            ‖euclideanVector r‖ := hcs
      _ ≤ L * ‖euclideanVector (x - s • r - x)‖ * ‖euclideanVector r‖ :=
          mul_le_mul_of_nonneg_right hlip (norm_nonneg _)
      _ = L * s * ‖euclideanVector r‖ ^ 2 := by rw [hnorm]; ring
  have hB : ∀ s : ℝ, HasDerivAt (fun s : ℝ => L / 2 * s ^ 2 * ‖euclideanVector r‖ ^ 2)
      (L * s * ‖euclideanVector r‖ ^ 2) s := by
    intro s
    have h := ((hasDerivAt_pow 2 s).const_mul (L / 2)).mul_const (‖euclideanVector r‖ ^ 2)
    convert h using 1
    push_cast
    ring
  have hfin := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := fun s : ℝ => ψ (x - s • r) - ψ x + s * c)
    (f' := fun s : ℝ => -dot (coordinateGradient ψ (x - s • r)) r + c)
    (B := fun s : ℝ => L / 2 * s ^ 2 * ‖euclideanVector r‖ ^ 2)
    (B' := fun s : ℝ => L * s * ‖euclideanVector r‖ ^ 2) (a := 0) (b := τ)
    (fun s hs => (hder s hs.1 (hs.2.trans hτ1)).continuousAt.continuousWithinAt)
    (fun s hs => (hder s hs.1 (hs.2.le.trans hτ1)).hasDerivWithinAt)
    (by simp) hB hbound ⟨hτ0, le_rfl⟩
  rw [Real.norm_eq_abs] at hfin
  calc |ψ (x - τ • r) - ψ x + τ * c| ≤ L / 2 * τ ^ 2 * ‖euclideanVector r‖ ^ 2 := hfin
    _ = 1 / 2 * L * τ ^ 2 * ‖euclideanVector r‖ ^ 2 := by ring

/-- Proof of Theorem `art:centered`, undisplayed claims of `paper/sections/global.tex:156-159`
(not a register item): "At a differentiable point of $F$ in $U$, the representation and
smoothness of $\psi$ imply differentiability of $\gamma$ at $r_x$. Differentiating its
homogeneity identity gives $\nabla\gamma(r_x)^Tr_x=\gamma(r_x)$. Its contribution to the inward
remainder is therefore exactly zero." With $g=\nabla F(x)$, $\nabla\gamma(r_x)=g-\nabla\psi(x)$. -/
theorem homogeneous_part_at_differentiable {n : ℕ} {F ψ γ : Vec n → ℝ} (xstar : Vec n)
    {U : Set (Vec n)} (hU : IsOpen U) (hψ11 : CenteredSmoothSublinear.LocallyC11On U ψ)
    (hγ : ConvexOn ℝ univ γ) (hγh : Homogeneous.PositiveDegreeOne γ)
    (hrep : ∀ x ∈ U, F x = ψ x + γ (x - xstar)) {x g : Vec n} (hx : x ∈ U)
    (hg : HasFDerivAt F (gradientFunctional g) x) :
    HasFDerivAt γ (gradientFunctional (g - coordinateGradient ψ x)) (x - xstar) ∧
      dot (g - coordinateGradient ψ x) (x - xstar) = γ (x - xstar) ∧
      ∀ τ : ℝ, τ ≤ 1 → γ ((x - xstar) - τ • (x - xstar)) - γ (x - xstar) +
        τ * dot (g - coordinateGradient ψ x) (x - xstar) = 0 := by
  have hψd := hasFDerivAt_coordinateGradient ((hψ11.1 x hx).differentiableAt (hU.mem_nhds hx))
  have hγd := CenteredSmoothSublinear.homogeneous_summand_derivative xstar hU hrep hx hg hψd
  exact ⟨hγd, Homogeneous.supporting_euler hγh (convex_supporting_inequality hγ hγd),
    fun τ hτ => homogeneous_inward_remainder_zero hγ hγh hγd τ hτ⟩

/-- Proof of Theorem `art:centered`, undisplayed claim of `paper/sections/global.tex:160-161`
(not a register item): "The upper bound in \eqref{art:inward-condition} follows with
$M=L\max_{x\in K}\|r_x\|^2$; its lower bound follows from convexity of $F$." Under the
hypotheses of the theorem, the inward condition holds on $K=\{F\le F(x_0)\}$ (with
$\theta=1/2$ for every band). -/
theorem centered_inward_condition {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (xstar : Vec n) (hmin : ∀ x, F xstar ≤ F x)
    (U : Set (Vec n)) (hU : IsOpen U) (hUc : Convex ℝ U)
    (ψ : Vec n → ℝ) (hψ : ConvexOn ℝ U ψ) (hψ11 : CenteredSmoothSublinear.LocallyC11On U ψ)
    (γ : Vec n → ℝ) (hγ : ConvexOn ℝ univ γ) (hγh : Homogeneous.PositiveDegreeOne γ)
    (hrep : ∀ x ∈ U, F x = ψ x + γ (x - xstar))
    (R : AdmissibleBFGSRun n F) (hKc : IsCompact {x | F x ≤ F (R.x 0)})
    (hKU : {x | F x ≤ F (R.x 0)} ⊆ U) :
    InwardModelCondition F xstar {x | F x ≤ F (R.x 0)} := by
  set K := {x | F x ≤ F (R.x 0)} with hK_def
  obtain ⟨L, hL0, hL⟩ := uniform_lipschitz_gradient hU hψ11 hKc hKU
  have hcont : Continuous (fun x : Vec n => ‖euclideanVector (x - xstar)‖ ^ 2) :=
    ((continuous_norm.comp ((PiLp.continuous_equiv_symm 2 _).comp
      (continuous_id.sub continuous_const))).pow 2)
  obtain ⟨xm, -, hxm⟩ := hKc.exists_isMaxOn ⟨R.x 0, le_refl (F (R.x 0))⟩ hcont.continuousOn
  set M := L * ‖euclideanVector (xm - xstar)‖ ^ 2 with hM
  have hKconv : Convex ℝ K := sublevel_convex hF _
  have hstarK : xstar ∈ K := hmin _
  intro η _
  refine ⟨M, 1 / 2, by positivity, by norm_num, le_rfl, ?_⟩
  intro x g hx hg _ τ hτ0 hτθ
  have hτ1 : τ ≤ 1 := by linarith
  have hin : x - τ • (x - xstar) ∈ K := by
    have he : x - τ • (x - xstar) = (1 - τ) • x + τ • xstar := by module
    rw [he]
    exact hKconv hx hstarK (by linarith) hτ0 (by ring)
  refine ⟨?_, ?_⟩
  · have hs := convex_supporting_inequality hF hg (x - τ • (x - xstar))
    have he : x - τ • (x - xstar) - x = (-τ) • (x - xstar) := by module
    rw [he, dot_smul_right] at hs
    linarith
  · obtain ⟨-, -, hzero⟩ := homogeneous_part_at_differentiable xstar hU hψ11 hγ hγh hrep (hKU hx) hg
    have hrem := smooth_inward_remainder hF xstar hmin U hU hUc ψ hψ hψ11 γ hγ hγh hrep R hKc hKU
      K hK_def L hL0 hL x hx τ hτ0 hτ1
    have hFin := hrep _ (hKU hin)
    have hFx := hrep x (hKU hx)
    have hγe : x - τ • (x - xstar) - xstar = (x - xstar) - τ • (x - xstar) := by abel
    rw [hγe] at hFin
    have hz := hzero τ hτ1
    have hsplit : dot g (x - xstar) =
        dot (coordinateGradient ψ x) (x - xstar) +
          dot (g - coordinateGradient ψ x) (x - xstar) := by
      rw [dot_sub_left]
      ring
    have hmax : ‖euclideanVector (x - xstar)‖ ^ 2 ≤ ‖euclideanVector (xm - xstar)‖ ^ 2 := hxm hx
    have hb : 1 / 2 * L * τ ^ 2 * ‖euclideanVector (x - xstar)‖ ^ 2 ≤ M / 2 * τ ^ 2 := by
      rw [hM]
      have := mul_le_mul_of_nonneg_left hmax (by positivity : (0 : ℝ) ≤ 1 / 2 * L * τ ^ 2)
      linarith
    rw [hFin, hFx, hsplit]
    have habs := (le_abs_self _).trans hrem
    nlinarith

/-- Item `A/global/theorem/art:centered`, Theorem `art:centered`
(`paper/sections/global.tex:130-142`), including its display `A/global/disp/008`
(lines 135-137). "Let $F:\R^n\to\R$ be finite and convex, and suppose $x_*$ minimizes $F$. Let
$U$ be an open convex set, let $\psi$ be convex and locally $C^{1,1}$ on $U$, and let
$\gamma:\R^n\to\R$ be finite, convex and positively homogeneous of degree one. Suppose
$F(x)=\psi(x)+\gamma(x-x_*)$ $(x\in U)$. Every admissible run whose initial sublevel is compact
and contained in $U$ satisfies $F(x_k)\to F(x_*)$. The distance to $\arg\min F$ also tends to
zero. If $x_*$ is the unique minimizer, then $x_k\to x_*$."

Locally $C^{1,1}$ on $U$ is the library's `LocallyC11On U ψ` ($\psi$ differentiable on $U$ with
locally Lipschitz derivative); positive homogeneity of degree one is
`Homogeneous.PositiveDegreeOne γ` ($\gamma(tx)=t\gamma(x)$ for $t\ge0$). The distance is the
Euclidean one. The last sentence of the theorem is `centered_summands_not_minimized`.

The proof is the paper's: `initial_value_gt`, `uniform_lipschitz_gradient`,
`smooth_inward_remainder` (display `A/global/disp/009`), `homogeneous_part_at_differentiable`
and `centered_inward_condition` give \eqref{art:inward-condition} on the initial sublevel, and
Corollary `art:radial-convergence` (`radial_convergence`) concludes. The library proves the
value and iterate statements by a different route (a cocoercivity bound on the secant
corrections) as `AdmissibleBFGSRun.centered_values` and `AdmissibleBFGSRun.centered_iterates`,
for open `U`. -/
theorem centered {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (xstar : Vec n) (hmin : ∀ x, F xstar ≤ F x)
    (U : Set (Vec n)) (hU : IsOpen U) (hUc : Convex ℝ U)
    (ψ : Vec n → ℝ) (hψ : ConvexOn ℝ U ψ) (hψ11 : CenteredSmoothSublinear.LocallyC11On U ψ)
    (γ : Vec n → ℝ) (hγ : ConvexOn ℝ univ γ) (hγh : Homogeneous.PositiveDegreeOne γ)
    (hrep : ∀ x ∈ U, F x = ψ x + γ (x - xstar))
    (R : AdmissibleBFGSRun n F) (hKc : IsCompact {x | F x ≤ F (R.x 0)})
    (hKU : {x | F x ≤ F (R.x 0)} ⊆ U) :
    Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) ∧
      Tendsto (fun k => euclideanSolutionDistance F (R.x k)) atTop (𝓝 0) ∧
      ((∀ y, (∀ x, F y ≤ F x) → y = xstar) → Tendsto R.x atTop (𝓝 xstar)) :=
  radial_convergence hF xstar hmin (F (R.x 0)) (initial_value_gt R xstar hmin) _ rfl hKc
    (Or.inr (centered_inward_condition hF xstar hmin U hU hUc ψ hψ hψ11 γ hγ hγh hrep R hKc hKU))
    R (le_refl (F (R.x 0)))

/-- Item `A/global/prose/024` (`paper/sections/global.tex:127-128`), "In particular, the two
summands need not separately be minimized at that center", and the last sentence of Theorem
`art:centered` (lines 140-141), "Neither original summand is required to be minimized at
$x_*$." An instance of all hypotheses of Theorem `art:centered` (with $U=\R$ and all sublevels
compact, so that every admissible run qualifies): $\psi(x)=x^2$, $\gamma(r)=r$, $x_*=-1/2$,
$F(x)=x^2+x+1/2$; neither $\psi$ nor $\gamma(\cdot-x_*)$ is minimized at $x_*$. -/
theorem centered_summands_not_minimized :
    ∃ (F ψ γ : Vec 1 → ℝ) (xstar : Vec 1),
      ConvexOn ℝ univ F ∧ (∀ x, F xstar ≤ F x) ∧
        ConvexOn ℝ univ ψ ∧ CenteredSmoothSublinear.LocallyC11On univ ψ ∧
        ConvexOn ℝ univ γ ∧ Homogeneous.PositiveDegreeOne γ ∧
        (∀ x, F x = ψ x + γ (x - xstar)) ∧ (∀ b : ℝ, IsCompact {x | F x ≤ b}) ∧
        (∃ y, ψ y < ψ xstar) ∧ (∃ y, γ (y - xstar) < γ (xstar - xstar)) := by
  set xstar : Vec 1 := fun _ => -1 / 2 with hxstar
  have hψ : ConvexOn ℝ univ (fun x : Vec 1 => (x 0) ^ 2) := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have he : (a * x 0 + b * y 0) ^ 2 + a * b * (x 0 - y 0) ^ 2 =
        (a + b) * (a * (x 0) ^ 2 + b * (y 0) ^ 2) := by ring
    rw [hab, one_mul] at he
    nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x 0 - y 0))]
  have hγ : ConvexOn ℝ univ (fun x : Vec 1 => x 0) := by
    refine ⟨convex_univ, fun x _ y _ a b _ _ _ => ?_⟩
    simp
  have hF : ConvexOn ℝ univ (fun x : Vec 1 => (x 0) ^ 2 + (x 0 + 1 / 2)) := by
    have hlin : ConvexOn ℝ univ (fun x : Vec 1 => x 0 + 1 / 2) := by
      refine ⟨convex_univ, fun x _ y _ a b _ _ hab => ?_⟩
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith
    exact hψ.add hlin
  have hmin : ∀ x : Vec 1, (xstar 0) ^ 2 + (xstar 0 + 1 / 2) ≤ (x 0) ^ 2 + (x 0 + 1 / 2) := by
    intro x
    simp only [hxstar]
    nlinarith [sq_nonneg (x 0 + 1 / 2)]
  have huniq : ∀ x : Vec 1, (x 0) ^ 2 + (x 0 + 1 / 2) = (xstar 0) ^ 2 + (xstar 0 + 1 / 2) →
      x = xstar := by
    intro x hx
    simp only [hxstar] at hx
    have h0 : x 0 = -1 / 2 := by nlinarith [sq_nonneg (x 0 + 1 / 2)]
    ext i
    fin_cases i
    simpa [hxstar] using h0
  refine ⟨fun x => (x 0) ^ 2 + (x 0 + 1 / 2), fun x => (x 0) ^ 2, fun x => x 0, xstar, hF, hmin,
    hψ, ConvexCellRadial.contDiffOn_two_locallyC11 isOpen_univ
      (by fun_prop : ContDiff ℝ 2 (fun x : Vec 1 => (x 0) ^ 2)).contDiffOn,
    hγ, fun t _ x => by simp, fun x => by simp [hxstar]; ring,
    fun b => Localization.sublevel_compact hF xstar hmin huniq b,
    ⟨0, by simp [hxstar]; norm_num⟩, ⟨fun _ => -1, by simp [hxstar]; norm_num⟩⟩

/-! ### Remarks on Theorem `art:centered` (lines 166-173) -/

/-- Item `A/global/prose/025` (`paper/sections/global.tex:166-167`): "The compact initial
sublevel supplies uniform constants and traps the accepted iterates." Armijo keeps every
iterate in $\{F\le F(x_0)\}$; the uniform constants are those of `uniform_lipschitz_gradient`
and `centered_inward_condition`. -/
theorem initial_sublevel_traps {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) :
    ∀ k, R.x k ∈ {x | F x ≤ F (R.x 0)} :=
  fun k => R.objective_le_initial k

/-- Item `A/global/prose/026` (`paper/sections/global.tex:167-169`): "When the representation
is global and all sublevels are compact, the theorem applies from every differentiable
nonstationary starting point, for every initial SPD matrix and every fixed valid
Armijo--weak-Wolfe pair." With $U=\R^n$ and compact sublevels, the conclusion of Theorem
`art:centered` holds for every admissible run (whose $x_0$, $H_0$, $c_1$, $c_2$ are
arbitrary). -/
theorem centered_global {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (xstar : Vec n) (hmin : ∀ x, F xstar ≤ F x)
    (ψ : Vec n → ℝ) (hψ : ConvexOn ℝ univ ψ) (hψ11 : CenteredSmoothSublinear.LocallyC11On univ ψ)
    (γ : Vec n → ℝ) (hγ : ConvexOn ℝ univ γ) (hγh : Homogeneous.PositiveDegreeOne γ)
    (hrep : ∀ x, F x = ψ x + γ (x - xstar)) (hsub : ∀ b : ℝ, IsCompact {x | F x ≤ b}) :
    ∀ R : AdmissibleBFGSRun n F,
      Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) ∧
        Tendsto (fun k => euclideanSolutionDistance F (R.x k)) atTop (𝓝 0) ∧
        ((∀ y, (∀ x, F y ≤ F x) → y = xstar) → Tendsto R.x atTop (𝓝 xstar)) :=
  fun R => centered hF xstar hmin univ isOpen_univ convex_univ ψ hψ hψ11 γ hγ hγh
    (fun x _ => hrep x) R (hsub _) (subset_univ _)

/-! ### Corollary `art:mixed-benchmark` -/

/-- Proof of Corollary `art:mixed-benchmark`, undisplayed claims of
`paper/sections/global.tex:183-185` (not a register item): "Take $\psi(u,v)=u^2$,
$\gamma(u,v)=|v|$, $x_*=(0,0)$ and $U=\R^2$. The objective is finite and convex, its sublevels
are closed and bounded, and its minimizer is unique." All hypotheses of Theorem `art:centered`
hold for these data. -/
theorem mixed_hypotheses (F : Vec 2 → ℝ) (hF_def : ∀ x, F x = (x 0) ^ 2 + |x 1|) :
    ConvexOn ℝ univ F ∧ (∀ x, F 0 ≤ F x) ∧ (∀ y, (∀ x, F y ≤ F x) → y = 0) ∧
      (∀ b : ℝ, IsCompact {x | F x ≤ b}) ∧
      ConvexOn ℝ univ (fun x : Vec 2 => (x 0) ^ 2) ∧
      CenteredSmoothSublinear.LocallyC11On univ (fun x : Vec 2 => (x 0) ^ 2) ∧
      ConvexOn ℝ univ (fun x : Vec 2 => |x 1|) ∧
      Homogeneous.PositiveDegreeOne (fun x : Vec 2 => |x 1|) ∧
      (∀ x, F x = (x 0) ^ 2 + |(x - 0) 1|) := by
  have hFeq : F = UnexcitedMetric.objective := funext hF_def
  have hconv : ConvexOn ℝ univ F := hFeq ▸ UnexcitedMetric.objective_convex
  have hF0 : F 0 = 0 := by simp [hF_def]
  have hmin : ∀ x, F 0 ≤ F x := fun x => by rw [hF0, hF_def]; positivity
  have hunique : ∀ y, F y = F 0 → y = 0 := fun y hy => by
    rw [hFeq] at hy
    exact UnexcitedMetric.unique_minimum hy
  have hψ : ConvexOn ℝ univ (fun x : Vec 2 => (x 0) ^ 2) := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have he : (a * x 0 + b * y 0) ^ 2 + a * b * (x 0 - y 0) ^ 2 =
        (a + b) * (a * (x 0) ^ 2 + b * (y 0) ^ 2) := by ring
    rw [hab, one_mul] at he
    nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x 0 - y 0))]
  have hψ11 : CenteredSmoothSublinear.LocallyC11On univ (fun x : Vec 2 => (x 0) ^ 2) :=
    ConvexCellRadial.contDiffOn_two_locallyC11 isOpen_univ (by fun_prop : ContDiff ℝ 2
      (fun x : Vec 2 => (x 0) ^ 2)).contDiffOn
  have hγ : ConvexOn ℝ univ (fun x : Vec 2 => |x 1|) := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb _ => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc |a * x 1 + b * y 1| ≤ |a * x 1| + |b * y 1| := abs_add_le _ _
      _ = a * |x 1| + b * |y 1| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  have hγh : Homogeneous.PositiveDegreeOne (fun x : Vec 2 => |x 1|) := by
    intro t ht x
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg ht]
  exact ⟨hconv, hmin, fun y hy => hunique y (le_antisymm (hy 0) (hmin y)),
    Localization.sublevel_compact hconv 0 hmin hunique, hψ, hψ11, hγ, hγh,
    fun x => by simp [hF_def]⟩

/-- Item `A/global/corollary/art:mixed-benchmark`, Corollary `art:mixed-benchmark`
(`paper/sections/global.tex:175-181`), including its display `A/global/disp/010`
(lines 178-180): "For $F(u,v)=u^2+|v|$, every infinite admissible full-BFGS run, with
arbitrary $H_0\succ0$ and any fixed $0<c_1<c_2<1$, satisfies
$F(u_k,v_k)\to0$, $(u_k,v_k)\to(0,0)$." Here $(u,v)$ is `x : Vec 2` with $u=x_0$, $v=x_1$;
$H_0$, $c_1$, $c_2$ are fields of the run.

The proof is the paper's: `mixed_hypotheses`, then Theorem `art:centered` with
$\psi(u,v)=u^2$, $\gamma(u,v)=|v|$, $x_*=(0,0)$, $U=\R^2$. The article supplement proves the
same statement through the inward condition as `ArticlePositive.mixed_benchmark_global`. -/
theorem mixed_benchmark (F : Vec 2 → ℝ) (hF_def : ∀ x, F x = (x 0) ^ 2 + |x 1|)
    (R : AdmissibleBFGSRun 2 F) :
    Tendsto (fun k => F (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0) := by
  obtain ⟨hconv, hmin, hunique, hK, hψ, hψ11, hγ, hγh, hrep⟩ := mixed_hypotheses F hF_def
  have hF0 : F 0 = 0 := by simp [hF_def]
  obtain ⟨hv, -, hi⟩ := centered hconv 0 hmin univ isOpen_univ convex_univ _ hψ hψ11 _ hγ hγh
    (fun x _ => hrep x) R (hK _) (subset_univ _)
  exact ⟨by rwa [hF0] at hv, hi hunique⟩

/-- Item `A/global/prose/027` (`paper/sections/global.tex:170-171`): "Neither a lower Hessian
bound for the smooth term nor differentiability of the full objective away from the minimizer
is required." The benchmark satisfies all hypotheses of Theorem `art:centered` with
$\psi(u,v)=u^2$, $\gamma(u,v)=|v|$, $x_*=0$, $U=\R^2$ (`mixed_hypotheses`), although $\psi$
has no positive lower Hessian bound (it is strongly convex for no modulus $m>0$) and $F$ is
not differentiable at any $(u,0)$, $u\ne0$ included. -/
theorem centered_weak_hypotheses (F : Vec 2 → ℝ) (hF_def : ∀ x, F x = (x 0) ^ 2 + |x 1|) :
    (ConvexOn ℝ univ F ∧ (∀ x, F 0 ≤ F x) ∧
      ConvexOn ℝ univ (fun x : Vec 2 => (x 0) ^ 2) ∧
      CenteredSmoothSublinear.LocallyC11On univ (fun x : Vec 2 => (x 0) ^ 2) ∧
      ConvexOn ℝ univ (fun x : Vec 2 => |x 1|) ∧
      Homogeneous.PositiveDegreeOne (fun x : Vec 2 => |x 1|) ∧
      (∀ x, F x = (x 0) ^ 2 + |(x - 0) 1|) ∧ (∀ b : ℝ, IsCompact {x | F x ≤ b})) ∧
      (∀ m : ℝ, 0 < m → ¬ StrongConvexOn univ m (fun x : Vec 2 => (x 0) ^ 2)) ∧
      ∀ u : ℝ, ¬ DifferentiableAt ℝ F ![u, 0] := by
  obtain ⟨hconv, hmin, -, hK, hψ, hψ11, hγ, hγh, hrep⟩ := mixed_hypotheses F hF_def
  refine ⟨⟨hconv, hmin, hψ, hψ11, hγ, hγh, hrep, hK⟩, fun m hm h => ?_,
    mixed_not_differentiable F hF_def⟩
  have hy : (![0, 1] : Vec 2) ≠ 0 := by
    intro h0
    have := congrFun h0 1
    simp at this
  have hpos : 0 < ‖(0 : Vec 2) - ![0, 1]‖ := by
    rw [zero_sub, norm_neg]
    exact norm_pos_iff.mpr hy
  have hc := h.2 (mem_univ (0 : Vec 2)) (mem_univ (![0, 1] : Vec 2))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Matrix.cons_val_zero,
    mul_zero, add_zero] at hc
  have : 0 < 1 / 2 * (1 / 2) * (m / 2 * ‖(0 : Vec 2) - ![0, 1]‖ ^ 2) := by positivity
  linarith

/-! ### Theorem `art:homogeneous` and its proof -/

/-- The Euclidean unit sphere of `Vec n` is compact, and nonempty when $n\ge1$. -/
theorem unit_sphere_compact {n : ℕ} : IsCompact {x : Vec n | ‖euclideanVector x‖ = 1} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_eq (continuous_norm.comp (PiLp.continuous_equiv_symm 2 _)) continuous_const
  · refine (Metric.isBounded_closedBall (x := (0 : Vec n)) (r := 1)).subset ?_
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_le_norm_euclideanVector x).trans (le_of_eq hx)

theorem unit_sphere_nonempty {n : ℕ} (hn : 1 ≤ n) :
    ({x : Vec n | ‖euclideanVector x‖ = 1}).Nonempty := by
  refine ⟨Pi.single ⟨0, hn⟩ 1, ?_⟩
  change ‖euclideanVector (Pi.single ⟨0, hn⟩ 1 : Vec n)‖ = 1
  rw [norm_euclideanVector]
  have hs : sqNorm (Pi.single ⟨0, hn⟩ (1 : ℝ) : Vec n) = 1 := by
    simp [sqNorm, Pi.single_apply]
  rw [hs, Real.sqrt_one]

/-- The sphere argument of `paper/sections/global.tex:213-217` and `:235-239`: a continuous
positively homogeneous function that is positive off zero attains a positive minimum $\mu$ on
the Euclidean unit sphere, and $F(x)\ge\mu\|x\|$. -/
theorem sphere_minimum {n : ℕ} (hn : 1 ≤ n) {F : Vec n → ℝ} (hc : Continuous F)
    (hhom : Homogeneous.PositiveDegreeOne F) (hpos : ∀ x, x ≠ 0 → 0 < F x) :
    (∃ μ, IsLeast (F '' {x | ‖euclideanVector x‖ = 1}) μ) ∧
      ∀ μ, IsLeast (F '' {x | ‖euclideanVector x‖ = 1}) μ →
        0 < μ ∧ ∀ x, μ * ‖euclideanVector x‖ ≤ F x := by
  have hne := unit_sphere_nonempty hn
  obtain ⟨x₀, hx₀, hmin₀⟩ := unit_sphere_compact.exists_isMinOn hne hc.continuousOn
  refine ⟨⟨F x₀, ⟨x₀, hx₀, rfl⟩, ?_⟩, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hmin₀ hx
  · rintro μ ⟨⟨x₁, hx₁, hx₁μ⟩, hlow⟩
    have hx₁0 : x₁ ≠ 0 := by
      rintro rfl
      have h1 : ‖euclideanVector (0 : Vec n)‖ = 1 := hx₁
      rw [norm_euclideanVector] at h1
      simp [sqNorm] at h1
    refine ⟨hx₁μ ▸ hpos x₁ hx₁0, fun x => ?_⟩
    by_cases hx : x = 0
    · subst hx
      rw [Homogeneous.value_zero hhom, norm_euclideanVector]
      simp [sqNorm]
    · have hnx : 0 < ‖euclideanVector x‖ := by
        rw [norm_euclideanVector]
        apply Real.sqrt_pos.mpr
        by_contra hle
        push_neg at hle
        apply hx
        ext i
        have hsum : sqNorm x = 0 := le_antisymm hle (sqNorm_nonneg x)
        have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (x j))).mp hsum i
          (Finset.mem_univ i)
        simpa using hi
      set u : Vec n := ‖euclideanVector x‖⁻¹ • x with hu
      have hu1 : ‖euclideanVector u‖ = 1 := by
        rw [hu, norm_euclideanVector_smul, abs_of_pos (inv_pos.mpr hnx), inv_mul_cancel₀ hnx.ne']
      have hxu : x = ‖euclideanVector x‖ • u := by
        rw [hu, smul_smul, mul_inv_cancel₀ hnx.ne', one_smul]
      have hFu : μ ≤ F u := hlow ⟨u, hu1, rfl⟩
      calc μ * ‖euclideanVector x‖ ≤ F u * ‖euclideanVector x‖ :=
            mul_le_mul_of_nonneg_right hFu hnx.le
        _ = F x := by
            conv_rhs => rw [hxu, hhom _ hnx.le u]
            ring

/-- Item `A/global/prose/031` (`paper/sections/global.tex:196-198`), first half: coercivity
"prevents escape along a direction of zero or negative homogeneous value"; also the proof of
Theorem `art:homogeneous`, undisplayed claims of lines 211-213 (not a register item):
"Homogeneity gives $F(0)=0$. If $F(x)\le0$ for some $x\ne0$, then $F(tx)=tF(x)\le0$ as
$t\to\infty$, contradicting coercivity. Thus $F(x)>0$ off zero." -/
theorem coercive_homogeneous_positive {n : ℕ} {F : Vec n → ℝ}
    (hhom : Homogeneous.PositiveDegreeOne F) (hcoer : Tendsto F (cocompact (Vec n)) atTop) :
    F 0 = 0 ∧ ∀ x, x ≠ 0 → 0 < F x :=
  ⟨Homogeneous.value_zero hhom, fun _ hx => Homogeneous.positive_of_bounded_zero_sublevel hhom
    (Homogeneous.bounded_zero_sublevel_of_coercive hcoer) hx⟩

/-- Item `A/global/disp/012` (`paper/sections/global.tex:214-217`), in the proof of Theorem
`art:homogeneous`: "Continuity on the unit sphere gives
\[ \mu=\min_{\|x\|=1}F(x)>0,\qquad F(x)\ge\mu\|x\|." \]
Stated under the hypotheses of the theorem: the minimum over the Euclidean unit sphere exists,
and the minimum $\mu$ is positive with $F(x)\ge\mu\|x\|$ for every $x$. -/
theorem homogeneous_sphere_bound {n : ℕ} (hn : 1 ≤ n) {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (hhom : Homogeneous.PositiveDegreeOne F)
    (hcoer : Tendsto F (cocompact (Vec n)) atTop) :
    (∃ μ, IsLeast (F '' {x | ‖euclideanVector x‖ = 1}) μ) ∧
      ∀ μ, IsLeast (F '' {x | ‖euclideanVector x‖ = 1}) μ →
        0 < μ ∧ ∀ x, μ * ‖euclideanVector x‖ ≤ F x :=
  sphere_minimum hn (convex_continuous hF) hhom (coercive_homogeneous_positive hhom hcoer).2

/-- Item `A/global/prose/040` (`paper/sections/global.tex:255`): "Coercivity supplies this
compact, whole-iterate route." Every sublevel of a continuous coercive function is compact
(also the proof of Theorem `art:homogeneous`, line 218: "All sublevels are compact"); the
whole-iterate conclusion is `homogeneous`. -/
theorem sublevels_compact_of_coercive {n : ℕ} {F : Vec n → ℝ} (hc : Continuous F)
    (hcoer : Tendsto F (cocompact (Vec n)) atTop) (b : ℝ) : IsCompact {x | F x ≤ b} := by
  have hev : {x | b < F x} ∈ cocompact (Vec n) := hcoer.eventually (eventually_gt_atTop b)
  obtain ⟨C, hC, hsub⟩ := mem_cocompact'.mp hev
  refine hC.of_isClosed_subset (isClosed_le hc continuous_const) (fun x hx => hsub ?_)
  simpa only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] using hx

/-- A lower bound $F(x)\ge\mu\|x\|$ with $\mu>0$ gives coercivity
(`paper/sections/global.tex:238-239`, "hence coercivity"). -/
theorem coercive_of_lower_bound {n : ℕ} {F : Vec n → ℝ} {μ : ℝ} (hμ : 0 < μ)
    (hlow : ∀ x, μ * ‖euclideanVector x‖ ≤ F x) : Tendsto F (cocompact (Vec n)) atTop := by
  refine tendsto_atTop_mono (fun x => ?_) (tendsto_norm_cocompact_atTop.const_mul_atTop hμ)
  exact (mul_le_mul_of_nonneg_left (norm_le_norm_euclideanVector x) hμ.le).trans (hlow x)

/-- Item `A/global/prose/031` (`paper/sections/global.tex:196-198`), second half: coercivity
"converts convergence in value into convergence to the origin". With $F(x)\ge\mu\|x\|$,
$\mu>0$ (display `A/global/disp/012`), $F(x_k)\to0$ gives $x_k\to0$; also the proof of
Theorem `art:homogeneous`, line 219-220: "the displayed lower bound gives convergence of the
iterates". -/
theorem iterates_of_values {n : ℕ} {F : Vec n → ℝ} {μ : ℝ} (hμ : 0 < μ)
    (hlow : ∀ x, μ * ‖euclideanVector x‖ ≤ F x) {x : ℕ → Vec n}
    (hv : Tendsto (fun k => F (x k)) atTop (𝓝 0)) : Tendsto x atTop (𝓝 0) := by
  apply squeeze_zero_norm (a := fun k => F (x k) / μ) (fun k => ?_)
  · simpa using hv.div_const μ
  · rw [le_div_iff₀ hμ, mul_comm]
    exact (mul_le_mul_of_nonneg_left (norm_le_norm_euclideanVector (x k)) hμ.le).trans (hlow _)

/-- Item `A/global/theorem/art:homogeneous`, Theorem `art:homogeneous`
(`paper/sections/global.tex:200-209`), including its display `A/global/disp/011`
(lines 204-206): "Let $F:\R^n\to\R$, $n\ge1$, be finite, convex, positively homogeneous of
degree one, and coercive. Then zero is its unique minimizer and every infinite admissible
full-BFGS run satisfies $F(x_k)\to0$, $x_k\to0$. The initial point, initial SPD matrix and
fixed valid line-search constants are arbitrary within admissibility." Coercive is
`Tendsto F (cocompact (Vec n)) atTop`; the run is arbitrary (`∀ R`), so are its fields.

The proof is the paper's: `coercive_homogeneous_positive`, `homogeneous_sphere_bound`
(display `A/global/disp/012`), `sublevels_compact_of_coercive`, then Theorem `art:centered`
(`centered`) with $\psi=0$, $\gamma=F$, $x_*=0$, $U=\R^n$, and `iterates_of_values`. The library
proves the iterate statement by the homogeneous potential as
`AdmissibleBFGSRun.homogeneous_coercive_iterates_zero`. -/
theorem homogeneous {n : ℕ} (hn : 1 ≤ n) {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (hhom : Homogeneous.PositiveDegreeOne F) (hcoer : Tendsto F (cocompact (Vec n)) atTop) :
    ((∀ x, F 0 ≤ F x) ∧ ∀ y, (∀ x, F y ≤ F x) → y = 0) ∧
      ∀ R : AdmissibleBFGSRun n F,
        Tendsto (fun k => F (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0) := by
  obtain ⟨h0, hpos⟩ := coercive_homogeneous_positive hhom hcoer
  obtain ⟨⟨μ, hμ⟩, hμprop⟩ := homogeneous_sphere_bound hn hF hhom hcoer
  obtain ⟨hμ0, hlow⟩ := hμprop μ hμ
  have hmin : ∀ x, F 0 ≤ F x := fun x => by
    by_cases hx : x = 0
    · rw [hx]
    · rw [h0]
      exact (hpos x hx).le
  have hunique : ∀ y, (∀ x, F y ≤ F x) → y = 0 := fun y hy => by
    by_contra hne
    have := hpos y hne
    have := hy 0
    linarith
  refine ⟨⟨hmin, hunique⟩, fun R => ?_⟩
  have hKc := sublevels_compact_of_coercive (convex_continuous hF) hcoer (F (R.x 0))
  have hψ11 : CenteredSmoothSublinear.LocallyC11On univ (fun _ : Vec n => (0 : ℝ)) :=
    ConvexCellRadial.contDiffOn_two_locallyC11 isOpen_univ contDiffOn_const
  obtain ⟨hv, -, -⟩ := centered hF 0 hmin univ isOpen_univ convex_univ (fun _ => 0)
    (convexOn_const 0 convex_univ) hψ11 F hF hhom (fun x _ => by simp) R hKc (subset_univ _)
  rw [h0] at hv
  exact ⟨hv, iterates_of_values hμ0 hlow hv⟩

/-- Item `A/global/prose/030` (`paper/sections/global.tex:195`), "Pure homogeneous geometry
is the limiting case with no smooth remainder", and the proof of Theorem `art:homogeneous`,
undisplayed claim of lines 220-221: "the inward remainder is identically zero". For finite
convex positively homogeneous $F$, centered at $x_*=0$, the inward remainder vanishes at every
differentiable point, so \eqref{art:inward-condition} holds with $M_\eta=0$ on every
sublevel. -/
theorem homogeneous_inward_condition {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (hhom : Homogeneous.PositiveDegreeOne F) (b : ℝ) :
    (∀ x g : Vec n, HasFDerivAt F (gradientFunctional g) x → ∀ τ : ℝ, τ ≤ 1 →
      F (x - τ • (x - 0)) - F x + τ * dot g (x - 0) = 0) ∧
      InwardModelCondition F 0 {x | F x ≤ b} := by
  have hzero : ∀ x g : Vec n, HasFDerivAt F (gradientFunctional g) x → ∀ τ : ℝ, τ ≤ 1 →
      F (x - τ • (x - 0)) - F x + τ * dot g (x - 0) = 0 := fun x g hg τ hτ => by
    simpa only [sub_zero] using homogeneous_inward_remainder_zero hF hhom hg τ hτ
  refine ⟨hzero, fun η _ => ⟨0, 1 / 2, le_rfl, by norm_num, le_rfl, ?_⟩⟩
  intro x g _ hg _ τ _ hτθ
  rw [hzero x g hg τ (by linarith)]
  simp

/-- Proof of Theorem `art:homogeneous`, last sentence (`paper/sections/global.tex:220-221`,
not a register item): "Equivalently, the inward remainder is identically zero, so the radial
convergence corollary applies directly." A second proof of the run conclusion, through
`homogeneous_inward_condition` and Corollary `art:radial-convergence`. -/
theorem homogeneous_via_radial {n : ℕ} (hn : 1 ≤ n) {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (hhom : Homogeneous.PositiveDegreeOne F) (hcoer : Tendsto F (cocompact (Vec n)) atTop)
    (R : AdmissibleBFGSRun n F) :
    Tendsto (fun k => F (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0) := by
  obtain ⟨⟨hmin, hunique⟩, -⟩ := homogeneous hn hF hhom hcoer
  have h0 : F 0 = 0 := Homogeneous.value_zero hhom
  obtain ⟨hv, -, hi⟩ := radial_convergence hF 0 hmin (F (R.x 0)) (initial_value_gt R 0 hmin) _
    rfl (sublevels_compact_of_coercive (convex_continuous hF) hcoer _)
    (Or.inr (homogeneous_inward_condition hF hhom _).2) R (le_refl (F (R.x 0)))
  rw [h0] at hv
  exact ⟨hv, hi hunique⟩

/-! ### Corollary `art:homogeneous-examples` and its proof -/

/-- Proof of Corollary `art:homogeneous-examples`, undisplayed claims of
`paper/sections/global.tex:235-240` (not a register item): positivity off zero and "the same
sphere argument gives $F(x)\ge\mu\|x\|$, hence coercivity". -/
theorem coercive_of_positive {n : ℕ} (hn : 1 ≤ n) {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (hhom : Homogeneous.PositiveDegreeOne F) (hpos : ∀ x, x ≠ 0 → 0 < F x) :
    Tendsto F (cocompact (Vec n)) atTop := by
  obtain ⟨⟨μ, hμ⟩, hprop⟩ := sphere_minimum hn (convex_continuous hF) hhom hpos
  obtain ⟨hμ0, hlow⟩ := hprop μ hμ
  exact coercive_of_lower_bound hμ0 hlow

/-- Item `A/global/corollary/art:homogeneous-examples`, Corollary `art:homogeneous-examples`
(`paper/sections/global.tex:224-233`), the norm case: "The conclusion of
Theorem~\ref{art:homogeneous} holds for every norm". A norm on $\R^n$ is a `Seminorm` that
vanishes only at zero. The conclusion is that of `homogeneous`: zero is the unique minimizer,
and every admissible run (from every admissible start) has $N(x_k)\to0$ and $x_k\to0$.
The other two cases are `homogeneous_examples_gauge` and `homogeneous_examples_maxLinear`. -/
theorem homogeneous_examples_norm {n : ℕ} (hn : 1 ≤ n) (N : Seminorm ℝ (Vec n))
    (hN : ∀ x, N x = 0 → x = 0) :
    ((∀ x, N 0 ≤ N x) ∧ ∀ y, (∀ x, N y ≤ N x) → y = 0) ∧
      ∀ R : AdmissibleBFGSRun n N,
        Tendsto (fun k => N (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0) := by
  have hF : ConvexOn ℝ univ (N : Vec n → ℝ) := N.convexOn
  have hhom : Homogeneous.PositiveDegreeOne (N : Vec n → ℝ) := by
    intro t ht x
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg ht]
  have hpos : ∀ x, x ≠ 0 → 0 < N x := fun x hx =>
    lt_of_le_of_ne (apply_nonneg N x) (fun h => hx (hN x h.symm))
  exact homogeneous hn hF hhom (coercive_of_positive hn hF hhom hpos)

/-- Item `A/global/corollary/art:homogeneous-examples` (`paper/sections/global.tex:224-233`),
the gauge case: "every finite convex degree-one gauge with bounded unit sublevel". -/
theorem homogeneous_examples_gauge {n : ℕ} (hn : 1 ≤ n) {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (hhom : Homogeneous.PositiveDegreeOne F)
    (hb : Bornology.IsBounded {x | F x ≤ 1}) :
    ((∀ x, F 0 ≤ F x) ∧ ∀ y, (∀ x, F y ≤ F x) → y = 0) ∧
      ∀ R : AdmissibleBFGSRun n F,
        Tendsto (fun k => F (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0) := by
  have hb0 : Bornology.IsBounded {x | F x ≤ 0} :=
    hb.subset (fun x (hx : F x ≤ 0) => (hx.trans zero_le_one : F x ≤ 1))
  have hpos : ∀ x, x ≠ 0 → 0 < F x := fun x hx =>
    Homogeneous.positive_of_bounded_zero_sublevel hhom hb0 hx
  exact homogeneous hn hF hhom (coercive_of_positive hn hF hhom hpos)

/-- Proof of Corollary `art:homogeneous-examples`, undisplayed claim of
`paper/sections/global.tex:239-240` (not a register item): "Finite maxima of linear forms are
finite, convex and degree-one homogeneous". -/
theorem maxLinear_convex_homogeneous {n m : ℕ} (a : Fin m → Vec n) (F : Vec n → ℝ)
    (hF_def : ∀ x, IsGreatest (Set.range fun i => dot (a i) x) (F x)) :
    ConvexOn ℝ univ F ∧ Homogeneous.PositiveDegreeOne F := by
  refine ⟨⟨convex_univ, fun x _ y _ s t hs ht _ => ?_⟩, fun t ht x => ?_⟩
  · obtain ⟨⟨j, hj⟩, -⟩ := hF_def (s • x + t • y)
    simp only at hj
    rw [← hj]
    have h1 : dot (a j) x ≤ F x := (hF_def x).2 ⟨j, rfl⟩
    have h2 : dot (a j) y ≤ F y := (hF_def y).2 ⟨j, rfl⟩
    have he : dot (a j) (s • x + t • y) = s * dot (a j) x + t * dot (a j) y := by
      change a j ⬝ᵥ (s • x + t • y) = s * (a j ⬝ᵥ x) + t * (a j ⬝ᵥ y)
      rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    rw [he]
    simp only [smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left h1 hs, mul_le_mul_of_nonneg_left h2 ht]
  · apply (hF_def (t • x)).unique
    obtain ⟨⟨j, hj⟩, hub⟩ := hF_def x
    refine ⟨⟨j, ?_⟩, ?_⟩
    · simp only [dot_smul_right, hj]
    · rintro _ ⟨i, rfl⟩
      simp only [dot_smul_right]
      exact mul_le_mul_of_nonneg_left (hub ⟨i, rfl⟩) ht

/-- Item `A/global/corollary/art:homogeneous-examples` (`paper/sections/global.tex:224-233`),
including its display `A/global/disp/013` (lines 228-230), the linear-maximum case: "every
finite linear maximum $F(x)=\max_{1\le i\le m}a_i^Tx$ whose zero sublevel is bounded". The
maximum is `IsGreatest` of the values $a_i^Tx$; there are no affine intercepts. -/
theorem homogeneous_examples_maxLinear {n m : ℕ} (hn : 1 ≤ n) (a : Fin m → Vec n)
    (F : Vec n → ℝ) (hF_def : ∀ x, IsGreatest (Set.range fun i => dot (a i) x) (F x))
    (hb : Bornology.IsBounded {x | F x ≤ 0}) :
    ((∀ x, F 0 ≤ F x) ∧ ∀ y, (∀ x, F y ≤ F x) → y = 0) ∧
      ∀ R : AdmissibleBFGSRun n F,
        Tendsto (fun k => F (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0) := by
  obtain ⟨hF, hhom⟩ := maxLinear_convex_homogeneous a F hF_def
  have hpos : ∀ x, x ≠ 0 → 0 < F x := fun x hx =>
    Homogeneous.positive_of_bounded_zero_sublevel hhom hb hx
  exact homogeneous hn hF hhom (coercive_of_positive hn hF hhom hpos)

/-! ### Explicit admissible runs on homogeneous objectives -/

/-- In dimension one a BFGS step with $H=h$ (a $1\times1$ matrix) is $s=-\alpha hg$. -/
theorem bfgsStep_one_dim (h g α : ℝ) :
    bfgsStep (Matrix.diagonal (fun _ : Fin 1 => h)) (OneDimensional.embed g) α =
      OneDimensional.embed (-(α * h * g)) := by
  ext i
  simp [bfgsStep, Matrix.mulVec_diagonal]
  ring

/-- In dimension one the inverse-BFGS update \eqref{art:update} is the secant ratio $s/y$. -/
theorem inverseBFGS_one_dim (h s y : ℝ) (hs : s ≠ 0) (hy : y ≠ 0) :
    inverseBFGS (Matrix.diagonal (fun _ : Fin 1 => h)) (OneDimensional.embed s)
      (OneDimensional.embed y) = Matrix.diagonal (fun _ : Fin 1 => s / y) := by
  ext i j
  fin_cases i
  fin_cases j
  simp [inverseBFGS, outer, dot, Matrix.mul_apply, Matrix.diagonal]
  field_simp
  ring

theorem dot_embed (a b : ℝ) :
    dot (OneDimensional.embed a) (OneDimensional.embed b) = a * b := by
  simp [dot]

/-- A one-dimensional admissible run built from scalar data: iterates `x k`, gradients `g k`,
inverse Hessian approximations `h k` (the $1\times1$ matrices $H_k$) and steps `a k`, with the
scalar forms of the conditions of Definition `art:admissible`. In dimension one the
inverse-BFGS update \eqref{art:update} is the secant ratio $h_{k+1}=s_k/y_k$
(`inverseBFGS_one_dim`). -/
def oneDimRun (F : Vec 1 → ℝ) (hconv : ConvexOn ℝ univ F) (x g h a : ℕ → ℝ) (c₁ c₂ : ℝ)
    (hc₁ : 0 < c₁) (hc : c₁ < c₂) (hc₂ : c₂ < 1) (hh0 : 0 < h 0) (ha : ∀ k, 0 < a k)
    (hg : ∀ k, g k ≠ 0)
    (hgrad : ∀ k, HasFDerivAt F (gradientFunctional (OneDimensional.embed (g k)))
      (OneDimensional.embed (x k)))
    (hstep : ∀ k, x (k + 1) = x k - a k * h k * g k)
    (hs : ∀ k, x (k + 1) ≠ x k) (hy : ∀ k, g (k + 1) ≠ g k)
    (hupd : ∀ k, h (k + 1) = (x (k + 1) - x k) / (g (k + 1) - g k))
    (harmijo : ∀ k, F (OneDimensional.embed (x (k + 1))) ≤
      F (OneDimensional.embed (x k)) + c₁ * (g k * (x (k + 1) - x k)))
    (hwolfe : ∀ k, c₂ * (g k * (x (k + 1) - x k)) ≤ g (k + 1) * (x (k + 1) - x k)) :
    AdmissibleBFGSRun 1 F where
  convex := hconv
  x k := OneDimensional.embed (x k)
  H k := Matrix.diagonal (fun _ => h k)
  g k := OneDimensional.embed (g k)
  α := a
  c₁ := c₁
  c₂ := c₂
  c₁_pos := hc₁
  c₁_lt_c₂ := hc
  c₂_lt_one := hc₂
  initial_posDef := Matrix.PosDef.diagonal (fun _ => hh0)
  alpha_pos := ha
  gradient_nonzero k := fun h0 => hg k (by simpa using congrFun h0 0)
  hasGradient := hgrad
  step k := by
    rw [bfgsStep_one_dim, ← map_add, hstep k, sub_eq_add_neg]
  update k := by
    have hsk : -(a k * h k * g k) = x (k + 1) - x k := by rw [hstep k]; ring
    rw [bfgsStep_one_dim, hsk, ← map_sub,
      inverseBFGS_one_dim _ _ _ (sub_ne_zero.mpr (hs k)) (sub_ne_zero.mpr (hy k)), hupd k]
  armijo k := by
    have hsk : -(a k * h k * g k) = x (k + 1) - x k := by rw [hstep k]; ring
    rw [bfgsStep_one_dim, hsk, dot_embed]
    exact harmijo k
  weak_wolfe k := by
    have hsk : -(a k * h k * g k) = x (k + 1) - x k := by rw [hstep k]; ring
    rw [bfgsStep_one_dim, hsk, dot_embed, dot_embed]
    exact hwolfe k

theorem neg_one_pow_cases (k : ℕ) :
    ((-1 : ℝ) ^ k = 1 ∧ (-1 : ℝ) ^ (k + 1) = -1) ∨
      ((-1 : ℝ) ^ k = -1 ∧ (-1 : ℝ) ^ (k + 1) = 1) := by
  rcases Nat.even_or_odd k with he | ho
  · exact Or.inl ⟨he.neg_one_pow, he.add_one.neg_one_pow⟩
  · exact Or.inr ⟨ho.neg_one_pow, ho.add_one.neg_one_pow⟩

theorem abs_coord_convex : ConvexOn ℝ univ (fun x : Vec 1 => |x 0|) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb _ => ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  calc |a * x 0 + b * y 0| ≤ |a * x 0| + |b * y 0| := abs_add_le _ _
    _ = a * |x 0| + b * |y 0| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]

/-- An explicit admissible run for $F(x)=|x|$ on $\R$ (any `F` with $F(x)=|x_0|$, so also for
the norms, the gauge and the linear maximum $\max(x,-x)$ that equal it): $x_k=(-1/2)^k$,
$g_k=(-1)^k$, $H_k=\tfrac32\,2^{-k}$, $\alpha_k=1$, $c_1=1/4$, $c_2=1/2$. Every step overshoots
the kink, $x_{k+1}=-x_k/2$; Armijo holds because $c_1\le1/3$. -/
def absRun (F : Vec 1 → ℝ) (hF : ∀ x, F x = |x 0|) : AdmissibleBFGSRun 1 F :=
  oneDimRun F (by rw [show F = fun x : Vec 1 => |x 0| from funext hF]; exact abs_coord_convex)
    (fun k => (-1) ^ k * (1 / 2) ^ k) (fun k => (-1) ^ k) (fun k => 3 / 2 * (1 / 2) ^ k)
    (fun _ => 1) (1 / 4) (1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun _ => one_pos) (fun k => pow_ne_zero k (by norm_num))
    (fun k => by
      rw [show F = fun x : Vec 1 => |x 0| from funext hF]
      have hp : 0 < ((1 : ℝ) / 2) ^ k := by positivity
      rcases neg_one_pow_cases k with ⟨h1, -⟩ | ⟨h1, -⟩
      · simp only [h1, one_mul]
        exact ScalarCounterexamples.coordinate_hasGradient (f := fun t => |t|)
          (hasDerivAt_abs_pos hp)
      · simp only [h1, neg_one_mul]
        exact ScalarCounterexamples.coordinate_hasGradient (f := fun t => |t|)
          (hasDerivAt_abs_neg (by linarith)))
    (fun k => by ring)
    (fun k => by
      have hp : 0 < ((1 : ℝ) / 2) ^ k := by positivity
      rcases neg_one_pow_cases k with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        simp only [h1, h2, pow_succ] <;> intro h <;> nlinarith)
    (fun k => by
      rcases neg_one_pow_cases k with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp only [h1, h2] <;> norm_num)
    (fun k => by
      rcases neg_one_pow_cases k with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp only [h1, h2, pow_succ] <;>
        ring)
    (fun k => by
      rw [hF, hF]
      have hp : 0 < ((1 : ℝ) / 2) ^ k := by positivity
      simp only [OneDimensional.embed_apply]
      rcases neg_one_pow_cases k with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp only [h1, h2, pow_succ] <;>
        simp only [max_def, abs_eq_max_neg] <;> split_ifs <;> nlinarith)
    (fun k => by
      have hp : 0 < ((1 : ℝ) / 2) ^ k := by positivity
      rcases neg_one_pow_cases k with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp only [h1, h2, pow_succ] <;>
        nlinarith)

theorem maxAsym_convex : ConvexOn ℝ univ (fun x : Vec 1 => max (x 0) (-2 * x 0)) := by
  have h1 : ConvexOn ℝ univ (fun x : Vec 1 => x 0) := by
    refine ⟨convex_univ, fun x _ y _ a b _ _ _ => ?_⟩
    simp
  have h2 : ConvexOn ℝ univ (fun x : Vec 1 => -2 * x 0) := by
    refine ⟨convex_univ, fun x _ y _ a b _ _ _ => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith
  exact h1.sup h2

theorem maxAsym_hasDerivAt_pos {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => max s (-2 * s)) 1 t := by
  apply (hasDerivAt_id t).congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds ht] with s hs
  exact max_eq_left (by linarith)

theorem maxAsym_hasDerivAt_neg {t : ℝ} (ht : t < 0) :
    HasDerivAt (fun s : ℝ => max s (-2 * s)) (-2) t := by
  have h := (hasDerivAt_id t).const_mul (-2)
  simp only [mul_one] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [gt_mem_nhds ht] with s hs
  exact max_eq_right (by linarith)

/-- An explicit admissible run for the asymmetric $F(x)=\max(x,-2x)$ on $\R$: $x_k=(-1/4)^k$,
$H_k=\tfrac53\,4^{-k}$, $g_k=1$ and $\alpha_k=3/4$ for even $k$, $g_k=-2$ and $\alpha_k=3/8$ for
odd $k$ (written with $(-1)^k$), $c_1=1/4$, $c_2=1/2$. -/
def asymRun (F : Vec 1 → ℝ) (hF : ∀ x, F x = max (x 0) (-2 * x 0)) : AdmissibleBFGSRun 1 F :=
  oneDimRun F
    (by rw [show F = fun x : Vec 1 => max (x 0) (-2 * x 0) from funext hF]; exact maxAsym_convex)
    (fun k => (-1) ^ k * (1 / 4) ^ k) (fun k => (3 * (-1) ^ k - 1) / 2)
    (fun k => 5 / 3 * (1 / 4) ^ k) (fun k => (9 + 3 * (-1) ^ k) / 16) (1 / 4) (1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun k => by
      rcases neg_one_pow_cases k with ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp only [h1] <;> norm_num)
    (fun k => by
      rcases neg_one_pow_cases k with ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp only [h1] <;> norm_num)
    (fun k => by
      rw [show F = fun x : Vec 1 => max (x 0) (-2 * x 0) from funext hF]
      have hp : 0 < ((1 : ℝ) / 4) ^ k := by positivity
      rcases neg_one_pow_cases k with ⟨h1, -⟩ | ⟨h1, -⟩
      · simp only [h1, one_mul, show (3 * (1 : ℝ) - 1) / 2 = 1 by norm_num]
        exact ScalarCounterexamples.coordinate_hasGradient (f := fun t => max t (-2 * t))
          (maxAsym_hasDerivAt_pos hp)
      · simp only [h1, neg_one_mul, show (3 * (-1 : ℝ) - 1) / 2 = -2 by norm_num]
        exact ScalarCounterexamples.coordinate_hasGradient (f := fun t => max t (-2 * t))
          (maxAsym_hasDerivAt_neg (by linarith)))
    (fun k => by
      rcases neg_one_pow_cases k with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp only [h1, h2, pow_succ] <;>
        ring)
    (fun k => by
      have hp : 0 < ((1 : ℝ) / 4) ^ k := by positivity
      rcases neg_one_pow_cases k with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        simp only [h1, h2, pow_succ] <;> intro h <;> nlinarith)
    (fun k => by
      rcases neg_one_pow_cases k with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp only [h1, h2] <;> norm_num)
    (fun k => by
      rcases neg_one_pow_cases k with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp only [h1, h2, pow_succ] <;>
        ring)
    (fun k => by
      rw [hF, hF]
      have hp : 0 < ((1 : ℝ) / 4) ^ k := by positivity
      simp only [OneDimensional.embed_apply]
      rcases neg_one_pow_cases k with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp only [h1, h2, pow_succ] <;>
        simp only [max_def] <;> split_ifs <;> nlinarith)
    (fun k => by
      have hp : 0 < ((1 : ℝ) / 4) ^ k := by positivity
      rcases neg_one_pow_cases k with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp only [h1, h2, pow_succ] <;>
        nlinarith)

/-! ### Remarks on the examples (lines 243-258) -/

/-- The $\ell^1$ norm $\|x\|_1=\sum_i|x_i|$ as a `Seminorm` on `Vec n`. -/
def l1Seminorm (n : ℕ) : Seminorm ℝ (Vec n) :=
  Seminorm.of (fun x => ∑ i, |x i|)
    (fun x y => by
      simp only [Pi.add_apply, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum (fun i _ => abs_add_le _ _))
    (fun c x => by
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul, Real.norm_eq_abs, Finset.mul_sum])

/-- The sup norm of `Vec n` is $\max_i|x_i|$: if $F(x)$ is the maximum of the $|x_i|$, then
$F(x)=\|x\|$. -/
theorem linf_eq_norm {n : ℕ} (F : Vec n → ℝ)
    (hF_def : ∀ x, IsGreatest (Set.range fun i => |x i|) (F x)) (x : Vec n) : F x = ‖x‖ := by
  obtain ⟨⟨j, hj⟩, hub⟩ := hF_def x
  simp only at hj
  have hF0 : 0 ≤ F x := hj ▸ abs_nonneg _
  apply le_antisymm
  · rw [← hj]
    simpa [Real.norm_eq_abs] using norm_le_pi_norm x j
  · exact (pi_norm_le_iff_of_nonneg hF0).mpr (fun i => by rw [Real.norm_eq_abs]; exact hub ⟨i, rfl⟩)

/-- Item `A/global/prose/033` (`paper/sections/global.tex:243-244`): "The norm cases include
$\|x\|_1=\sum_i|x_i|$ and $\|x\|_\infty=\max_i|x_i|$." The conclusion of Theorem
`art:homogeneous` for $\|\cdot\|_1$ (`linf_norm_case` is the case $\|\cdot\|_\infty$), derived
from the norm case `homogeneous_examples_norm` of the corollary. -/
theorem l1_norm_case {n : ℕ} (hn : 1 ≤ n) (F : Vec n → ℝ) (hF_def : ∀ x, F x = ∑ i, |x i|) :
    ((∀ x, F 0 ≤ F x) ∧ ∀ y, (∀ x, F y ≤ F x) → y = 0) ∧
      ∀ R : AdmissibleBFGSRun n F,
        Tendsto (fun k => F (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0) := by
  obtain rfl : F = (l1Seminorm n : Vec n → ℝ) := funext fun x => hF_def x
  apply homogeneous_examples_norm hn
  intro x hx
  have hx' : ∑ i, |x i| = 0 := hx
  ext i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => abs_nonneg (x j))).mp hx' i
    (Finset.mem_univ i)
  simpa using hi

/-- Item `A/global/prose/033` (`paper/sections/global.tex:243-244`), the case
$\|x\|_\infty=\max_i|x_i|$ (the maximum is `IsGreatest` of the $|x_i|$; it is the sup norm of
`Vec n`, `linf_eq_norm`), derived from `homogeneous_examples_norm`. -/
theorem linf_norm_case {n : ℕ} (hn : 1 ≤ n) (F : Vec n → ℝ)
    (hF_def : ∀ x, IsGreatest (Set.range fun i => |x i|) (F x)) :
    ((∀ x, F 0 ≤ F x) ∧ ∀ y, (∀ x, F y ≤ F x) → y = 0) ∧
      ∀ R : AdmissibleBFGSRun n F,
        Tendsto (fun k => F (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0) := by
  obtain rfl : F = (normSeminorm ℝ (Vec n) : Vec n → ℝ) :=
    funext fun x => (linf_eq_norm F hF_def x).trans (coe_normSeminorm ℝ (Vec n) ▸ rfl)
  exact homogeneous_examples_norm hn (normSeminorm ℝ (Vec n)) (fun x hx => norm_eq_zero.mp hx)

/-- Item `A/global/prose/034` (`paper/sections/global.tex:244-247`), the $\ell^1$ part: "In
dimension at least two their nonsmoothness is nonisolated: the first has gradient jumps across
coordinate hyperplanes". On the hyperplane $\{x_i=0\}$: along the normal direction $e_i$ the
norm is $\|x\|_1+|t|$ (the partial derivative jumps from $-1$ to $1$), the norm is not
differentiable there, and for $n\ge2$ no point of the hyperplane is isolated. -/
theorem l1_nonsmooth {n : ℕ} (F : Vec n → ℝ) (hF_def : ∀ x, F x = ∑ i, |x i|) (i : Fin n) :
    (∀ x : Vec n, x i = 0 → ∀ t : ℝ, F (x + t • (Pi.single i 1 : Vec n)) = F x + |t|) ∧
      (∀ x : Vec n, x i = 0 → ¬ DifferentiableAt ℝ F x) ∧
      (2 ≤ n → ∀ x : Vec n, x i = 0 → ∀ ε : ℝ, 0 < ε →
        ∃ y : Vec n, y i = 0 ∧ y ≠ x ∧ ‖y - x‖ < ε) := by
  have hline : ∀ x : Vec n, x i = 0 → ∀ t : ℝ, F (x + t • (Pi.single i 1 : Vec n)) = F x + |t| := by
    intro x hx t
    rw [hF_def, hF_def]
    have h : ∀ k, |(x + t • (Pi.single i 1 : Vec n)) k| = |x k| + if k = i then |t| else 0 := by
      intro k
      by_cases hk : k = i
      · subst hk
        simp [hx]
      · simp [Pi.single_apply, hk]
    simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine ⟨hline, fun x hx hd => ?_, fun hn x hx ε hε => ?_⟩
  · have hl : DifferentiableAt ℝ (fun t : ℝ => x + t • (Pi.single i 1 : Vec n)) 0 :=
      (differentiableAt_const _).add (differentiableAt_id.smul_const _)
    have hd' : DifferentiableAt ℝ F (x + (0 : ℝ) • (Pi.single i 1 : Vec n)) := by simpa using hd
    have hc := (hd'.comp (0 : ℝ) hl).sub_const (F x)
    have hfun : (fun t : ℝ => (F ∘ fun t : ℝ => x + t • (Pi.single i 1 : Vec n)) t - F x) =
        fun t : ℝ => |t| := by
      funext t
      simp only [Function.comp_apply, hline x hx t]
      ring
    rw [hfun] at hc
    exact not_differentiableAt_abs_zero hc
  · obtain ⟨j, hj⟩ : ∃ j : Fin n, j ≠ i := by
      by_cases h0 : (i : ℕ) = 0
      · exact ⟨⟨1, by omega⟩, fun h => by rw [Fin.ext_iff] at h; simp at h; omega⟩
      · exact ⟨⟨0, by omega⟩, fun h => by rw [Fin.ext_iff] at h; simp at h; omega⟩
    refine ⟨x + (ε / 2) • (Pi.single j 1 : Vec n), ?_, ?_, ?_⟩
    · simp [Pi.single_apply, Ne.symm hj, hx]
    · intro h
      have h' := congrFun h j
      simp at h'
      linarith
    · rw [add_sub_cancel_left, norm_smul, Pi.norm_single, norm_one, mul_one, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      linarith

/-- Item `A/global/prose/034` (`paper/sections/global.tex:244-247`), the $\ell^\infty$ part:
"the second has them where two nonzero coordinate magnitudes tie for the maximum". At $x$
with $|x_i|=|x_j|=\max_k|x_k|>0$, $i\ne j$, the norm $\|\cdot\|_\infty$ is not differentiable
(along $\operatorname{sign}(x_i)e_i$ it equals $\|x\|_\infty+\max(s,0)$), and such tie points
are not isolated (they form a cone). -/
theorem linf_nonsmooth {n : ℕ} (F : Vec n → ℝ)
    (hF_def : ∀ x, IsGreatest (Set.range fun i => |x i|) (F x))
    (x : Vec n) (i j : Fin n) (hij : i ≠ j) (hxi : x i ≠ 0) (htie : |x i| = |x j|)
    (hmax : ∀ k, |x k| ≤ |x i|) :
    ¬ DifferentiableAt ℝ F x ∧
      ∀ ε : ℝ, 0 < ε → ∃ y : Vec n, y ≠ x ∧ ‖y - x‖ < ε ∧
        y i ≠ 0 ∧ |y i| = |y j| ∧ ∀ k, |y k| ≤ |y i| := by
  have hFn : F = fun y => ‖y‖ := funext (linf_eq_norm F hF_def)
  subst hFn
  set M := |x i| with hM
  have hMpos : 0 < M := abs_pos.mpr hxi
  set σ := x i / M with hσ
  have hσabs : |σ| = 1 := by rw [hσ, abs_div, abs_abs, div_self hMpos.ne']
  have hxiσ : x i = σ * M := by rw [hσ, div_mul_cancel₀ _ hMpos.ne']
  have hpath : ∀ s : ℝ, -M < s → ‖x + (s * σ) • (Pi.single i 1 : Vec n)‖ = M + max s 0 := by
    intro s hs
    have hpi : |(x + (s * σ) • (Pi.single i 1 : Vec n)) i| = M + s := by
      simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
      rw [hxiσ, show σ * M + s * σ = σ * (M + s) by ring, abs_mul, hσabs, one_mul,
        abs_of_pos (by linarith)]
    have hpk : ∀ k, k ≠ i → (x + (s * σ) • (Pi.single i 1 : Vec n)) k = x k := by
      intro k hk
      simp [Pi.single_apply, hk]
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (by linarith [le_max_right s 0])).mpr
      intro k
      rw [Real.norm_eq_abs]
      by_cases hk : k = i
      · subst hk
        rw [hpi]
        linarith [le_max_left s 0]
      · rw [hpk k hk]
        linarith [hmax k, le_max_right s 0]
    · have h1 := norm_le_pi_norm (x + (s * σ) • (Pi.single i 1 : Vec n)) i
      have h2 := norm_le_pi_norm (x + (s * σ) • (Pi.single i 1 : Vec n)) j
      rw [Real.norm_eq_abs, hpi] at h1
      rw [Real.norm_eq_abs, hpk j (Ne.symm hij), ← htie] at h2
      rcases le_total s 0 with hs0 | hs0
      · rw [max_eq_right hs0]
        linarith
      · rw [max_eq_left hs0]
        linarith
  refine ⟨fun hd => ?_, fun ε hε => ?_⟩
  · have hl : DifferentiableAt ℝ (fun s : ℝ => x + (s * σ) • (Pi.single i 1 : Vec n)) 0 :=
      (differentiableAt_const _).add ((differentiableAt_id.mul_const σ).smul_const _)
    have hd' : DifferentiableAt ℝ (fun y : Vec n => ‖y‖)
        (x + ((0 : ℝ) * σ) • (Pi.single i 1 : Vec n)) := by simpa using hd
    have hc := hd'.comp (0 : ℝ) hl
    have hev : (fun s : ℝ => M + max s 0) =ᶠ[𝓝 0]
        ((fun y : Vec n => ‖y‖) ∘ fun s : ℝ => x + (s * σ) • (Pi.single i 1 : Vec n)) := by
      filter_upwards [eventually_gt_nhds (by linarith : -M < 0)] with s hs
      exact (hpath s hs).symm
    have hmaxd : DifferentiableAt ℝ (fun s : ℝ => M + max s 0) 0 := hc.congr_of_eventuallyEq hev
    have habs : DifferentiableAt ℝ (fun s : ℝ => |s|) 0 := by
      have h2 := ((hmaxd.sub_const M).const_mul 2).sub differentiableAt_id
      convert h2 using 1
      funext s
      simp only [id]
      rcases le_total s 0 with h | h
      · rw [max_eq_right h, abs_of_nonpos h]
        ring
      · rw [max_eq_left h, abs_of_nonneg h]
        ring
    exact not_differentiableAt_abs_zero habs
  · have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr (fun h => hxi (by rw [h]; rfl))
    set δ := ε / (2 * ‖x‖) with hδ
    have hδpos : 0 < δ := by positivity
    refine ⟨(1 + δ) • x, ?_, ?_, ?_, ?_, ?_⟩
    · intro h
      have h' := congrFun h i
      simp only [Pi.smul_apply, smul_eq_mul] at h'
      have : δ * x i = 0 := by linarith
      rcases mul_eq_zero.mp this with h0 | h0
      · linarith
      · exact hxi h0
    · have he : (1 + δ) • x - x = δ • x := by module
      have hx0' : ‖x‖ ≠ 0 := hx0.ne'
      have hδx : δ * ‖x‖ = ε / 2 := by
        rw [hδ]
        field_simp
        ring
      rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hδpos, hδx]
      linarith
    · simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_ne_zero (by linarith) hxi
    · simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
      rw [← hM, htie]
    · intro k
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (hmax k) (abs_nonneg _)

/-- Item `A/global/prose/035` (`paper/sections/global.tex:247-248`): "For example, along
$(t,t,0,\ldots,0)$ with $t>0$, the two active coordinate forms of $\|\cdot\|_\infty$ have
distinct gradients." With $i_0,i_1$ the first two coordinates: the forms $y\mapsto y_{i_0}$ and
$y\mapsto y_{i_1}$ both equal $\|x\|_\infty$ at $x$, their gradients are $e_{i_0}\ne e_{i_1}$,
and $\|\cdot\|_\infty$ is not differentiable at $x$. -/
theorem linf_tie_example {n : ℕ} (F : Vec n → ℝ)
    (hF_def : ∀ x, IsGreatest (Set.range fun i => |x i|) (F x))
    (i0 i1 : Fin n) (hi0 : (i0 : ℕ) = 0) (hi1 : (i1 : ℕ) = 1) {t : ℝ} (ht : 0 < t)
    (x : Vec n) (hx : x = Pi.single i0 t + Pi.single i1 t) :
    x i0 = F x ∧ x i1 = F x ∧
      HasFDerivAt (fun y : Vec n => y i0) (gradientFunctional (Pi.single i0 1)) x ∧
      HasFDerivAt (fun y : Vec n => y i1) (gradientFunctional (Pi.single i1 1)) x ∧
      (Pi.single i0 1 : Vec n) ≠ Pi.single i1 1 ∧ ¬ DifferentiableAt ℝ F x := by
  have h01 : i0 ≠ i1 := fun h => by rw [Fin.ext_iff, hi0, hi1] at h; exact zero_ne_one h
  have hx0 : x i0 = t := by simp [hx, Pi.single_apply, h01]
  have hx1 : x i1 = t := by simp [hx, Pi.single_apply, Ne.symm h01]
  have hxk : ∀ k, |x k| ≤ t := by
    intro k
    rw [hx]
    by_cases hk0 : k = i0
    · subst hk0
      simp [Pi.single_apply, h01, abs_of_pos ht]
    · by_cases hk1 : k = i1
      · subst hk1
        simp [Pi.single_apply, Ne.symm h01, abs_of_pos ht]
      · simp [Pi.single_apply, hk0, hk1, ht.le]
  have hFx : F x = t := by
    rw [linf_eq_norm F hF_def x]
    apply le_antisymm
    · exact (pi_norm_le_iff_of_nonneg ht.le).mpr (fun k => by rw [Real.norm_eq_abs]; exact hxk k)
    · have := norm_le_pi_norm x i0
      rwa [Real.norm_eq_abs, hx0, abs_of_pos ht] at this
  have hproj (i : Fin n) :
      HasFDerivAt (fun y : Vec n => y i) (gradientFunctional (Pi.single i 1)) x := by
    have h := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).hasFDerivAt (x := x)
    convert h using 1
    ext v
    simp [gradientFunctional_apply, dot, Pi.single_apply]
  refine ⟨hx0.trans hFx.symm, hx1.trans hFx.symm, hproj i0, hproj i1, ?_, ?_⟩
  · intro h
    have h' := congrFun h i0
    simp [Pi.single_apply, h01] at h'
  · exact (linf_nonsmooth F hF_def x i0 i1 h01 (by rw [hx0]; exact ht.ne')
      (by rw [hx0, hx1]) (fun k => by rw [hx0, abs_of_pos ht]; exact hxk k)).1

/-- The Euclidean norm $\|x\|=\sqrt{\sum_ix_i^2}$ as a `Seminorm` on `Vec n`. -/
def euclideanSeminorm (n : ℕ) : Seminorm ℝ (Vec n) :=
  Seminorm.of (fun x => ‖euclideanVector x‖)
    (fun x y => by
      simp only [euclideanVector, WithLp.equiv_symm_add]
      exact norm_add_le _ _)
    (fun c x => by
      simp only [euclideanVector, WithLp.equiv_symm_smul]
      exact norm_smul c _)

/-- Item `A/global/prose/037` (`paper/sections/global.tex:250-252`): "The familiar Euclidean
norm is an already established consequence of Guo--Lewis's smooth-extension analysis
\cite[Corollary~4.2]{GL18}". The mathematical content, the conclusion of Theorem
`art:homogeneous` for $F(x)=\sqrt{\sum_ix_i^2}$, as an instance of the norm case
`homogeneous_examples_norm`; the attribution to [GL18] is not checked. -/
theorem euclidean_norm_case {n : ℕ} (hn : 1 ≤ n) (F : Vec n → ℝ)
    (hF_def : ∀ x, F x = Real.sqrt (∑ i, (x i) ^ 2)) :
    ((∀ x, F 0 ≤ F x) ∧ ∀ y, (∀ x, F y ≤ F x) → y = 0) ∧
      ∀ R : AdmissibleBFGSRun n F,
        Tendsto (fun k => F (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0) := by
  obtain rfl : F = (euclideanSeminorm n : Vec n → ℝ) :=
    funext fun x => (hF_def x).trans (norm_euclideanVector x).symm
  apply homogeneous_examples_norm hn
  intro x hx
  have hx' : ‖euclideanVector x‖ = 0 := hx
  rw [norm_eq_zero] at hx'
  simpa [euclideanVector] using hx'

/-- Item `A/global/prose/039` (`paper/sections/global.tex:254-255`): "No symmetry is needed
for the gauge or max-linear cases." The finite linear maximum $F(x)=\max(x,-2x)$ on $\R$ has
bounded zero and unit sublevels and is a finite convex degree-one gauge, but
$F(-1)=2\ne1=F(1)$; the conclusion of Theorem `art:homogeneous` holds for it, and admissible
runs on it exist (`asymRun`), so that conclusion is not vacuous. -/
theorem asymmetric_example :
    ∃ (a : Fin 2 → Vec 1) (F : Vec 1 → ℝ),
      (∀ x, IsGreatest (Set.range fun i => dot (a i) x) (F x)) ∧
        Bornology.IsBounded {x | F x ≤ 0} ∧
        ConvexOn ℝ univ F ∧ Homogeneous.PositiveDegreeOne F ∧
        Bornology.IsBounded {x | F x ≤ 1} ∧ (∃ x, F (-x) ≠ F x) ∧
        ((∀ x, F 0 ≤ F x) ∧ ∀ y, (∀ x, F y ≤ F x) → y = 0) ∧
        (∀ R : AdmissibleBFGSRun 1 F,
          Tendsto (fun k => F (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0)) ∧
        Nonempty (AdmissibleBFGSRun 1 F) := by
  set a : Fin 2 → Vec 1 := ![fun _ => 1, fun _ => -2] with ha
  set F : Vec 1 → ℝ := fun x => max (x 0) (-2 * x 0) with hF
  have h0 : ∀ x : Vec 1, dot (a 0) x = x 0 := fun x => by simp [ha, dot]
  have h1 : ∀ x : Vec 1, dot (a 1) x = -2 * x 0 := fun x => by simp [ha, dot]
  have hgr : ∀ x, IsGreatest (Set.range fun i => dot (a i) x) (F x) := by
    intro x
    refine ⟨?_, ?_⟩
    · rcases max_choice (x 0) (-2 * x 0) with h | h
      · exact ⟨0, by simp only [h0, hF, h]⟩
      · exact ⟨1, by simp only [h1, hF, h]⟩
    · rintro _ ⟨i, rfl⟩
      fin_cases i
      · simp only [Fin.zero_eta, h0, hF]
        exact le_max_left _ _
      · simp only [Fin.mk_one, h1, hF]
        exact le_max_right _ _
  obtain ⟨hconv, hhom⟩ := maxLinear_convex_homogeneous a F hgr
  have hb0 : Bornology.IsBounded {x | F x ≤ 0} := by
    refine (Bornology.isBounded_singleton (x := (0 : Vec 1))).subset (fun x hx => ?_)
    have hx' : max (x 0) (-2 * x 0) ≤ 0 := hx
    have h00 : x 0 = 0 := by
      have := le_max_left (x 0) (-2 * x 0)
      have := le_max_right (x 0) (-2 * x 0)
      linarith
    show x = 0
    ext i
    fin_cases i
    simpa using h00
  have hb1 : Bornology.IsBounded {x | F x ≤ 1} := by
    refine (Metric.isBounded_closedBall (x := (0 : Vec 1)) (r := 1)).subset (fun x hx => ?_)
    have hx' : max (x 0) (-2 * x 0) ≤ 1 := hx
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    fin_cases i
    have := le_max_left (x 0) (-2 * x 0)
    have := le_max_right (x 0) (-2 * x 0)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> simp <;> linarith
  obtain ⟨hmin, hconc⟩ := homogeneous_examples_maxLinear le_rfl a F hgr hb0
  refine ⟨a, F, hgr, hb0, hconv, hhom, hb1, ⟨fun _ => 1, ?_⟩, hmin, hconc,
    ⟨asymRun F fun _ => rfl⟩⟩
  simp only [hF, Pi.neg_apply]
  norm_num

/-- Item `A/global/prose/041` (`paper/sections/global.tex:255-258`): "The complete companion,
Chapter~7, separately proves the noncompact homogeneous value dichotomy $F(x_k)\to0$ or
$F(x_k)\to-\infty$, together with its bounded-below and additional iterate consequences."
For finite convex positively homogeneous $F$ (no coercivity): every admissible run has
$F(x_k)\to0$ or $F(x_k)\to-\infty$; if $F$ is bounded below, zero minimizes $F$ and
$F(x_k)\to0$; if the zero sublevel is bounded, $x_k\to0$ (the library's
`AdmissibleBFGSRun.homogeneous_value_dichotomy`, `homogeneous_bounded_below_convergence` and
`homogeneous_iterates_zero_of_bounded_zero_sublevel`). -/
theorem homogeneous_value_dichotomy {n : ℕ} {F : Vec n → ℝ} (_hF : ConvexOn ℝ univ F)
    (hhom : Homogeneous.PositiveDegreeOne F) (R : AdmissibleBFGSRun n F) :
    (Tendsto (fun k => F (R.x k)) atTop (𝓝 0) ∨ Tendsto (fun k => F (R.x k)) atTop atBot) ∧
      ((∃ L, ∀ x, L ≤ F x) → (∀ x, F 0 ≤ F x) ∧ Tendsto (fun k => F (R.x k)) atTop (𝓝 0)) ∧
      (Bornology.IsBounded {x | F x ≤ 0} → Tendsto R.x atTop (𝓝 0)) :=
  ⟨R.homogeneous_value_dichotomy hhom,
    fun ⟨L, hL⟩ => ⟨(R.homogeneous_bounded_below_convergence hhom L hL).1,
      (R.homogeneous_bounded_below_convergence hhom L hL).2.2⟩,
    fun hb => R.homogeneous_iterates_zero_of_bounded_zero_sublevel hhom hb⟩

/-- The Euclidean norm on $\R^2$ is not a finite maximum of linear forms $\max_ia_i^Tx$: the
upper bounds $a_i^Tx\le\|x\|$ give $\|a_i\|\le1$, so a slope active at a unit vector $u$ equals
$u$, and the finitely many slopes cannot exhaust the infinitely many unit vectors. -/
theorem euclidean_norm_not_maxLinear (m : ℕ) (a : Fin m → Vec 2) :
    ¬ ∀ x, IsGreatest (Set.range fun i => dot (a i) x) (‖euclideanVector x‖) := by
  intro h
  have hunit : ∀ u : Vec 2, ‖euclideanVector u‖ = 1 → u ∈ Set.range a := by
    intro u hu
    obtain ⟨⟨i, hi⟩, -⟩ := h u
    simp only at hi
    have hub := (h (a i)).2 ⟨i, rfl⟩
    have hu2 := norm_euclideanVector_sq u
    have ha2 := norm_euclideanVector_sq (a i)
    rw [hu] at hi hu2
    simp only [dot, sqNorm, Fin.sum_univ_two] at hi hub hu2 ha2
    have hn := norm_nonneg (euclideanVector (a i))
    have hle : (a i 0 - u 0) ^ 2 + (a i 1 - u 1) ^ 2 ≤ 0 := by nlinarith
    have e0 : (a i 0 - u 0) ^ 2 = 0 :=
      le_antisymm (by nlinarith [sq_nonneg (a i 1 - u 1)]) (sq_nonneg _)
    have e1 : (a i 1 - u 1) ^ 2 = 0 :=
      le_antisymm (by nlinarith [sq_nonneg (a i 0 - u 0)]) (sq_nonneg _)
    refine ⟨i, ?_⟩
    ext j
    fin_cases j
    · exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp e0)
    · exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp e1)
  let f : ℕ → Vec 2 := fun t => (Real.sqrt (1 + (t : ℝ) ^ 2))⁻¹ • ![1, (t : ℝ)]
  have hf1 : ∀ t, ‖euclideanVector (f t)‖ = 1 := by
    intro t
    have hpos : 0 < Real.sqrt (1 + (t : ℝ) ^ 2) := Real.sqrt_pos.mpr (by positivity)
    have hs : sqNorm (![1, (t : ℝ)] : Vec 2) = 1 + (t : ℝ) ^ 2 := by
      simp [sqNorm, Fin.sum_univ_two]
    simp only [f]
    rw [norm_euclideanVector_smul, abs_of_pos (inv_pos.mpr hpos), norm_euclideanVector, hs,
      inv_mul_cancel₀ hpos.ne']
  have hinj : Function.Injective f := by
    intro s t hst
    have h0 := congrFun hst 0
    have h1 := congrFun hst 1
    simp only [f, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, mul_one] at h0 h1
    rw [h0] at h1
    have hne : (Real.sqrt (1 + (t : ℝ) ^ 2))⁻¹ ≠ 0 :=
      inv_ne_zero (Real.sqrt_pos.mpr (by positivity)).ne'
    exact_mod_cast mul_left_cancel₀ hne h1
  have hsub : Set.range f ⊆ Set.range a := by
    rintro _ ⟨t, rfl⟩
    exact hunit _ (hf1 t)
  exact (Set.infinite_range_of_injective hinj).mono hsub (Set.finite_range a)

/-- Item `A/global/prose/032` (`paper/sections/global.tex:198`): "It imposes no smoothness or
finite-piece condition." Coercivity, with the other hypotheses of Theorem `art:homogeneous`
(finite, convex, positively homogeneous of degree one), forces neither: the $\ell^1$ norm on
$\R^2$ satisfies all of them and is not differentiable at $(1,0)\ne0$ (`l1_nonsmooth`), and the
Euclidean norm on $\R^2$ satisfies all of them and is not a finite maximum of linear forms
(`euclidean_norm_not_maxLinear`). Both are covered by the theorem (`l1_norm_case`,
`euclidean_norm_case`). -/
theorem homogeneous_no_smoothness_or_pieces :
    (∃ F : Vec 2 → ℝ, ConvexOn ℝ univ F ∧ Homogeneous.PositiveDegreeOne F ∧
      Tendsto F (cocompact (Vec 2)) atTop ∧ ∃ x : Vec 2, x ≠ 0 ∧ ¬ DifferentiableAt ℝ F x) ∧
      ∃ F : Vec 2 → ℝ, ConvexOn ℝ univ F ∧ Homogeneous.PositiveDegreeOne F ∧
        Tendsto F (cocompact (Vec 2)) atTop ∧
        ∀ (m : ℕ) (a : Fin m → Vec 2),
          ¬ ∀ x, IsGreatest (Set.range fun i => dot (a i) x) (F x) := by
  have hhom (N : Seminorm ℝ (Vec 2)) : Homogeneous.PositiveDegreeOne (N : Vec 2 → ℝ) := by
    intro t ht x
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg ht]
  have hpos1 : ∀ x : Vec 2, x ≠ 0 → 0 < l1Seminorm 2 x := by
    intro x hx
    have hx' : l1Seminorm 2 x = ∑ i, |x i| := rfl
    rw [hx']
    by_contra hle
    apply hx
    have hz : ∑ i, |x i| = 0 :=
      le_antisymm (not_lt.mp hle) (Finset.sum_nonneg (fun i _ => abs_nonneg (x i)))
    ext i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => abs_nonneg (x j))).mp hz i
      (Finset.mem_univ i)
    simpa using hi
  refine ⟨⟨l1Seminorm 2, (l1Seminorm 2).convexOn, hhom _,
    coercive_of_positive (by norm_num) (l1Seminorm 2).convexOn (hhom _) hpos1, ![1, 0], ?_,
    (l1_nonsmooth _ (fun _ => rfl) 1).2.1 _ (by simp)⟩,
    euclideanSeminorm 2, (euclideanSeminorm 2).convexOn, hhom _,
    coercive_of_lower_bound one_pos (fun x => (one_mul _).le), euclidean_norm_not_maxLinear⟩
  intro h0
  have := congrFun h0 0
  simp at this

/-! ### Non-vacuity -/

/-- The standing assumptions of Theorem `art:radial-equivalence` and of the displays of its
proof can hold, including both cases $N\ge0$ and $N<0$: $F(u,v)=u^2+|v|$, $x_*=0$, $b=4$,
the band $\eta=1/8$ with its constants $M,\theta$, the pair $x=(0,1)$, $z=(0,-1)$ ($N=2$)
and the pair $x=(1,1)$, $z=(1/2,1)$ ($N=-1/2$). -/
example : ∃ (F : Vec 2 → ℝ) (xstar : Vec 2) (b : ℝ) (K : Set (Vec 2)) (Λ R η M θ : ℝ),
    ConvexOn ℝ univ F ∧ (∀ x, F xstar ≤ F x) ∧ F xstar < b ∧ K = {x | F x ≤ b} ∧
      IsCompact K ∧ 0 < Λ ∧ 0 < R ∧
      (∀ x ∈ K, ∀ v : Vec 2, (∀ y, F x + dot v (y - x) ≤ F y) → ‖euclideanVector v‖ ≤ Λ) ∧
      (∀ x ∈ K, ‖euclideanVector (x - xstar)‖ ≤ R) ∧ InwardModelCondition F xstar K ∧
      0 < η ∧ 0 ≤ M ∧ 0 < θ ∧ θ ≤ 1 / 2 ∧
      (∀ x g : Vec 2, x ∈ K → HasFDerivAt F (gradientFunctional g) x → F xstar + η ≤ F x →
        ∀ τ : ℝ, 0 ≤ τ → τ ≤ θ →
          0 ≤ F (x - τ • (x - xstar)) - F x + τ * dot g (x - xstar) ∧
            F (x - τ • (x - xstar)) - F x + τ * dot g (x - xstar) ≤ M / 2 * τ ^ 2) ∧
      (∃ x z g h : Vec 2, x ∈ K ∧ z ∈ K ∧ HasFDerivAt F (gradientFunctional g) x ∧
        HasFDerivAt F (gradientFunctional h) z ∧ F xstar + η ≤ F z ∧ F z ≤ F x ∧
        0 < dot (h - g) (z - x) ∧ 0 ≤ dot (h - g) (z - xstar)) ∧
      (∃ x z g h : Vec 2, x ∈ K ∧ z ∈ K ∧ HasFDerivAt F (gradientFunctional g) x ∧
        HasFDerivAt F (gradientFunctional h) z ∧ F xstar + η ≤ F z ∧ F z ≤ F x ∧
        0 < dot (h - g) (z - x) ∧ dot (h - g) (z - xstar) < 0) := by
  obtain ⟨hconv, hmin, -, hK, -⟩ := mixed_hypotheses UnexcitedMetric.objective (fun _ => rfl)
  have hinw := ((mixed_inward_condition UnexcitedMetric.objective (fun _ => rfl)).2.2 4
    (by norm_num)).2
  obtain ⟨Λ, R, hΛ, hR, hΛK, hRK⟩ := exists_subgradient_and_radius_bounds hconv 0 (hK 4)
  obtain ⟨M, θ, hM, hθ, hθ', hband⟩ := hinw (1 / 8) (by norm_num)
  have hF : ∀ u v : ℝ, UnexcitedMetric.objective ![u, v] = u ^ 2 + |v| := fun u v => rfl
  have hF0 : UnexcitedMetric.objective 0 = 0 := by simp [UnexcitedMetric.objective]
  have hgrad := fun (u v : ℝ) (hv : v ≠ 0) => ArticleGeometry.mixed_ridge_gradient (u := u) hv
  refine ⟨UnexcitedMetric.objective, 0, 4, _, Λ, R, 1 / 8, M, θ, hconv, hmin, by rw [hF0]; norm_num,
    rfl, hK 4, hΛ, hR, hΛK, hRK, hinw, by norm_num, hM, hθ, hθ', hband, ?_, ?_⟩
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

/-- The standing assumptions of Theorem `art:centered`, of display `A/global/disp/009` and of
Corollary `art:radial-convergence` can hold: the benchmark with $\psi(u,v)=u^2$,
$\gamma(u,v)=|v|$, $x_*=0$, $U=\R^2$, the library's explicit admissible run
`UnexcitedMetric.run` (with $c_1=1/4$, $c_2=1/2$), its initial sublevel $K$ and a Lipschitz
constant $L$. The same run shows that the "every admissible run" conclusions of `centered`,
`centered_global`, `radial_convergence` and `mixed_benchmark` are not vacuous. -/
example : ∃ (F ψ γ : Vec 2 → ℝ) (xstar : Vec 2) (U : Set (Vec 2)) (R : AdmissibleBFGSRun 2 F)
    (K : Set (Vec 2)) (L : ℝ),
    ConvexOn ℝ univ F ∧ (∀ x, F xstar ≤ F x) ∧ IsOpen U ∧ Convex ℝ U ∧ ConvexOn ℝ U ψ ∧
      CenteredSmoothSublinear.LocallyC11On U ψ ∧ ConvexOn ℝ univ γ ∧
      Homogeneous.PositiveDegreeOne γ ∧ (∀ x ∈ U, F x = ψ x + γ (x - xstar)) ∧
      IsCompact {x | F x ≤ F (R.x 0)} ∧ {x | F x ≤ F (R.x 0)} ⊆ U ∧
      K = {x | F x ≤ F (R.x 0)} ∧ 0 ≤ L ∧
      (∀ x ∈ K, ∀ y ∈ K, ‖euclideanVector (coordinateGradient ψ y - coordinateGradient ψ x)‖ ≤
        L * ‖euclideanVector (y - x)‖) ∧
      F xstar < F (R.x 0) ∧ InwardModelCondition F xstar K := by
  obtain ⟨hconv, hmin, -, hK, hψ, hψ11, hγ, hγh, hrep⟩ :=
    mixed_hypotheses UnexcitedMetric.objective (fun _ => rfl)
  let R := UnexcitedMetric.run 1 1 (1 / 4) (1 / 4) (1 / 2) one_pos one_pos (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨L, hL0, hL⟩ := uniform_lipschitz_gradient isOpen_univ hψ11 (hK (UnexcitedMetric.objective
    (R.x 0))) (subset_univ _)
  exact ⟨_, _, _, 0, univ, R, _, L, hconv, hmin, isOpen_univ, convex_univ, hψ, hψ11, hγ, hγh,
    fun x _ => hrep x, hK _, subset_univ _, rfl, hL0, hL, initial_value_gt R 0 hmin,
    centered_inward_condition hconv 0 hmin univ isOpen_univ convex_univ _ hψ hψ11 _ hγ hγh
      (fun x _ => hrep x) R (hK _) (subset_univ _)⟩

/-- The hypotheses of Theorem `art:homogeneous` (and of display `A/global/disp/012`) can hold,
and admissible runs exist for them, so the "every admissible run" conclusions about coercive
degree-one homogeneous objectives are not vacuous. $F(x)=|x|$ on $\R$ ($n=1$) is convex,
positively homogeneous of degree one and coercive; it is the norm `normSeminorm ℝ (Vec 1)`, a
gauge with bounded unit sublevel, the linear maximum $\max(x,-x)$ with bounded zero sublevel,
$\|x\|_1$, $\|x\|_\infty$ and the Euclidean norm on $\R^1$; and `absRun` is an admissible run
for it, also as the norm. This covers `homogeneous`, `homogeneous_via_radial`, the three cases
`homogeneous_examples_*`, `l1_norm_case`, `linf_norm_case`, `euclidean_norm_case` and
`homogeneous_value_dichotomy`; `asymmetric_example` exhibits its own run (`asymRun`). -/
example : ∃ F : Vec 1 → ℝ,
    1 ≤ 1 ∧ ConvexOn ℝ univ F ∧ Homogeneous.PositiveDegreeOne F ∧
      Tendsto F (cocompact (Vec 1)) atTop ∧
      Bornology.IsBounded {x | F x ≤ 1} ∧ Bornology.IsBounded {x | F x ≤ 0} ∧
      (∀ x, IsGreatest (Set.range fun i =>
        dot (![OneDimensional.embed 1, OneDimensional.embed (-1)] i) x) (F x)) ∧
      (∀ x, F x = ∑ i, |x i|) ∧ (∀ x, IsGreatest (Set.range fun i => |x i|) (F x)) ∧
      (∀ x, F x = Real.sqrt (∑ i, (x i) ^ 2)) ∧ (∀ x, F x = normSeminorm ℝ (Vec 1) x) ∧
      Nonempty (AdmissibleBFGSRun 1 F) ∧
      Nonempty (AdmissibleBFGSRun 1 (normSeminorm ℝ (Vec 1))) := by
  have hgr : ∀ x : Vec 1, IsGreatest (Set.range fun i => |x i|) (|x 0|) := by
    intro x
    refine ⟨⟨0, rfl⟩, ?_⟩
    rintro _ ⟨i, rfl⟩
    rw [Subsingleton.elim i 0]
  have hnorm : ∀ x : Vec 1, |x 0| = ‖x‖ := linf_eq_norm _ hgr
  have hhom : Homogeneous.PositiveDegreeOne (fun x : Vec 1 => |x 0|) := by
    intro t ht x
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg ht]
  have hzero : ∀ x : Vec 1, x 0 = 0 → x = 0 := by
    intro x h0
    ext i
    rw [Subsingleton.elim i 0]
    exact h0
  have hpos : ∀ x : Vec 1, x ≠ 0 → 0 < |x 0| :=
    fun x hx => abs_pos.mpr (fun h0 => hx (hzero x h0))
  have hnormF : ∀ x : Vec 1, (normSeminorm ℝ (Vec 1)) x = |x 0| := fun x => by
    rw [coe_normSeminorm]
    exact (hnorm x).symm
  refine ⟨fun x => |x 0|, le_rfl, abs_coord_convex, hhom,
    coercive_of_positive le_rfl abs_coord_convex hhom hpos, ?_, ?_, ?_, ?_, hgr, ?_,
    fun x => (hnormF x).symm, ⟨absRun _ fun _ => rfl⟩, ⟨absRun _ hnormF⟩⟩
  · refine (Metric.isBounded_closedBall (x := (0 : Vec 1)) (r := 1)).subset (fun x hx => ?_)
    rw [Metric.mem_closedBall, dist_zero_right, ← hnorm]
    exact hx
  · refine (Bornology.isBounded_singleton (x := (0 : Vec 1))).subset (fun x hx => ?_)
    have hx' : |x 0| ≤ 0 := hx
    exact hzero x (abs_nonpos_iff.mp hx')
  · intro x
    have h0 : dot (OneDimensional.embed 1) x = x 0 := by simp [dot]
    have h1 : dot (OneDimensional.embed (-1)) x = -x 0 := by simp [dot]
    refine ⟨?_, ?_⟩
    · rcases abs_choice (x 0) with h | h
      · exact ⟨0, by simp only [Matrix.cons_val_zero, h0, h]⟩
      · exact ⟨1, by simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero, h1,
          h]⟩
    · rintro _ ⟨i, rfl⟩
      fin_cases i
      · simp only [Fin.zero_eta, Matrix.cons_val_zero, h0]
        exact le_abs_self _
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero, h1]
        exact neg_le_abs _
  · intro x
    simp
  · intro x
    simp [Real.sqrt_sq_eq_abs]

end BfgsCoverage.Article.Global
