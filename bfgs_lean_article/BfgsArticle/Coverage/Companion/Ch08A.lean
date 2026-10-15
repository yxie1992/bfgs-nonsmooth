import BfgsArticle.Coverage.Article.Energy
import BfgsArticle.Coverage.Article.Global
import BfgsVerification.AffineCriticalObjective
import BfgsVerification.AffineRankLossTargets
import BfgsVerification.AffineRankLossObjective
import BfgsVerification.AffineGapTargets
import BfgsVerification.SemialgebraicCriticalGeometry
import BfgsVerification.AffineCriticalSemialgebraicPathComponents
import BfgsVerification.ObjectiveSemialgebraicComposition
import BfgsVerification.AffineCriticalDefinability
import BfgsVerification.ContinuousSemialgebraicComponents
import BfgsVerification.AffineSupportPath
import BfgsVerification.CriticalSmoothPathValues
import BfgsVerification.PlanarActiveGeometry

/-!
# Lean coverage: `companion/chapters/08_A.tex`

Chapter A ("Affine criticality and stratified geometry"): the projected-subgradient and
affine-hull decomposition, the condition (A:AC) and equal-rate descent, the compact-run reduction,
the rank-loss example, local affine-critical correctness of nondegenerate smooth maxima with the
lower semicontinuity of $\gamma$, Proposition `A:semialgebraic` with its proof and the path-class
statements, the general-dimensional conjecture (OPEN), and the bibliographic remarks. Register:
`editorial/lean_coverage/register/C_08_A.json`.

## Lean forms

$\partial F(p)$ is the global supporting set `ConvexSubdifferential.subdifferential F p`
($g$ with $F(z)\ge F(p)+g^T(z-p)$ for all $z$); its Euclidean copy is the family
`subgradientFamily F p`. Then $0\in\operatorname{aff}\partial F(p)$ is `IsAffineCritical F p`
(equivalently `(0 : Vec n) ∈ affineSpan ℝ (subdifferential F p)`, `ac_def`), (A:AC) at $p$ is
`AffineCorrectAt F p`, $V(p)$, $U(p)$, $a(p)$ are `jumpSpace`, `tangentSpace`, `canonicalVector`
(`decomposition_notation`), and $\gamma(p)$ is `AffineDistance.objectiveDistance F p`
(`gamma_def`). Pairings with $a(p)$ are Euclidean inner products of `euclideanVector g`. A finite
maximum $F=\max_if_i$ is `∀ x, IsGreatest (Set.range fun i => f i x) (F x)`, $\nabla f_i$ is
`coordinateGradient (f i)`, $I_*$ is `activeIndices F f xstar`, enumerated by `activeIndexMap`.
Semialgebraic objects are the library's `RealAlgebraicGeometry.IsSemialgebraic` sets (Boolean
polynomial formulas) and `IsSemialgebraicObjective` (semialgebraic graph,
`semialgebraic_objective_def`).

## Items

* Lines 3-27: `balances` (prose/001), `decomposition_notation` (disp/001),
  `affine_hull_decomposition` (prose/006), `subgradient_projection` (disp/002), `ac_def`
  (disp/003), `ac_iff_equal_rate`, `canonical_direction`, `equal_rate_excludes`,
  `equal_rate_stronger` (prose/007-010), `cluster_values`, `cluster_reduction`,
  `abs_gradients_unit` (prose/011, 012, 014).
* Lines 32-44: `gamma_def` (prose/015), `PositiveGapOnBands` (prose/016),
  `rank_loss_no_positive_minimum` (prose/017), `rank_loss_objective` (disp/004),
  `rank_loss_curvature`, `vertical_axis`, `origin_point`, `horizontal_axis`,
  `smooth_points_affine_critical`, `ac_global_and_gap` (prose/018-023), `rank_loss_point_excluded`
  (prose/025).
* Lines 49-76: `local_affine_correctness` (prose/026, with disp/005), `zero_extension_solves`
  (disp/006), `unique_solution_formula` (disp/007), `gamma_lsc`, `subfamily_distance_continuous`,
  `constant_active_subsequence` (prose/028-030), `limit_along_constant_active_set` (disp/008),
  `positive_minimum_on_bands` (prose/031), `gap_gives_visibility` (prose/032).
* Lines 81-117: `low_level_gap` (Proposition `A:semialgebraic`, with disp/009), `lifted_graph`,
  `support_local_min`, `path_derivative_pairing` (disp/010-012), `finitely_many_values` (proof
  steps), `PiecewiseC1` (prose/033), `path_classes`, `path_regularity`, `classes_constant`,
  `topological_components` (prose/035-038), `clarke_implies_affine` (prose/039).
* Lines 121-126: `GeneralDimensionalConjecture` with `activeTangentSpace` (prose/042, OPEN, with
  disp/013), `straightening_breaks_bfgs` (prose/045).
* Lines 131-139: `affine_zero_projects` (prose/056).

## Standing assumptions

The displays of the proof of the local statement are stated under its hypotheses (with the matrix
$A(p)$ as a variable with its defining equation); those of the proof of Proposition
`A:semialgebraic` under the proposition's hypotheses and the path, time and subgradient the proof
introduces. Hypotheses whose names start with `_` are standing assumptions that a proof does not
use.

## Non-vacuity

The examples at the end show that the hypotheses can hold: the one-branch maximum $F=x^2/2$ for
the local statement, the quadratic run for the cluster reduction, the semialgebraic $F=x^2/2$ with a
constant path for the proposition and its proof displays, a positive gap for
`gap_gives_visibility`, and the one-branch maximum $F=x^2/2$ for the hypotheses of the OPEN
`GeneralDimensionalConjecture`. The other statements are about explicit examples (`maxTwo`, $|x|$,
the rank-loss objective, the straightening map with
$F(u,v)=\max\{18u^2+v^2+v,\,2u^2+v^2-v\}$).
-/

noncomputable section
open scoped BigOperators Topology InnerProductSpace
open Matrix Filter BfgsVerification
open AffineCriticalObjective AffineCriticalGeometry AccessibleJumpGeometry ConvexSubdifferential

namespace BfgsCoverage.Companion.Ch08A

/-! ### Helpers -/

/-- `euclideanVector` maps $0$ to $0$. -/
theorem euclideanVector_zero {n : ℕ} : euclideanVector (0 : Vec n) = 0 := rfl

/-- `dot` is symmetric. -/
theorem dot_comm' {n : ℕ} (a b : Vec n) : dot a b = dot b a := dotProduct_comm a b

/-- Clarke (convex) criticality implies affine criticality:
$0\in\partial F(p)\Rightarrow0\in\operatorname{aff}\partial F(p)$. -/
theorem affineCritical_of_zero_mem {n : ℕ} {F : Vec n → ℝ} {p : Vec n}
    (h : (0 : Vec n) ∈ subdifferential F p) : IsAffineCritical F p := by
  have he : (0 : EuclideanSpace ℝ (Fin n)) = subgradientFamily F p ⟨0, h⟩ := rfl
  rw [IsAffineCritical, he]
  exact mem_affineSpan ℝ (Set.mem_range_self _)

/-- For $g\in\R^1$, the Euclidean norm is $|g_0|$. -/
theorem norm_euclideanVector_one (g : Vec 1) : ‖euclideanVector g‖ = |g 0| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs, Real.sqrt_sq_eq_abs]
  rfl

/-! ### Section "Equal-rate descent and affine criticality" (lines 7-27) -/

/-- Item `C/08_A/prose/001` (`companion/chapters/08_A.tex:3`): "Affine balance concerns
equal-rate descent, whereas convex balance concerns stationarity." For finite convex $F$ and
every point $p$: $0\notin\operatorname{aff}\partial F(p)$ iff some $v$ has $g^Tv=-1$ for every
$g\in\partial F(p)$; and $0\in\partial F(p)$ iff $p$ minimizes $F$ (stationarity). -/
theorem balances {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ Set.univ F) (p : Vec n) :
    (¬ IsAffineCritical F p ↔ ∃ v : Vec n, ∀ g ∈ subdifferential F p, dot g v = -1) ∧
      ((0 : Vec n) ∈ subdifferential F p ↔ ∀ z, F p ≤ F z) :=
  ⟨(equal_rate_exists_iff_not_affineCritical hF p).symm, zero_mem_iff_global_minimum⟩

/-- Item `C/08_A/disp/001` (`companion/chapters/08_A.tex:12-15`): "For a finite convex $F$, put
$V(p)=\operatorname{span}(\partial F(p)-\partial F(p))$, $U(p)=V(p)^\perp$,
$a(p)=\operatorname{proj}_{\operatorname{aff}\partial F(p)}0$." In Lean the subgradients are taken
in Euclidean space (`subgradientFamily F p`, the family $g\mapsto g$ on $\partial F(p)$, with range
`euclideanVector '' ∂F(p)`); $V(p)$ is `jumpSpace (subgradientFamily F p)` (the vector span of the
range), which is the span of the differences; $U(p)$ is `tangentSpace` $=V(p)^\perp$; and $a(p)$ is
`canonicalVector hF p`, the Euclidean orthogonal projection of $0$ onto the affine hull. -/
theorem decomposition_notation {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ Set.univ F) (p : Vec n)
    [Nonempty (affineSpan ℝ (Set.range (subgradientFamily F p)))] :
    Set.range (subgradientFamily F p) = euclideanVector '' subdifferential F p ∧
      jumpSpace (subgradientFamily F p) = Submodule.span ℝ
        ((euclideanVector '' subdifferential F p) -ᵥ (euclideanVector '' subdifferential F p)) ∧
      tangentSpace (subgradientFamily F p) = (jumpSpace (subgradientFamily F p))ᗮ ∧
      canonicalVector hF p = (EuclideanGeometry.orthogonalProjection
        (affineSpan ℝ (Set.range (subgradientFamily F p))) 0 : EuclideanSpace ℝ (Fin n)) := by
  refine ⟨range_subgradientFamily F p, ?_, rfl, ?_⟩
  · rw [jumpSpace, vectorSpan_def, range_subgradientFamily]
  · exact closest_eq_affine_orthogonalProjection (subgradientFamily F p) _

/-- Item `C/08_A/prose/006` (`companion/chapters/08_A.tex:16`): "The affine hull equals
$a(p)+V(p)$ and $a(p)\perp V(p)$." -/
theorem affine_hull_decomposition {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ Set.univ F)
    (p : Vec n) :
    (∀ z : EuclideanSpace ℝ (Fin n), z ∈ affineSpan ℝ (Set.range (subgradientFamily F p)) ↔
        z - canonicalVector hF p ∈ jumpSpace (subgradientFamily F p)) ∧
      canonicalVector hF p ∈ (jumpSpace (subgradientFamily F p))ᗮ :=
  ⟨fun z => mem_affineSpan_iff_sub_closest_mem (subgradientFamily F p) _ z,
    closestAffinePoint_orthogonal (subgradientFamily F p) _⟩

/-- Item `C/08_A/disp/002` (`companion/chapters/08_A.tex:17-19`): "Hence every subgradient
satisfies $P_{U(p)}g=a(p)$, $g^Ta(p)=\|a(p)\|^2$." -/
theorem subgradient_projection {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ Set.univ F) (p : Vec n)
    (g : Vec n) (hg : g ∈ subdifferential F p) :
    ((tangentSpace (subgradientFamily F p)).orthogonalProjection (euclideanVector g) :
        EuclideanSpace ℝ (Fin n)) = canonicalVector hF p ∧
      ⟪euclideanVector g, canonicalVector hF p⟫_ℝ = ‖canonicalVector hF p‖ ^ 2 :=
  ⟨(canonicalVector_eq hF p ⟨g, hg⟩).symm, canonicalVector_pairing hF p g hg⟩

/-- Item `C/08_A/disp/003`, equation `A:AC` (`companion/chapters/08_A.tex:21-23`): the condition
$0\in\operatorname{aff}\partial F(p)\Rightarrow0\in\partial F(p)$ is the library's
`AffineCorrectAt F p`; its premise `IsAffineCritical F p` (stated for the Euclidean copy of
$\partial F(p)$) is $0\in\operatorname{aff}\partial F(p)$ with the affine hull taken in $\R^n$. -/
theorem ac_def {n : ℕ} (F : Vec n → ℝ) (p : Vec n) :
    (AffineCorrectAt F p ↔
        ((0 : Vec n) ∈ affineSpan ℝ (subdifferential F p) → (0 : Vec n) ∈ subdifferential F p)) ∧
      (IsAffineCritical F p ↔ (0 : Vec n) ∈ affineSpan ℝ (subdifferential F p)) := by
  have h := isAffineCritical_iff_coordinate_affineSpan F p
  exact ⟨by rw [AffineCorrectAt, h], h⟩

/-- Item `C/08_A/prose/007` (`companion/chapters/08_A.tex:24`): "[\eqref{A:AC}] is therefore
equivalent, at every nonoptimal point under consideration, to the existence of a direction $v$ with
$g^Tv=-1$ for every $g\in\partial F(p)$." -/
theorem ac_iff_equal_rate {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ Set.univ F) (p : Vec n)
    (hp : p ∉ argmin F) :
    AffineCorrectAt F p ↔ ∃ v : Vec n, ∀ g ∈ subdifferential F p, dot g v = -1 := by
  rw [affineCorrectAt_iff_nonoptimal_equal_rate hF p]
  exact ⟨fun h => h hp, fun h _ => h⟩

/-- Item `C/08_A/prose/008` (`companion/chapters/08_A.tex:24`): "One may take
$v=-a(p)/\|a(p)\|^2$." At a point that is not affine critical (by (A:AC), every nonoptimal point
where it holds): $a(p)\ne0$ and $v=-a(p)/\|a(p)\|^2$ has $g^Tv=-1$ for every $g\in\partial F(p)$
(Euclidean pairing). -/
theorem canonical_direction {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ Set.univ F) (p : Vec n) :
    (AffineCorrectAt F p → p ∉ argmin F → ¬ IsAffineCritical F p) ∧
      (¬ IsAffineCritical F p → canonicalVector hF p ≠ 0 ∧ ∀ g ∈ subdifferential F p,
        ⟪euclideanVector g, -(‖canonicalVector hF p‖ ^ 2)⁻¹ • canonicalVector hF p⟫_ℝ = -1) := by
  refine ⟨fun hc hp ha => hp (zero_mem_iff_global_minimum.mp (hc ha)), fun hp => ⟨?_, ?_⟩⟩
  · exact fun h0 => hp ((canonicalVector_zero_iff hF p).mp h0)
  · intro g hg
    exact canonical_equal_rate (subgradientFamily F p) _ hp ⟨g, hg⟩

/-- Item `C/08_A/prose/009` (`companion/chapters/08_A.tex:24`): "Conversely such an equal-rate
direction rules out zero in the affine hull." -/
theorem equal_rate_excludes {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ Set.univ F) (p : Vec n)
    (h : ∃ v : Vec n, ∀ g ∈ subdifferential F p, dot g v = -1) : ¬ IsAffineCritical F p :=
  (equal_rate_exists_iff_not_affineCritical hF p).mp h

/-- The objective $F(x)=\max(x,2x)$ on $\R$ (used for `equal_rate_stronger`). -/
def maxTwo : Vec 1 → ℝ := fun x => max (x 0) (2 * x 0)

theorem maxTwo_convex : ConvexOn ℝ Set.univ maxTwo := by
  have h1 : ConvexOn ℝ Set.univ (fun x : Vec 1 => x 0) := by
    refine ⟨convex_univ, fun x _ y _ a b _ _ _ => ?_⟩
    simp
  have h2 : ConvexOn ℝ Set.univ (fun x : Vec 1 => 2 * x 0) := by
    refine ⟨convex_univ, fun x _ y _ a b _ _ _ => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith
  exact h1.sup h2

/-- Item `C/08_A/prose/010` (`companion/chapters/08_A.tex:24`): "This is stronger than ordinary
strict descent, which requires only negative, not equal, inner products." Every equal-rate
direction is a strict descent direction ($g^Tv<0$ for all $g\in\partial F(p)$); the converse fails:
for $F(x)=\max(x,2x)$ at $p=0$, $\partial F(0)\subseteq[1,2]$ contains $1$ and $2$, so $v=-1$ is a
strict descent direction but no $v$ has $g^Tv=-1$ for every subgradient. -/
theorem equal_rate_stronger :
    (∀ {n : ℕ} (F : Vec n → ℝ) (p v : Vec n), (∀ g ∈ subdifferential F p, dot g v = -1) →
        ∀ g ∈ subdifferential F p, dot g v < 0) ∧
      ∃ (F : Vec 1 → ℝ) (p v : Vec 1), (∀ x, F x = max (x 0) (2 * x 0)) ∧
        ConvexOn ℝ Set.univ F ∧ (∀ g ∈ subdifferential F p, dot g v < 0) ∧
        ¬ ∃ w : Vec 1, ∀ g ∈ subdifferential F p, dot g w = -1 := by
  refine ⟨fun F p v h g hg => by rw [h g hg]; norm_num, maxTwo, 0, fun _ => -1, fun _ => rfl,
    maxTwo_convex, fun g hg => ?_, fun ⟨w, hw⟩ => ?_⟩
  · have h := hg (fun _ => -1)
    simp only [maxTwo, dot, Fin.sum_univ_one, sub_zero, Pi.zero_apply] at h
    simp only [dot, Fin.sum_univ_one]
    norm_num at h ⊢
    linarith
  · have h1 : (fun _ => (1 : ℝ)) ∈ subdifferential maxTwo (0 : Vec 1) := by
      intro z
      simp only [maxTwo, dot, Fin.sum_univ_one, sub_zero, Pi.zero_apply]
      norm_num
    have h2 : (fun _ => (2 : ℝ)) ∈ subdifferential maxTwo (0 : Vec 1) := by
      intro z
      simp only [maxTwo, dot, Fin.sum_univ_one, sub_zero, Pi.zero_apply]
      norm_num
    have e1 := hw _ h1
    have e2 := hw _ h2
    simp only [dot, Fin.sum_univ_one] at e1 e2
    linarith

/-- Item `C/08_A/prose/011` (`companion/chapters/08_A.tex:26`): "On a compact admissible run,
all cluster points share the limiting value $\ell$." For an admissible run staying in a compact
set $K$, the values converge to some $\ell$ and every cluster point $p$ of $(x_k)$ has
$F(p)=\ell$. -/
theorem cluster_values {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) {K : Set (Vec n)}
    (hK : IsCompact K) (hxK : ∀ k, R.x k ∈ K) :
    ∃ ℓ : ℝ, Tendsto (fun k => F (R.x k)) atTop (𝓝 ℓ) ∧
      ∀ p : Vec n, MapClusterPt p atTop R.x → F p = ℓ := by
  obtain ⟨L, hL⟩ := convex_boundedBelow_on_compact R.convex hK
  obtain ⟨ℓ, hℓ⟩ := R.objective_value_limit_of_lower_bound L (fun k => hL _ (hxK k))
  exact ⟨ℓ, hℓ, fun p hp => R.value_of_cluster hℓ hp⟩

/-- Item `C/08_A/prose/012` (`companion/chapters/08_A.tex:26`): "If at least one cluster point
is affine critical and \eqref{A:AC} holds on the basin, that point is optimal, so $\ell=F_*$.
Compactness gives convergence to the solution set, and uniqueness gives convergence of the entire
sequence." For an admissible run in a compact $K$ on which (A:AC) holds, and an affine-critical
cluster point $p$: $p$ minimizes $F$, $F(x_k)\to F(p)=F_*$, the Euclidean distance to
$\arg\min F$ tends to $0$, and $x_k\to p$ if $p$ is the unique minimizer. No convergence of the
iterates is assumed. -/
theorem cluster_reduction {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) {K : Set (Vec n)}
    (hK : IsCompact K) (hxK : ∀ k, R.x k ∈ K) (hcorrect : ∀ p ∈ K, AffineCorrectAt F p)
    (p : Vec n) (hp : MapClusterPt p atTop R.x) (ha : IsAffineCritical F p) :
    (∀ z, F p ≤ F z) ∧ Tendsto (fun k => F (R.x k)) atTop (𝓝 (F p)) ∧
      Tendsto (fun k => euclideanSolutionDistance F (R.x k)) atTop (𝓝 0) ∧
      ((∀ z, F z = F p → z = p) → Tendsto R.x atTop (𝓝 p)) := by
  obtain ⟨hmin, hv, -, hd, hu⟩ := R.convergence_of_affineCritical_cluster hK hxK hcorrect p hp ha
  exact ⟨hmin, hv, hd, hu⟩

/-- Item `C/08_A/prose/014` (`companion/chapters/08_A.tex:26`): "It would be incorrect to
replace affine criticality of a cluster point by vanishing gradients at differentiable iterates:
for example, the gradients of $|x|$ have unit magnitude away from its minimizer." For $F(x)=|x|$ on
$\R$: every gradient at a point $x\ne0$ has norm $1$; and the admissible run $x_k=(-1/2)^k$
(`BfgsCoverage.Article.Global.absRun`) converges to the minimizer $0$, its cluster point $0$ is
affine critical, yet $\|g_k\|=1$ for every $k$: the gradients do not vanish. -/
theorem abs_gradients_unit :
    ∃ F : Vec 1 → ℝ, (∀ x, F x = |x 0|) ∧ ConvexOn ℝ Set.univ F ∧ (∀ x, F 0 ≤ F x) ∧
      (∀ x g : Vec 1, x ≠ 0 → HasFDerivAt F (gradientFunctional g) x → ‖euclideanVector g‖ = 1) ∧
      ∃ R : AdmissibleBFGSRun 1 F, Tendsto R.x atTop (𝓝 0) ∧
        (∀ k, ‖euclideanVector (R.g k)‖ = 1) ∧ MapClusterPt (0 : Vec 1) atTop R.x ∧
        IsAffineCritical F 0 := by
  let F : Vec 1 → ℝ := BfgsCoverage.Article.Energy.absF
  have hF : ∀ x, F x = |x 0| := fun _ => rfl
  have hmin : ∀ x, F 0 ≤ F x := fun x => by simp [F, BfgsCoverage.Article.Energy.absF]
  let R := BfgsCoverage.Article.Global.absRun F hF
  have hx : ∀ k, R.x k = OneDimensional.embed ((-1) ^ k * (1 / 2) ^ k) := fun _ => rfl
  have hg : ∀ k, R.g k = OneDimensional.embed ((-1) ^ k) := fun _ => rfl
  have hlim : Tendsto R.x atTop (𝓝 0) := by
    have hs : Tendsto (fun k : ℕ => ((-1 : ℝ) ^ k * (1 / 2) ^ k)) atTop (𝓝 0) := by
      have h := tendsto_pow_atTop_nhds_zero_of_abs_lt_one (r := (-1 / 2 : ℝ))
        (by rw [abs_lt]; constructor <;> norm_num)
      refine h.congr fun k => ?_
      rw [← mul_pow]
      norm_num
    have hc := (OneDimensional.embed.continuous.tendsto 0).comp hs
    simp only [map_zero] at hc
    exact hc.congr fun k => (hx k).symm
  refine ⟨F, hF, BfgsCoverage.Article.Energy.abs_coord_convex, hmin, fun x g hx0 hgx => ?_,
    R, hlim, fun k => ?_, hlim.mapClusterPt, affineCritical_of_zero_mem
      (zero_mem_iff_global_minimum.mpr hmin)⟩
  · have hx0' : x 0 ≠ 0 := by
      intro h
      apply hx0
      funext i
      fin_cases i
      exact h
    have h := BfgsCoverage.Article.Energy.absF_grad hx0' hgx
    rw [norm_euclideanVector_one, h]
    split_ifs <;> norm_num
  · rw [hg k, norm_euclideanVector_one, OneDimensional.embed_apply, abs_pow, abs_neg, abs_one,
      one_pow]

/-! ### Section "Why pointwise affine separation need not be uniform" (lines 32-44) -/

/-- Item `C/08_A/prose/015` (`companion/chapters/08_A.tex:34`): "Let
$\gamma(p)=\operatorname{dist}(0,\operatorname{aff}\partial F(p))$." This is the library's
`AffineDistance.objectiveDistance F p`, the Euclidean distance from $0$ to the affine hull of the
Euclidean copy of $\partial F(p)$; for finite convex $F$ it equals $\|a(p)\|$, and it is positive
exactly at the points that are not affine critical. -/
theorem gamma_def {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ Set.univ F) (p : Vec n) :
    AffineDistance.objectiveDistance F p = Metric.infDist (0 : EuclideanSpace ℝ (Fin n))
        (affineSpan ℝ (euclideanVector '' subdifferential F p) : Set (EuclideanSpace ℝ (Fin n))) ∧
      AffineDistance.objectiveDistance F p = ‖canonicalVector hF p‖ ∧
      (0 < AffineDistance.objectiveDistance F p ↔ ¬ IsAffineCritical F p) := by
  refine ⟨by rw [AffineDistance.objectiveDistance, range_subgradientFamily],
    affine_distance_eq_norm hF p, AffineDistance.objectiveDistance_pos_iff hF p⟩

/-- Item `C/08_A/prose/016` (`companion/chapters/08_A.tex:34`): "A useful quantitative
condition is a positive minimum of $\gamma$ on every compact positive objective band." The
condition: on every band $\{F_*+\eta\le F\le b\}$ ($\eta>0$) that is compact and nonempty, $\gamma$
attains a strictly positive minimum. -/
def PositiveGapOnBands {n : ℕ} (F : Vec n → ℝ) (Fstar : ℝ) : Prop :=
  ∀ η b : ℝ, 0 < η → IsCompact {x | Fstar + η ≤ F x ∧ F x ≤ b} →
    {x | Fstar + η ≤ F x ∧ F x ≤ b}.Nonempty →
    ∃ p ∈ {x | Fstar + η ≤ F x ∧ F x ≤ b}, 0 < AffineDistance.objectiveDistance F p ∧
      ∀ q ∈ {x | Fstar + η ≤ F x ∧ F x ≤ b},
        AffineDistance.objectiveDistance F p ≤ AffineDistance.objectiveDistance F q

/-- The rank-loss example's $\gamma$ is the library's `AffineRankLoss.affineDistance`. -/
theorem rankLoss_gamma (x : Vec 2) :
    AffineDistance.objectiveDistance AffineRankLoss.objective x = AffineRankLoss.affineDistance x :=
  rfl

/-- Item `C/08_A/disp/004` (`companion/chapters/08_A.tex:37-40`): "Consider
$F(u,v)=u+u^2+v^2+|uv|=\max\{u+u^2+v^2+uv,\ u+u^2+v^2-uv\}$." The library's
`AffineRankLoss.objective` (with $u=x_0$, $v=x_1$) is this function, the maximum of its two
branches `AffineRankLoss.branch 0`, `branch 1`. -/
theorem rank_loss_objective (x : Vec 2) :
    AffineRankLoss.objective x = x 0 + x 0 ^ 2 + x 1 ^ 2 + |x 0 * x 1| ∧
      AffineRankLoss.objective x = max (x 0 + x 0 ^ 2 + x 1 ^ 2 + x 0 * x 1)
        (x 0 + x 0 ^ 2 + x 1 ^ 2 - x 0 * x 1) ∧
      AffineRankLoss.branch 0 x = x 0 + x 0 ^ 2 + x 1 ^ 2 + x 0 * x 1 ∧
      AffineRankLoss.branch 1 x = x 0 + x 0 ^ 2 + x 1 ^ 2 - x 0 * x 1 := by
  have h0 : AffineRankLoss.branch 0 x = x 0 + x 0 ^ 2 + x 1 ^ 2 + x 0 * x 1 := by
    simp [AffineRankLoss.branch]
  have h1 : AffineRankLoss.branch 1 x = x 0 + x 0 ^ 2 + x 1 ^ 2 - x 0 * x 1 := by
    simp [AffineRankLoss.branch]
    ring
  refine ⟨rfl, ?_, h0, h1⟩
  rw [AffineRankLoss.objective_eq_max, h0, h1]

/-- Item `C/08_A/prose/018` (`companion/chapters/08_A.tex:41`): "Both branch Hessians have
eigenvalues $1$ and $3$, so $F$ is strongly convex, with unique minimizer $(-1/2,0)$ and value
$-1/4$." Each branch is $C^\infty$ with constant Hessian matrix
$\begin{pmatrix}2&\pm1\\\pm1&2\end{pmatrix}$ (the matrix of the second derivative,
`RadialHessian.matrix`), symmetric, whose eigenvalues are exactly $1$ and $3$; each branch and $F$
are strongly convex with modulus $1$ (Euclidean: $F-\frac12\|x\|^2$ convex); $F(-1/2,0)=-1/4$, every
value is $\ge-1/4$, and only $(-1/2,0)$ attains it. -/
theorem rank_loss_curvature :
    (∀ i : Fin 2, ContDiff ℝ ⊤ (AffineRankLoss.branch i) ∧
      (∀ x, RadialHessian.matrix (AffineRankLoss.branch i) x = AffineRankLoss.hessian i) ∧
      (AffineRankLoss.hessian i).IsSymm ∧
      (∀ r : ℝ, (∃ v : Vec 2, v ≠ 0 ∧ (AffineRankLoss.hessian i) *ᵥ v = r • v) ↔ r = 1 ∨ r = 3) ∧
      FixedNormal.EuclideanStrongConvexOn Set.univ 1 (AffineRankLoss.branch i)) ∧
    FixedNormal.EuclideanStrongConvexOn Set.univ 1 AffineRankLoss.objective ∧
    AffineRankLoss.objective ![-1 / 2, 0] = -1 / 4 ∧ (∀ x, -1 / 4 ≤ AffineRankLoss.objective x) ∧
    (∀ x, AffineRankLoss.objective x = -1 / 4 → x = ![-1 / 2, 0]) := by
  obtain ⟨hb, ho⟩ := AffineRankLoss.rankLossCurvature
  exact ⟨fun i => ⟨(hb i).1, (hb i).2.2.1, (hb i).2.2.2.1, (hb i).2.2.2.2, (hb i).2.1⟩, ho,
    AffineRankLoss.unique_minimum⟩

/-- Item `C/08_A/prose/019` (`companion/chapters/08_A.tex:41`): "At $(0,t)$, $t\ne0$, the
active gradients are $(1+t,2t)$ and $(1-t,2t)$, giving $\gamma(0,t)=2|t|$." Both branches are
active there, with these gradients, $\partial F(0,t)$ is their convex hull, and
$\gamma(0,t)=2|t|$. -/
theorem vertical_axis (t : ℝ) (ht : t ≠ 0) :
    ConvexSubdifferential.activeIndices AffineRankLoss.objective AffineRankLoss.branch ![0, t] =
        Finset.univ ∧
      AffineRankLoss.branchGradient ![0, t] 0 = ![1 + t, 2 * t] ∧
      AffineRankLoss.branchGradient ![0, t] 1 = ![1 - t, 2 * t] ∧
      subdifferential AffineRankLoss.objective ![0, t] =
        convexHull ℝ (Set.range (AffineRankLoss.branchGradient ![0, t])) ∧
      AffineDistance.objectiveDistance AffineRankLoss.objective ![0, t] = 2 * |t| := by
  have hz : (![0, t] : Vec 2) 0 * (![0, t] : Vec 2) 1 = 0 := by simp
  refine ⟨AffineRankLoss.all_active_of_product_zero _ hz, ?_, ?_,
    AffineRankLoss.axis_subdifferential _ hz, AffineRankLoss.actual_vertical_distance ht⟩
  · ext i
    fin_cases i <;> simp [AffineRankLoss.branchGradient]
  · ext i
    fin_cases i <;> simp [AffineRankLoss.branchGradient]

/-- The gradient of the rank-loss objective at $0$ is $(1,0)$:
$F(x)-F(0)-x_0=x_0^2+x_1^2+|x_0x_1|\le3\|x\|_\infty^2$. -/
theorem rankLoss_hasGradient_origin :
    HasFDerivAt AffineRankLoss.objective (gradientFunctional ![1, 0]) (0 : Vec 2) := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hball : ∀ᶠ h : Vec 2 in 𝓝 0, ‖h‖ ≤ c / 3 := by
    filter_upwards [Metric.closedBall_mem_nhds (0 : Vec 2) (by positivity : (0 : ℝ) < c / 3)]
      with h hh
    simpa [Metric.mem_closedBall, dist_zero_right] using hh
  filter_upwards [hball] with h hh
  have h0 : |h 0| ≤ ‖h‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm h 0
  have h1 : |h 1| ≤ ‖h‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm h 1
  have hval : AffineRankLoss.objective (0 + h) - AffineRankLoss.objective 0 -
      gradientFunctional ![1, 0] h = h 0 ^ 2 + h 1 ^ 2 + |h 0 * h 1| := by
    simp [AffineRankLoss.objective, gradientFunctional_apply, dot, Fin.sum_univ_two]
    ring
  rw [hval, Real.norm_eq_abs]
  have hnn : 0 ≤ h 0 ^ 2 + h 1 ^ 2 + |h 0 * h 1| := by positivity
  rw [abs_of_nonneg hnn, abs_mul]
  have hN := norm_nonneg h
  have ha0 := abs_nonneg (h 0)
  have ha1 := abs_nonneg (h 1)
  have hsq0 : h 0 ^ 2 = |h 0| ^ 2 := (sq_abs _).symm
  have hsq1 : h 1 ^ 2 = |h 1| ^ 2 := (sq_abs _).symm
  rw [hsq0, hsq1]
  have hb : |h 0| ^ 2 + |h 1| ^ 2 + |h 0| * |h 1| ≤ 3 * ‖h‖ ^ 2 := by
    nlinarith [mul_le_mul h0 h1 ha1 hN, mul_le_mul h0 h0 ha0 hN, mul_le_mul h1 h1 ha1 hN]
  have hc3 : 3 * ‖h‖ ^ 2 ≤ c * ‖h‖ := by nlinarith
  linarith

/-- Item `C/08_A/prose/020` (`companion/chapters/08_A.tex:41`): "At zero the gradient is
$(1,0)$, so $\gamma(0,0)=1$." -/
theorem origin_point :
    HasFDerivAt AffineRankLoss.objective (gradientFunctional ![1, 0]) (0 : Vec 2) ∧
      AffineDistance.objectiveDistance AffineRankLoss.objective 0 = 1 :=
  ⟨rankLoss_hasGradient_origin, AffineRankLoss.actual_origin_distance⟩

/-- Item `C/08_A/prose/021` (`companion/chapters/08_A.tex:41`): "On the other switching axis
$\gamma(u,0)=|1+2u|$, vanishing only at the optimizer." -/
theorem horizontal_axis (u : ℝ) :
    AffineDistance.objectiveDistance AffineRankLoss.objective ![u, 0] = |1 + 2 * u| ∧
      (AffineDistance.objectiveDistance AffineRankLoss.objective ![u, 0] = 0 ↔
        (![u, 0] : Vec 2) = ![-1 / 2, 0]) := by
  refine ⟨AffineRankLoss.actual_horizontal_distance u, ?_⟩
  rw [rankLoss_gamma, AffineRankLoss.actual_horizontal_distance u, abs_eq_zero]
  constructor
  · intro h
    have hu : u = -1 / 2 := by linarith
    rw [hu]
  · intro h
    have hu := congrFun h 0
    simp at hu
    rw [hu]
    norm_num

/-- At a point where a finite convex $F$ is differentiable with gradient $g$, $p$ is affine
critical iff $g=0$. -/
theorem affineCritical_iff_gradient_zero {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ Set.univ F)
    {p g : Vec n} (hg : HasFDerivAt F (gradientFunctional g) p) :
    IsAffineCritical F p ↔ g = 0 := by
  have hs := subdifferential_eq_singleton_of_hasFDerivAt hF hg
  constructor
  · intro ha
    have h0 := affineCorrectAt_of_hasFDerivAt hF hg ha
    rw [hs] at h0
    exact (Set.mem_singleton_iff.mp h0).symm
  · intro h0
    apply affineCritical_of_zero_mem
    rw [hs, h0]
    exact Set.mem_singleton 0

/-- Item `C/08_A/prose/022` (`companion/chapters/08_A.tex:41`): "Smooth points are affine
critical only when stationary." At every point where the rank-loss objective is differentiable
with gradient $g$: affine critical iff $g=0$. -/
theorem smooth_points_affine_critical (p g : Vec 2)
    (hg : HasFDerivAt AffineRankLoss.objective (gradientFunctional g) p) :
    IsAffineCritical AffineRankLoss.objective p ↔ g = 0 :=
  affineCritical_iff_gradient_zero AffineRankLoss.objective_convex hg

/-- Item `C/08_A/prose/023` (`companion/chapters/08_A.tex:41`): "Thus \eqref{A:AC} holds
globally, but $\gamma(0,t)\to0$ while the objective gap tends to $1/4$." -/
theorem ac_global_and_gap :
    (∀ x, AffineCorrectAt AffineRankLoss.objective x) ∧
      Tendsto (fun t : ℝ => AffineDistance.objectiveDistance AffineRankLoss.objective ![0, t])
        (𝓝[≠] 0) (𝓝 0) ∧
      Tendsto (fun t : ℝ =>
          AffineRankLoss.objective ![0, t] - AffineRankLoss.objective ![-1 / 2, 0])
        (𝓝[≠] 0) (𝓝 (1 / 4)) :=
  ⟨AffineRankLoss.globally_affine_correct, AffineRankLoss.vertical_distance_tendsto_zero,
    AffineRankLoss.vertical_positive_gap_limit⟩

/-- Item `C/08_A/prose/017` (`companion/chapters/08_A.tex:34`): "Pointwise nonvanishing plus
compactness does not establish it when ranks change." For the rank-loss objective ($F_*=-1/4$):
$\gamma(p)>0$ at every point with $F(p)>F_*$, every band $\{F_*+\eta\le F\le b\}$ is compact, yet
the
condition `PositiveGapOnBands` fails (on the band $\{-1/8\le F\le1\}$ the points $(0,t)$ have
$\gamma(0,t)=2|t|\to0$). -/
theorem rank_loss_no_positive_minimum :
    (∀ p, -1 / 4 < AffineRankLoss.objective p →
        0 < AffineDistance.objectiveDistance AffineRankLoss.objective p) ∧
      (∀ η b : ℝ, IsCompact {x | -1 / 4 + η ≤ AffineRankLoss.objective x ∧
        AffineRankLoss.objective x ≤ b}) ∧
      ¬ PositiveGapOnBands AffineRankLoss.objective (-1 / 4) := by
  have hmin := AffineRankLoss.unique_minimum
  have hpos : ∀ p, -1 / 4 < AffineRankLoss.objective p →
      0 < AffineDistance.objectiveDistance AffineRankLoss.objective p := by
    intro p hp
    apply (AffineDistance.objectiveDistance_pos_iff AffineRankLoss.objective_convex p).mpr
    intro ha
    have h0 := zero_mem_iff_global_minimum.mp (AffineRankLoss.globally_affine_correct p ha)
      ![-1 / 2, 0]
    rw [hmin.1] at h0
    linarith
  have hcpt : ∀ η b : ℝ, IsCompact {x | -1 / 4 + η ≤ AffineRankLoss.objective x ∧
      AffineRankLoss.objective x ≤ b} := by
    intro η b
    have hK := Localization.sublevel_compact AffineRankLoss.objective_convex ![-1 / 2, 0]
      (fun x => by rw [hmin.1]; exact hmin.2.1 x)
      (fun x hx => hmin.2.2 x (by rw [hx, hmin.1])) b
    have hcl : IsClosed {x | -1 / 4 + η ≤ AffineRankLoss.objective x ∧
        AffineRankLoss.objective x ≤ b} :=
      (isClosed_le continuous_const AffineRankLoss.objective_continuous).inter
        (isClosed_le AffineRankLoss.objective_continuous continuous_const)
    exact hK.of_isClosed_subset hcl (fun x hx => hx.2)
  refine ⟨hpos, hcpt, fun h => ?_⟩
  have hne : {x | -1 / 4 + 1 / 8 ≤ AffineRankLoss.objective x ∧
      AffineRankLoss.objective x ≤ 1}.Nonempty :=
    ⟨0, by norm_num [AffineRankLoss.objective]⟩
  obtain ⟨p, _, hp, hle⟩ := h (1 / 8) 1 (by norm_num) (hcpt _ _) hne
  set γ := AffineDistance.objectiveDistance AffineRankLoss.objective p
  set t := min (γ / 4) (1 / 2) with ht
  have htpos : 0 < t := lt_min (by positivity) (by norm_num)
  have ht2 : t ≤ 1 / 2 := min_le_right _ _
  have htγ : t ≤ γ / 4 := min_le_left _ _
  have hF0t : AffineRankLoss.objective ![0, t] = t ^ 2 := by
    simp [AffineRankLoss.objective]
  have hq : (![0, t] : Vec 2) ∈ {x | -1 / 4 + 1 / 8 ≤ AffineRankLoss.objective x ∧
      AffineRankLoss.objective x ≤ 1} := by
    constructor
    · show -1 / 4 + 1 / 8 ≤ AffineRankLoss.objective ![0, t]
      rw [hF0t]
      nlinarith
    · show AffineRankLoss.objective ![0, t] ≤ 1
      rw [hF0t]
      nlinarith
  have hγq := hle _ hq
  rw [rankLoss_gamma, AffineRankLoss.actual_vertical_distance htpos.ne', abs_of_pos htpos] at hγq
  linarith

/-- Item `C/08_A/prose/025` (`companion/chapters/08_A.tex:43`): "A sufficiently small
neighborhood of its actual optimizer excludes the rank-loss point." The rank loss happens along the
axis $\{u=0\}$ at the origin ($\gamma(0,t)\to0\ne\gamma(0,0)$); the neighborhood
$\{u<-1/4\}$ of the optimizer $(-1/2,0)$ contains no point of that axis. -/
theorem rank_loss_point_excluded :
    ∃ U ∈ 𝓝 (![-1 / 2, 0] : Vec 2), (0 : Vec 2) ∉ U ∧ ∀ p ∈ U, p 0 ≠ 0 := by
  have ho : IsOpen {x : Vec 2 | x 0 < -1 / 4} := isOpen_lt (continuous_apply 0) continuous_const
  refine ⟨{x : Vec 2 | x 0 < -1 / 4}, ho.mem_nhds (by norm_num), by simp, fun p hp => ?_⟩
  have : p 0 < -1 / 4 := hp
  linarith

/-! ### Section "Nondegenerate smooth maxima give local affine-critical correctness" (lines 49-76)

The setting of the section: $F=\max_{i\le m}f_i$ (`hmax : ∀ x, IsGreatest (Set.range fun i => f i x)
(F x)`), convex $C^1$ branches, a minimizer $x_*$. $I_*$ is `activeIndices F f xstar`, enumerated by
`activeIndexMap F f xstar : Fin (card I_*) → Fin m`; $\nabla f_i$ is `coordinateGradient (f i)`. The
active gradients at $p$ are `fun i => coordinateGradient (f (activeIndexMap F f xstar i)) p`. -/

/-- A pointwise maximum of convex functions is convex. -/
theorem max_convex {n m : ℕ} {F : Vec n → ℝ} {f : Fin m → Vec n → ℝ}
    (hmax : ∀ x, IsGreatest (Set.range fun i => f i x) (F x))
    (hconv : ∀ i, ConvexOn ℝ Set.univ (f i)) : ConvexOn ℝ Set.univ F := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  obtain ⟨j, hj⟩ := (hmax (a • x + b • y)).1
  have hjx := (hmax x).2 (Set.mem_range_self j)
  have hjy := (hmax y).2 (Set.mem_range_self j)
  rw [← hj]
  calc f j (a • x + b • y) ≤ a • f j x + b • f j y :=
        (hconv j).2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab
    _ ≤ a • F x + b • F y := by
        simp only [smul_eq_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left hjx ha) (mul_le_mul_of_nonneg_left hjy hb)

/-- A $C^1$ function has its coordinate gradient as derivative everywhere. -/
theorem c1_hasGradient {n : ℕ} {f : Vec n → ℝ} (hf : ContDiff ℝ 1 f) (p : Vec n) :
    HasFDerivAt f (gradientFunctional (coordinateGradient f p)) p :=
  hasFDerivAt_coordinateGradient ((hf.differentiable (by norm_num)) p)

/-- The augmented matrix $A$ with columns $(g_j,1)$: rows $0,\dots,n-1$ carry the vectors $g_j$
and the last row carries the ones (as in the text). -/
def augmentedLast {n m : ℕ} (g : Fin m → Vec n) : Matrix (Fin (n + 1)) (Fin m) ℝ :=
  fun i j => Fin.lastCases (1 : ℝ) (fun k => g j k) i

/-- The right-hand side $(0,\dots,0,1)^T$. -/
def lastTarget (n : ℕ) : Vec (n + 1) := Pi.single (Fin.last n) 1

theorem augmentedLast_mulVec_last {n m : ℕ} (g : Fin m → Vec n) (w : Vec m) :
    (augmentedLast g *ᵥ w) (Fin.last n) = ∑ j, w j := by
  simp [augmentedLast, Matrix.mulVec, dotProduct]

theorem augmentedLast_mulVec_castSucc {n m : ℕ} (g : Fin m → Vec n) (w : Vec m) (k : Fin n) :
    (augmentedLast g *ᵥ w) k.castSucc = (∑ j, w j • g j) k := by
  simp [augmentedLast, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

/-- $A\lambda=(0,\dots,0,1)^T$ iff $\sum_j\lambda_j=1$ and $\sum_j\lambda_jg_j=0$: the solutions are
exactly the affine coefficients representing $0$. -/
theorem augmentedLast_equation_iff {n m : ℕ} (g : Fin m → Vec n) (w : Vec m) :
    augmentedLast g *ᵥ w = lastTarget n ↔ (∑ j, w j) = 1 ∧ (∑ j, w j • g j) = 0 := by
  constructor
  · intro he
    refine ⟨?_, ?_⟩
    · have h := congrFun he (Fin.last n)
      rwa [augmentedLast_mulVec_last, lastTarget, Pi.single_eq_same] at h
    · ext k
      have h := congrFun he k.castSucc
      rwa [augmentedLast_mulVec_castSucc, lastTarget,
        Pi.single_eq_of_ne (Fin.castSucc_lt_last k).ne] at h
  · rintro ⟨hw, hg⟩
    ext i
    refine Fin.lastCases ?_ (fun k => ?_) i
    · rw [augmentedLast_mulVec_last, lastTarget, Pi.single_eq_same, hw]
    · rw [augmentedLast_mulVec_castSucc, lastTarget,
        Pi.single_eq_of_ne (Fin.castSucc_lt_last k).ne, hg, Pi.zero_apply]

theorem augmentedLast_eq_zero_iff {n m : ℕ} (g : Fin m → Vec n) (w : Vec m) :
    augmentedLast g *ᵥ w = 0 ↔ (∑ j, w j) = 0 ∧ (∑ j, w j • g j) = 0 := by
  constructor
  · intro he
    refine ⟨?_, ?_⟩
    · have h := congrFun he (Fin.last n)
      rwa [augmentedLast_mulVec_last] at h
    · ext k
      have h := congrFun he k.castSucc
      rwa [augmentedLast_mulVec_castSucc] at h
  · rintro ⟨hw, hg⟩
    ext i
    refine Fin.lastCases ?_ (fun k => ?_) i
    · rw [augmentedLast_mulVec_last, hw, Pi.zero_apply]
    · rw [augmentedLast_mulVec_castSucc, hg, Pi.zero_apply, Pi.zero_apply]

/-- Affine independence of the $g_j$ is full column rank of $A$. -/
theorem affineIndependent_iff_augmentedLast_injective {n m : ℕ} (g : Fin m → Vec n) :
    AffineIndependent ℝ g ↔ Function.Injective (augmentedLast g).mulVec := by
  rw [AffineBarycentric.affineIndependent_iff_augmented_injective]
  constructor
  · intro h u v huv
    apply h
    have hz : augmentedLast g *ᵥ (u - v) = 0 := by rw [Matrix.mulVec_sub, huv, sub_self]
    obtain ⟨h1, h2⟩ := (augmentedLast_eq_zero_iff g (u - v)).mp hz
    have h3 := (AffineBarycentric.augmented_mulVec_eq_zero_iff g (u - v)).mpr ⟨h1, h2⟩
    rw [Matrix.mulVec_sub] at h3
    exact sub_eq_zero.mp h3
  · intro h u v huv
    apply h
    have hz : AffineBarycentric.augmented g *ᵥ (u - v) = 0 := by
      rw [Matrix.mulVec_sub, huv, sub_self]
    obtain ⟨h1, h2⟩ := (AffineBarycentric.augmented_mulVec_eq_zero_iff g (u - v)).mp hz
    have h3 := (augmentedLast_eq_zero_iff g (u - v)).mpr ⟨h1, h2⟩
    rw [Matrix.mulVec_sub] at h3
    exact sub_eq_zero.mp h3

theorem augmentedLast_continuousAt {X : Type*} [TopologicalSpace X] {n m : ℕ}
    (g : X → Fin m → Vec n) (x : X) (hc : ∀ j, ContinuousAt (fun p => g p j) x) :
    ContinuousAt (fun p => augmentedLast (g p)) x := by
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp only [augmentedLast, Fin.lastCases_last]
    exact continuousAt_const
  · simp only [augmentedLast, Fin.lastCases_castSucc]
    exact (continuous_apply k).continuousAt.comp (hc j)

/-- Item `C/08_A/prose/026` (`companion/chapters/08_A.tex:51-56`), with its display
`C/08_A/disp/005`: "Let $F=\max_{i\le m}f_i$ with convex $C^1$ branches and a minimizer $x_*$.
Restrict to $I_*$, the active branches there; inactive branches have positive gaps and disappear in
a sufficiently small neighborhood. Suppose the active gradients are affinely independent and admit
strictly positive coefficients $\lambda_i^*>0$, $\sum_{i\in I_*}\lambda_i^*=1$,
$\sum_{i\in I_*}\lambda_i^*\nabla f_i(x_*)=0$. Then \eqref{A:AC} holds near $x_*$." Also: the
inactive branches have $f_i(x_*)<F(x_*)$ and near $x_*$ every active index is in $I_*$.
(Library: `finite_C1_max_neighborhood_gap`, which needs neither convex branches nor that $x_*$
minimizes.) -/
theorem local_affine_correctness {n m : ℕ} (F : Vec n → ℝ) (f : Fin m → Vec n → ℝ)
    (hmax : ∀ x, IsGreatest (Set.range fun i => f i x) (F x))
    (hconv : ∀ i, ConvexOn ℝ Set.univ (f i)) (hC1 : ∀ i, ContDiff ℝ 1 (f i))
    (xstar : Vec n) (_hmin : ∀ x, F xstar ≤ F x)
    (hind : AffineIndependent ℝ
      (fun i => coordinateGradient (f (activeIndexMap F f xstar i)) xstar))
    (lam : Vec (activeIndices F f xstar).card) (hpos : ∀ i, 0 < lam i) (hsum : ∑ i, lam i = 1)
    (hzero : ∑ i, lam i • coordinateGradient (f (activeIndexMap F f xstar i)) xstar = 0) :
    (∀ i, i ∉ activeIndices F f xstar → f i xstar < F xstar) ∧
      (∀ᶠ p in 𝓝 xstar, activeIndices F f p ⊆ activeIndices F f xstar) ∧
      ∀ᶠ p in 𝓝 xstar, AffineCorrectAt F p := by
  have hF := max_convex hmax hconv
  have hrep : LocalFiniteMax F f xstar := Eventually.of_forall (fun z => hmax z)
  refine ⟨fun i hi => lt_of_le_of_ne ((hmax xstar).2 (Set.mem_range_self i))
      (fun he => hi (mem_activeIndices.mpr he)),
    activeIndices_eventually_subset (convex_continuous hF).continuousAt
      (fun i => (hC1 i).continuous.continuousAt) hrep, ?_⟩
  obtain ⟨V, hVo, hxV, hV, -⟩ := AffineDistance.finite_C1_max_neighborhood_gap hF isOpen_univ
    xstar (Set.mem_univ _) (fun i => (hC1 i).contDiffOn) hrep hind lam hpos hsum hzero
  filter_upwards [hVo.mem_nhds hxV] with p hp
  intro ha
  exact zero_mem_iff_global_minimum.mpr ((hV p hp).2.mp ha)

/-- Item `C/08_A/disp/006` (`companion/chapters/08_A.tex:60-62`), in the proof of the local
correctness statement (standing assumptions: those of `local_affine_correctness`, and
$A(p)$ the matrix with columns $(\nabla f_i(p),1)$, $i\in I_*$, as a variable with its defining
equation): "At an affine-critical point $p$, extend the affine coefficients of its active gradients
by zero on missing indices. They solve $A(p)\lambda=(0,\dots,0,1)^T$." The solutions of the system
are exactly the affine coefficients representing $0$; and at every affine-critical $p$ near $x_*$
there are such coefficients vanishing on every index of $I_*$ not active at $p$. -/
theorem zero_extension_solves {n m : ℕ} (F : Vec n → ℝ) (f : Fin m → Vec n → ℝ)
    (hmax : ∀ x, IsGreatest (Set.range fun i => f i x) (F x))
    (hconv : ∀ i, ConvexOn ℝ Set.univ (f i)) (hC1 : ∀ i, ContDiff ℝ 1 (f i))
    (xstar : Vec n) (_hmin : ∀ x, F xstar ≤ F x)
    (_hind : AffineIndependent ℝ
      (fun i => coordinateGradient (f (activeIndexMap F f xstar i)) xstar))
    (lam : Vec (activeIndices F f xstar).card) (_hpos : ∀ i, 0 < lam i) (_hsum : ∑ i, lam i = 1)
    (_hzero : ∑ i, lam i • coordinateGradient (f (activeIndexMap F f xstar i)) xstar = 0)
    (A : Vec n → Matrix (Fin (n + 1)) (Fin (activeIndices F f xstar).card) ℝ)
    (hA : ∀ p, A p = augmentedLast
      (fun i => coordinateGradient (f (activeIndexMap F f xstar i)) p)) :
    (∀ (p : Vec n) (w : Vec (activeIndices F f xstar).card), A p *ᵥ w = lastTarget n ↔
        (∑ i, w i) = 1 ∧
          (∑ i, w i • coordinateGradient (f (activeIndexMap F f xstar i)) p) = 0) ∧
      ∀ᶠ p in 𝓝 xstar, IsAffineCritical F p →
        ∃ w : Vec (activeIndices F f xstar).card, A p *ᵥ w = lastTarget n ∧
          ∀ i, f (activeIndexMap F f xstar i) p ≠ F p → w i = 0 := by
  have hF := max_convex hmax hconv
  have hrep : LocalFiniteMax F f xstar := Eventually.of_forall (fun z => hmax z)
  have hr := localFiniteMax_restrict_active (convex_continuous hF).continuousAt
    (fun i => (hC1 i).continuous.continuousAt) hrep
  refine ⟨fun p w => by rw [hA p]; exact augmentedLast_equation_iff _ w, ?_⟩
  filter_upwards [hr.eventually] with p hp
  intro ha
  set g : Fin (activeIndices F f xstar).card → Vec n :=
    fun i => coordinateGradient (f (activeIndexMap F f xstar i)) p
  have hg : ∀ i, HasFDerivAt (f (activeIndexMap F f xstar i)) (gradientFunctional (g i)) p :=
    fun i => c1_hasGradient (hC1 _) p
  have heq := subdifferential_eq_active_convexHull hF hp hg
  have h0 : (0 : Vec n) ∈ affineSpan ℝ (subdifferential F p) :=
    (isAffineCritical_iff_coordinate_affineSpan F p).mp ha
  rw [heq, affineSpan_convexHull] at h0
  obtain ⟨w, hw, hwJ⟩ := AffineBarycentric.affine_zero_subset_coefficients g _ h0
  refine ⟨w, ?_, fun i hi => hwJ i (fun hmem => hi (by simpa only [mem_activeIndices] using hmem))⟩
  rw [hA p]
  exact (augmentedLast_equation_iff g w).mpr ((AffineBarycentric.augmented_equation_iff g w).mp hw)

/-- Item `C/08_A/disp/007` (`companion/chapters/08_A.tex:64-66`), in the same proof: "Full column
rank at $x_*$ persists nearby. [...] Whenever this system is solvable, its unique solution equals
$\lambda(p)=(A(p)^TA(p))^{-1}A(p)^T(0,\dots,0,1)^T$." Near $x_*$, $A(p)$ has full column rank,
$\det(A(p)^TA(p))\ne0$, and every solution of $A(p)\lambda=(0,\dots,0,1)^T$ is this vector. -/
theorem unique_solution_formula {n m : ℕ} (F : Vec n → ℝ) (f : Fin m → Vec n → ℝ)
    (_hmax : ∀ x, IsGreatest (Set.range fun i => f i x) (F x))
    (_hconv : ∀ i, ConvexOn ℝ Set.univ (f i)) (hC1 : ∀ i, ContDiff ℝ 1 (f i))
    (xstar : Vec n) (_hmin : ∀ x, F xstar ≤ F x)
    (hind : AffineIndependent ℝ
      (fun i => coordinateGradient (f (activeIndexMap F f xstar i)) xstar))
    (lam : Vec (activeIndices F f xstar).card) (_hpos : ∀ i, 0 < lam i) (_hsum : ∑ i, lam i = 1)
    (_hzero : ∑ i, lam i • coordinateGradient (f (activeIndexMap F f xstar i)) xstar = 0)
    (A : Vec n → Matrix (Fin (n + 1)) (Fin (activeIndices F f xstar).card) ℝ)
    (hA : ∀ p, A p = augmentedLast
      (fun i => coordinateGradient (f (activeIndexMap F f xstar i)) p)) :
    ∀ᶠ p in 𝓝 xstar, Function.Injective (A p).mulVec ∧ ((A p)ᵀ * A p).det ≠ 0 ∧
      ∀ w, A p *ᵥ w = lastTarget n → w = ((A p)ᵀ * A p)⁻¹ *ᵥ ((A p)ᵀ *ᵥ lastTarget n) := by
  have hAe : A = fun p => augmentedLast
      (fun i => coordinateGradient (f (activeIndexMap F f xstar i)) p) := funext hA
  have hc : ContinuousAt A xstar := by
    rw [hAe]
    exact augmentedLast_continuousAt _ xstar (fun j =>
      AffineDistance.coordinateGradient_continuousAt_of_contDiffAt (hC1 _).contDiffAt)
  have hinj : Function.Injective (A xstar).mulVec := by
    rw [hA xstar]
    exact (affineIndependent_iff_augmentedLast_injective _).mp hind
  filter_upwards [AffineBarycentric.eventually_full_column_rank A xstar hc hinj] with p hp
  have hdet : (AffineBarycentric.gram (A p)).det ≠ 0 :=
    (AffineBarycentric.gram_posDef (A p) hp).det_pos.ne'
  refine ⟨hp, hdet, fun w hw => ?_⟩
  rw [AffineBarycentric.solution_eq_coefficients (A p) hdet (lastTarget n) w hw,
    AffineBarycentric.coefficients, AffineBarycentric.leftInverse, ← Matrix.mulVec_mulVec]
  rfl

/-- Proof of the local correctness statement, undisplayed claims of
`companion/chapters/08_A.tex:67` (not a register item): "This continuous expression equals the
strictly positive vector $\lambda^*$ at $x_*$. It remains positive nearby. No missing index can
therefore have zero coefficient, and the affine combination is a convex combination." Near $x_*$
every solution of $A(p)\lambda=(0,\dots,0,1)^T$ has all coordinates positive. -/
theorem formula_positive_near {n m : ℕ} (F : Vec n → ℝ) (f : Fin m → Vec n → ℝ)
    (hC1 : ∀ i, ContDiff ℝ 1 (f i)) (xstar : Vec n)
    (hind : AffineIndependent ℝ
      (fun i => coordinateGradient (f (activeIndexMap F f xstar i)) xstar))
    (lam : Vec (activeIndices F f xstar).card) (hpos : ∀ i, 0 < lam i) (hsum : ∑ i, lam i = 1)
    (hzero : ∑ i, lam i • coordinateGradient (f (activeIndexMap F f xstar i)) xstar = 0)
    (A : Vec n → Matrix (Fin (n + 1)) (Fin (activeIndices F f xstar).card) ℝ)
    (hA : ∀ p, A p = augmentedLast
      (fun i => coordinateGradient (f (activeIndexMap F f xstar i)) p)) :
    ∀ᶠ p in 𝓝 xstar, ∀ w, A p *ᵥ w = lastTarget n → ∀ i, 0 < w i := by
  have hAe : A = fun p => augmentedLast
      (fun i => coordinateGradient (f (activeIndexMap F f xstar i)) p) := funext hA
  have hc : ContinuousAt A xstar := by
    rw [hAe]
    exact augmentedLast_continuousAt _ xstar (fun j =>
      AffineDistance.coordinateGradient_continuousAt_of_contDiffAt (hC1 _).contDiffAt)
  have hinj : Function.Injective (A xstar).mulVec := by
    rw [hA xstar]
    exact (affineIndependent_iff_augmentedLast_injective _).mp hind
  have h0 : A xstar *ᵥ lam = lastTarget n := by
    rw [hA xstar]
    exact (augmentedLast_equation_iff _ lam).mpr ⟨hsum, hzero⟩
  filter_upwards [AffineBarycentric.positive_solutions_eventually A xstar hc hinj
    (lastTarget n) lam h0 hpos] with p hp
  exact fun w hw => (hp.2 w hw).2

/-- Item `C/08_A/prose/028` (`companion/chapters/08_A.tex:71`): "There is also local lower
semicontinuity of $\gamma$." In the setting of `local_affine_correctness`, $\gamma$ is lower
semicontinuous at every point of a neighborhood of $x_*$. -/
theorem gamma_lsc {n m : ℕ} (F : Vec n → ℝ) (f : Fin m → Vec n → ℝ)
    (hmax : ∀ x, IsGreatest (Set.range fun i => f i x) (F x))
    (hconv : ∀ i, ConvexOn ℝ Set.univ (f i)) (hC1 : ∀ i, ContDiff ℝ 1 (f i))
    (xstar : Vec n) (_hmin : ∀ x, F xstar ≤ F x)
    (hind : AffineIndependent ℝ
      (fun i => coordinateGradient (f (activeIndexMap F f xstar i)) xstar))
    (lam : Vec (activeIndices F f xstar).card) (hpos : ∀ i, 0 < lam i) (hsum : ∑ i, lam i = 1)
    (hzero : ∑ i, lam i • coordinateGradient (f (activeIndexMap F f xstar i)) xstar = 0) :
    ∀ᶠ p in 𝓝 xstar, LowerSemicontinuousAt (AffineDistance.objectiveDistance F) p := by
  have hF := max_convex hmax hconv
  obtain ⟨V, hVo, hxV, hV, -⟩ := AffineDistance.finite_C1_max_neighborhood_gap hF isOpen_univ
    xstar (Set.mem_univ _) (fun i => (hC1 i).contDiffOn) (Eventually.of_forall (fun z => hmax z))
    hind lam hpos hsum hzero
  filter_upwards [hVo.mem_nhds hxV] with p hp
  exact (hV p hp).1

/-- The active gradients are affinely independent near $x_*$ (full column rank persists). -/
theorem eventually_affineIndependent {n m : ℕ} (F : Vec n → ℝ) (f : Fin m → Vec n → ℝ)
    (hC1 : ∀ i, ContDiff ℝ 1 (f i)) (xstar : Vec n)
    (hind : AffineIndependent ℝ
      (fun i => coordinateGradient (f (activeIndexMap F f xstar i)) xstar)) :
    ∀ᶠ p in 𝓝 xstar, AffineIndependent ℝ
      (fun i => coordinateGradient (f (activeIndexMap F f xstar i)) p) := by
  have hc : ContinuousAt (fun p => AffineBarycentric.augmented
      (fun i => coordinateGradient (f (activeIndexMap F f xstar i)) p)) xstar :=
    AffineBarycentric.augmented_continuousAt _ xstar (fun j =>
      AffineDistance.coordinateGradient_continuousAt_of_contDiffAt (hC1 _).contDiffAt)
  filter_upwards [AffineBarycentric.eventually_full_column_rank _ xstar hc
    ((AffineBarycentric.affineIndependent_iff_augmented_injective _).mp hind)] with p hp
  exact (AffineBarycentric.affineIndependent_iff_augmented_injective _).mpr hp

/-- Item `C/08_A/prose/029` (`companion/chapters/08_A.tex:71`): "For each nonempty
$J\subset I_*$, the distance to the affine hull of the gradients in $J$ is continuous, because the
relevant difference Gram matrix remains nonsingular." Near $x_*$, for every nonempty
$J\subseteq I_*$
the function $q\mapsto\operatorname{dist}(0,\operatorname{aff}\{\nabla f_i(q):i\in J\})$
(`AffineDistance.subfamilyDistance`) is continuous at $p$. (The library proves it from the
Gram-inverse formula of the closest point, `affine_distance_eq_formula`.) -/
theorem subfamily_distance_continuous {n m : ℕ} (F : Vec n → ℝ) (f : Fin m → Vec n → ℝ)
    (_hmax : ∀ x, IsGreatest (Set.range fun i => f i x) (F x))
    (_hconv : ∀ i, ConvexOn ℝ Set.univ (f i)) (hC1 : ∀ i, ContDiff ℝ 1 (f i))
    (xstar : Vec n) (_hmin : ∀ x, F xstar ≤ F x)
    (hind : AffineIndependent ℝ
      (fun i => coordinateGradient (f (activeIndexMap F f xstar i)) xstar))
    (lam : Vec (activeIndices F f xstar).card) (_hpos : ∀ i, 0 < lam i) (_hsum : ∑ i, lam i = 1)
    (_hzero : ∑ i, lam i • coordinateGradient (f (activeIndexMap F f xstar i)) xstar = 0) :
    ∀ᶠ p in 𝓝 xstar, ∀ J : Finset (Fin (activeIndices F f xstar).card), J.Nonempty →
      ContinuousAt (fun q => AffineDistance.subfamilyDistance
        (fun i => coordinateGradient (f (activeIndexMap F f xstar i)) q) J) p := by
  filter_upwards [eventually_affineIndependent F f hC1 xstar hind] with p hp
  intro J hJ
  exact AffineDistance.subfamilyDistance_continuousAt
    (fun q i => coordinateGradient (f (activeIndexMap F f xstar i)) q) p J hJ
    (fun j => AffineDistance.coordinateGradient_continuousAt_of_contDiffAt (hC1 _).contDiffAt) hp

/-- Item `C/08_A/prose/030` (`companion/chapters/08_A.tex:71`): "For $p_j\to p$, pass to a
subsequence of constant active set $J\subset I(p)$." Near $x_*$, for every sequence $p_j\to p$ there
are a subsequence and a nonempty $J\subseteq I(p)$ (active indices of $I_*$ at $p$) such that the
active set at every $p_{\varphi(j)}$ is $J$. -/
theorem constant_active_subsequence {n m : ℕ} (F : Vec n → ℝ) (f : Fin m → Vec n → ℝ)
    (hmax : ∀ x, IsGreatest (Set.range fun i => f i x) (F x))
    (hconv : ∀ i, ConvexOn ℝ Set.univ (f i)) (hC1 : ∀ i, ContDiff ℝ 1 (f i))
    (xstar : Vec n) (_hmin : ∀ x, F xstar ≤ F x)
    (_hind : AffineIndependent ℝ
      (fun i => coordinateGradient (f (activeIndexMap F f xstar i)) xstar))
    (lam : Vec (activeIndices F f xstar).card) (_hpos : ∀ i, 0 < lam i) (_hsum : ∑ i, lam i = 1)
    (_hzero : ∑ i, lam i • coordinateGradient (f (activeIndexMap F f xstar i)) xstar = 0) :
    ∀ᶠ p in 𝓝 xstar, ∀ ps : ℕ → Vec n, Tendsto ps atTop (𝓝 p) →
      ∃ (φ : ℕ → ℕ) (J : Finset (Fin (activeIndices F f xstar).card)), StrictMono φ ∧
        J.Nonempty ∧ J ⊆ activeIndices F (fun i => f (activeIndexMap F f xstar i)) p ∧
        ∀ j, activeIndices F (fun i => f (activeIndexMap F f xstar i)) (ps (φ j)) = J := by
  have hF := max_convex hmax hconv
  have hrep : LocalFiniteMax F f xstar := Eventually.of_forall (fun z => hmax z)
  have hr := localFiniteMax_restrict_active (convex_continuous hF).continuousAt
    (fun i => (hC1 i).continuous.continuousAt) hrep
  filter_upwards [hr.eventually.eventually_nhds, hr.eventually] with p hpn hp
  intro ps hps
  set A : ℕ → Finset (Fin (activeIndices F f xstar).card) :=
    fun j => activeIndices F (fun i => f (activeIndexMap F f xstar i)) (ps j)
  have hsub : ∀ᶠ j in atTop, A j ⊆ activeIndices F (fun i => f (activeIndexMap F f xstar i)) p :=
    hps.eventually (activeIndices_eventually_subset (convex_continuous hF).continuousAt
      (fun i => (hC1 _).continuous.continuousAt) hp)
  have hne : ∀ᶠ j in atTop, (A j).Nonempty :=
    (hps.eventually hpn).mono fun j hj => activeIndices_nonempty hj
  have hfreq : ∃ J, ∃ᶠ j in atTop, A j = J := by
    by_contra hcon
    push_neg at hcon
    have hall : ∀ᶠ j in atTop, ∀ J, A j ≠ J :=
      Filter.eventually_all.mpr fun J => Filter.not_frequently.mp (hcon J)
    obtain ⟨j, hj⟩ := hall.exists
    exact hj _ rfl
  obtain ⟨J, hJ⟩ := hfreq
  obtain ⟨φ, hφ, hP⟩ :=
    Filter.extraction_of_frequently_atTop ((hJ.and_eventually hsub).and_eventually hne)
  refine ⟨φ, J, hφ, ?_, ?_, fun j => (hP j).1.1⟩
  · rw [← (hP 0).1.1]
    exact (hP 0).2
  · rw [← (hP 0).1.1]
    exact (hP 0).1.2

/-- Item `C/08_A/disp/008` (`companion/chapters/08_A.tex:72-74`): for $p_j\to p$ with constant
active set $J\subseteq I(p)$,
\[ \lim\gamma(p_j)=\operatorname{dist}(0,\operatorname{aff}\{\nabla f_i(p):i\in J\})\ge\gamma(p). \]
In the setting of `local_affine_correctness`, for every $p$ near $x_*$. -/
theorem limit_along_constant_active_set {n m : ℕ} (F : Vec n → ℝ) (f : Fin m → Vec n → ℝ)
    (hmax : ∀ x, IsGreatest (Set.range fun i => f i x) (F x))
    (hconv : ∀ i, ConvexOn ℝ Set.univ (f i)) (hC1 : ∀ i, ContDiff ℝ 1 (f i))
    (xstar : Vec n) (_hmin : ∀ x, F xstar ≤ F x)
    (hind : AffineIndependent ℝ
      (fun i => coordinateGradient (f (activeIndexMap F f xstar i)) xstar))
    (lam : Vec (activeIndices F f xstar).card) (_hpos : ∀ i, 0 < lam i) (_hsum : ∑ i, lam i = 1)
    (_hzero : ∑ i, lam i • coordinateGradient (f (activeIndexMap F f xstar i)) xstar = 0) :
    ∀ᶠ p in 𝓝 xstar, ∀ (ps : ℕ → Vec n) (J : Finset (Fin (activeIndices F f xstar).card)),
      Tendsto ps atTop (𝓝 p) → J.Nonempty →
      J ⊆ activeIndices F (fun i => f (activeIndexMap F f xstar i)) p →
      (∀ j, activeIndices F (fun i => f (activeIndexMap F f xstar i)) (ps j) = J) →
      Tendsto (fun j => AffineDistance.objectiveDistance F (ps j)) atTop
          (𝓝 (AffineDistance.subfamilyDistance
            (fun i => coordinateGradient (f (activeIndexMap F f xstar i)) p) J)) ∧
        AffineDistance.subfamilyDistance
            (fun i => coordinateGradient (f (activeIndexMap F f xstar i)) p) J ≥
          AffineDistance.objectiveDistance F p := by
  have hF := max_convex hmax hconv
  have hrep : LocalFiniteMax F f xstar := Eventually.of_forall (fun z => hmax z)
  have hr := localFiniteMax_restrict_active (convex_continuous hF).continuousAt
    (fun i => (hC1 i).continuous.continuousAt) hrep
  set g : Vec n → Fin (activeIndices F f xstar).card → Vec n :=
    fun q i => coordinateGradient (f (activeIndexMap F f xstar i)) q
  have hgrad : ∀ q i, HasFDerivAt (f (activeIndexMap F f xstar i)) (gradientFunctional (g q i)) q :=
    fun q i => c1_hasGradient (hC1 _) q
  filter_upwards [hr.eventually.eventually_nhds, hr.eventually,
    eventually_affineIndependent F f hC1 xstar hind] with p hpn hp hpind
  intro ps J hps hJ hJp hconst
  have hcont : ContinuousAt (fun q => AffineDistance.subfamilyDistance (g q) J) p :=
    AffineDistance.subfamilyDistance_continuousAt g p J hJ
      (fun j => AffineDistance.coordinateGradient_continuousAt_of_contDiffAt (hC1 _).contDiffAt)
      hpind
  refine ⟨?_, ?_⟩
  · have hlim := hcont.tendsto.comp hps
    refine hlim.congr' ?_
    filter_upwards [hps.eventually hpn] with j hj
    simp only [Function.comp_apply]
    rw [AffineDistance.objectiveDistance_eq_active hF hj (hgrad (ps j)), hconst j]
  · rw [AffineDistance.objectiveDistance_eq_active hF hp (hgrad p)]
    exact AffineDistance.subfamilyDistance_antitone (g p) hJ hJp

/-- Item `C/08_A/prose/031` (`companion/chapters/08_A.tex:75`): "On a compact positive band,
local \eqref{A:AC} therefore gives a strictly positive minimum." In the setting of
`local_affine_correctness` there is a neighborhood $V$ of $x_*$ such that on every nonempty compact
$K\subseteq V$ with $F>F(x_*)$ on $K$ the function $\gamma$ attains a strictly positive minimum. -/
theorem positive_minimum_on_bands {n m : ℕ} (F : Vec n → ℝ) (f : Fin m → Vec n → ℝ)
    (hmax : ∀ x, IsGreatest (Set.range fun i => f i x) (F x))
    (hconv : ∀ i, ConvexOn ℝ Set.univ (f i)) (hC1 : ∀ i, ContDiff ℝ 1 (f i))
    (xstar : Vec n) (_hmin : ∀ x, F xstar ≤ F x)
    (hind : AffineIndependent ℝ
      (fun i => coordinateGradient (f (activeIndexMap F f xstar i)) xstar))
    (lam : Vec (activeIndices F f xstar).card) (hpos : ∀ i, 0 < lam i) (hsum : ∑ i, lam i = 1)
    (hzero : ∑ i, lam i • coordinateGradient (f (activeIndexMap F f xstar i)) xstar = 0) :
    ∃ V ∈ 𝓝 xstar, ∀ K : Set (Vec n), IsCompact K → K.Nonempty → K ⊆ V →
      (∀ p ∈ K, F xstar < F p) →
      ∃ p ∈ K, 0 < AffineDistance.objectiveDistance F p ∧
        ∀ q ∈ K, AffineDistance.objectiveDistance F p ≤ AffineDistance.objectiveDistance F q := by
  have hF := max_convex hmax hconv
  obtain ⟨V, hVo, hxV, -, hK⟩ := AffineDistance.finite_C1_max_neighborhood_gap hF isOpen_univ
    xstar (Set.mem_univ _) (fun i => (hC1 i).contDiffOn) (Eventually.of_forall (fun z => hmax z))
    hind lam hpos hsum hzero
  exact ⟨V, hVo.mem_nhds hxV, hK⟩

/-- Item `C/08_A/prose/032` (`companion/chapters/08_A.tex:75`): "This establishes visibility,
not the full transport needed in arbitrary dimension." A positive lower bound $\gamma\ge\gamma_0>0$
on a set $S$ gives the visibility condition (V) of Chapter~T there, for the field
$W(x)=a(x)a(x)^T$: $g^TW(x)g=(g^Ta(x))^2=\|a(x)\|^4=\gamma(x)^4\ge\gamma_0^4$ at every
differentiable $x\in S$ with $g=\nabla F(x)$; and $W(x)\succeq0$. (No transport is claimed.) -/
theorem gap_gives_visibility {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ Set.univ F)
    (S : Set (Vec n)) (γ₀ : ℝ) (hγ₀ : 0 < γ₀)
    (hgap : ∀ x ∈ S, γ₀ ≤ AffineDistance.objectiveDistance F x) :
    ∀ x ∈ S,
      (outer (WithLp.equiv 2 (Fin n → ℝ) (canonicalVector hF x))
        (WithLp.equiv 2 (Fin n → ℝ) (canonicalVector hF x))).PosSemidef ∧
      ∀ g : Vec n, HasFDerivAt F (gradientFunctional g) x →
        dot g (outer (WithLp.equiv 2 (Fin n → ℝ) (canonicalVector hF x))
          (WithLp.equiv 2 (Fin n → ℝ) (canonicalVector hF x)) *ᵥ g) ≥ γ₀ ^ 4 := by
  intro x hx
  set a : Vec n := WithLp.equiv 2 (Fin n → ℝ) (canonicalVector hF x)
  refine ⟨by simpa only [one_smul] using SmoothSubspace.scaled_outer_posSemidef a 1 zero_le_one,
    fun g hg => ?_⟩
  have hgsub : g ∈ subdifferential F x := convex_supporting_inequality hF hg
  have hpair : dot g a = AffineDistance.objectiveDistance F x ^ 2 := by
    rw [← euclidean_pairing_eq_dot]
    have he : euclideanVector a = canonicalVector hF x := rfl
    rw [he, canonicalVector_pairing hF x g hgsub, AffineDistance.objectiveDistance,
      affine_distance_eq_norm hF x]
  have hE : dot g (outer a a *ᵥ g) = (dot g a) ^ 2 := by
    rw [dot_comm' g a]
    exact EnergyIdentities.energy_outer a g
  rw [hE, hpair]
  have h0 := hgap x hx
  have hγ0 : 0 ≤ γ₀ := hγ₀.le
  calc (AffineDistance.objectiveDistance F x ^ 2) ^ 2
      = AffineDistance.objectiveDistance F x ^ 4 := by ring
    _ ≥ γ₀ ^ 4 := pow_le_pow_left₀ hγ0 h0 4

/-! ### Section "Semialgebraic objectives have finitely many affine-critical values"
(lines 81-117)

"Semialgebraic" is the library's `RealAlgebraicGeometry.IsSemialgebraic` (a set defined by a
quantifier-free Boolean combination of polynomial equations and strict inequalities); a
semialgebraic objective is one with semialgebraic graph (`IsSemialgebraicObjective`,
`semialgebraic_objective_def`). The lifted graph uses the coordinates `Option (Fin n)`, with
`none` the value coordinate. -/

/-- A semialgebraic objective is one whose graph $\{(x,F(x))\}$ is semialgebraic: some Boolean
polynomial formula in the coordinates $(x,F(x))$ defines it. -/
theorem semialgebraic_objective_def {n : ℕ} (F : Vec n → ℝ) :
    RealAlgebraicGeometry.IsSemialgebraicObjective F ↔
      ∃ φ : RealAlgebraicGeometry.PolynomialFormula (Option (Fin n)),
        ∀ v : Option (Fin n) → ℝ, v none = F (fun i => v (some i)) ↔ φ.Holds v :=
  Iff.rfl

/-- Item `C/08_A/proposition/A:semialgebraic` (`companion/chapters/08_A.tex:83-89`), Proposition
`A:semialgebraic` (A low-level affine-critical gap), with its display `C/08_A/disp/009`: "If
$F:\R^n\to\R$ is finite convex and semialgebraic and attains $F_*$, then some $\epsilon>0$
satisfies $F(p)<F_*+\epsilon$, $0\in\operatorname{aff}\partial F(p)\Rightarrow0\in\partial F(p)$."
(Library: `RealAlgebraicGeometry.semialgebraic_low_affine_critical_gap`.) -/
theorem low_level_gap {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ Set.univ F)
    (hsa : RealAlgebraicGeometry.IsSemialgebraicObjective F) (Fstar : ℝ)
    (hFstar : IsLeast (Set.range F) Fstar) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p : Vec n, F p < Fstar + ε →
      (0 : Vec n) ∈ affineSpan ℝ (subdifferential F p) → (0 : Vec n) ∈ subdifferential F p := by
  obtain ⟨xs, hxs⟩ := hFstar.1
  have hmin : ∀ x, F xs ≤ F x := fun x => hxs ▸ hFstar.2 (Set.mem_range_self x)
  obtain ⟨ε, hε, h⟩ := RealAlgebraicGeometry.semialgebraic_low_affine_critical_gap hF hsa xs hmin
  exact ⟨ε, hε, fun p hp h0 => h p (by rw [hxs]; exact hp)
    ((isAffineCritical_iff_coordinate_affineSpan F p).mpr h0)⟩

/-- Item `C/08_A/disp/010` (`companion/chapters/08_A.tex:92-94`), in the proof of Proposition
`A:semialgebraic` (standing assumptions: those of the proposition): "It follows that both the
affine-critical set $C_{\rm aff}$ and its lifted graph
$\widehat C_{\rm aff}=\{(p,F(p)):p\in C_{\rm aff}\}$ are semialgebraic." The lifted graph is the
library's `affineCriticalGraph F`. -/
theorem lifted_graph {n : ℕ} {F : Vec n → ℝ} (_hF : ConvexOn ℝ Set.univ F)
    (hsa : RealAlgebraicGeometry.IsSemialgebraicObjective F) (Fstar : ℝ)
    (_hFstar : IsLeast (Set.range F) Fstar) :
    RealAlgebraicGeometry.affineCriticalGraph F =
        {v : Option (Fin n) → ℝ | v none = F (fun i => v (some i)) ∧
          IsAffineCritical F (fun i => v (some i))} ∧
      RealAlgebraicGeometry.IsSemialgebraic {x : Vec n | IsAffineCritical F x} ∧
      RealAlgebraicGeometry.IsSemialgebraic (RealAlgebraicGeometry.affineCriticalGraph F) :=
  ⟨rfl, RealAlgebraicGeometry.affineCritical_set_semialgebraic hsa,
    RealAlgebraicGeometry.affineCriticalGraph_semialgebraic hsa⟩

/-- Item `C/08_A/disp/011` (`companion/chapters/08_A.tex:100-102`), in the proof of Proposition
`A:semialgebraic`. Standing assumptions: those of the proposition, a path $p$ on $[0,1]$ inside
$C_{\rm aff}$ (a piece of the cover), an interior time $t$ at which $p$ and $F\circ p$ are
differentiable, and $g\in\partial F(p(t))$: "the supporting inequality makes
$u\mapsto F(p(u))-g^Tp(u)$ have a local minimum at $t$." -/
theorem support_local_min {n : ℕ} {F : Vec n → ℝ} (_hF : ConvexOn ℝ Set.univ F)
    (_hsa : RealAlgebraicGeometry.IsSemialgebraicObjective F) (Fstar : ℝ)
    (_hFstar : IsLeast (Set.range F) Fstar) (p : ℝ → Vec n)
    (_hpath : ∀ u ∈ Set.Icc (0 : ℝ) 1, IsAffineCritical F (p u)) (t : ℝ)
    (_ht : t ∈ Set.Ioo (0 : ℝ) 1) (_hpt : DifferentiableAt ℝ p t)
    (_hFpt : DifferentiableAt ℝ (F ∘ p) t) (g : Vec n) (hg : g ∈ subdifferential F (p t)) :
    IsLocalMin (fun u => F (p u) - dot g (p u)) t := by
  refine Filter.Eventually.of_forall fun u => ?_
  have hs := hg (p u)
  have hlin : dot g (p u - p t) = dot g (p u) - dot g (p t) := by
    simp only [dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  change F (p t) - dot g (p t) ≤ F (p u) - dot g (p u)
  linarith

/-- Item `C/08_A/disp/012` (`companion/chapters/08_A.tex:104-106`), in the proof of Proposition
`A:semialgebraic`, under the standing assumptions of display `C/08_A/disp/011` with derivatives
$p'(t)=v$ and $(F\circ p)'(t)=a$: "Differentiation gives $(F\circ p)'(t)=g^Tp'(t)$ for every
$g\in\partial F(p(t))$." -/
theorem path_derivative_pairing {n : ℕ} {F : Vec n → ℝ} (_hF : ConvexOn ℝ Set.univ F)
    (_hsa : RealAlgebraicGeometry.IsSemialgebraicObjective F) (Fstar : ℝ)
    (_hFstar : IsLeast (Set.range F) Fstar) (p : ℝ → Vec n)
    (_hpath : ∀ u ∈ Set.Icc (0 : ℝ) 1, IsAffineCritical F (p u)) (t : ℝ)
    (_ht : t ∈ Set.Ioo (0 : ℝ) 1) (v : Vec n) (hpv : HasDerivAt p v t) (a : ℝ)
    (hFa : HasDerivAt (F ∘ p) a t) :
    ∀ g ∈ subdifferential F (p t), a = dot g v :=
  fun _ hg => (AffineSupportPath.supporting_path_derivative_eq hg hpv hFa).symm

/-- Proof of Proposition `A:semialgebraic`, undisplayed conclusions of
`companion/chapters/08_A.tex:107-109` (not a register item): an affine combination of subgradients
equal to zero forces $(F\circ p)'(t)=0$; the value is constant along every piecewise smooth path in
$C_{\rm aff}$; and $F$ takes finitely many values on $C_{\rm aff}$. -/
theorem finitely_many_values {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ Set.univ F)
    (hsa : RealAlgebraicGeometry.IsSemialgebraicObjective F) :
    (∀ (p : ℝ → Vec n) (t a : ℝ) (v : Vec n), IsAffineCritical F (p t) → HasDerivAt p v t →
        HasDerivAt (F ∘ p) a t → a = 0) ∧
      (∀ (x y : Vec n)
        (P : RealAlgebraicGeometry.PiecewiseSmoothPath {z | IsAffineCritical F z} x y),
        ∀ t ∈ Set.Icc (0 : ℝ) 1, F (P.curve t) = F x) ∧
      (F '' {x | IsAffineCritical F x}).Finite :=
  ⟨fun _ _ _ _ hc hp hFp => AffineSupportPath.derivative_zero_of_affineCritical hc hp hFp,
    fun _ _ P => RealAlgebraicGeometry.semialgebraic_affine_critical_path_constant hF hsa P,
    RealAlgebraicGeometry.semialgebraic_affine_critical_values hF hsa⟩

/-- Item `C/08_A/prose/033` (`companion/chapters/08_A.tex:111`): "Here and below, a
piecewise $C^1$ path is continuous on $[0,1]$ and $C^1$ at every interior parameter outside a finite
set. No derivative at $0$ or $1$, or derivative extension across a junction, is required." -/
def PiecewiseC1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (p : ℝ → E) : Prop :=
  ContinuousOn p (Set.Icc 0 1) ∧
    ∃ S : Finset ℝ, ∀ t ∈ Set.Ioo (0 : ℝ) 1, t ∉ S → ContDiffAt ℝ 1 p t

open scoped ContDiff in
/-- The paths of the library's covers (`PiecewiseSmoothPath`, $C^\infty$ off a finite set of
interior parameters) are piecewise $C^1$. -/
theorem piecewiseC1_of_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} {x y : E} (P : RealAlgebraicGeometry.PiecewiseSmoothPath S x y) :
    PiecewiseC1 P.curve :=
  ⟨P.continuousOn, P.exceptions, fun t ht he => (P.smoothAt t ht he).of_le (by norm_cast)⟩

/-- Item `C/08_A/prose/035` (`companion/chapters/08_A.tex:113`): "The affine-critical set
also has finitely many actual semialgebraic path classes, where two points are related when a
continuous path with semialgebraic restricted graph joins them inside the set. Each class is
semialgebraic and internally connected by such paths." The relation (a path continuous on $[0,1]$
inside $C_{\rm aff}$ with semialgebraic graph over $[0,1]$) is an equivalence relation on
$C_{\rm aff}$; its classes are finitely many, semialgebraic and path connected by such paths. -/
theorem path_classes {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ Set.univ F)
    (hsa : RealAlgebraicGeometry.IsSemialgebraicObjective F) :
    (∀ x y : Vec n, RealAlgebraicGeometry.ContinuousSemialgebraicPathIn
        {z | IsAffineCritical F z} x y ↔
      ∃ c : ℝ → Vec n, ContinuousOn c (Set.Icc 0 1) ∧ c 0 = x ∧ c 1 = y ∧
        Set.MapsTo c (Set.Icc 0 1) {z | IsAffineCritical F z} ∧
        RealAlgebraicGeometry.IsSemialgebraicCurveOn c (Set.Icc 0 1)) ∧
      Equivalence (fun x y : {z : Vec n | IsAffineCritical F z} =>
        RealAlgebraicGeometry.ContinuousSemialgebraicPathIn {z | IsAffineCritical F z} x.1 y.1) ∧
      (RealAlgebraicGeometry.continuousSemialgebraicComponent {z | IsAffineCritical F z} ''
        {z | IsAffineCritical F z}).Finite ∧
      ∀ x : Vec n, RealAlgebraicGeometry.IsSemialgebraic
          (RealAlgebraicGeometry.continuousSemialgebraicComponent {z | IsAffineCritical F z} x) ∧
        RealAlgebraicGeometry.ContinuousSemialgebraicPathConnected
          (RealAlgebraicGeometry.continuousSemialgebraicComponent
            {z | IsAffineCritical F z} x) := by
  have h := RealAlgebraicGeometry.affine_critical_continuous_semialgebraic_components hF hsa
  refine ⟨fun x y => ⟨fun ⟨P⟩ => ⟨P.curve, P.continuousOn, P.source, P.target, P.mapsTo,
      P.semialgebraic⟩, fun ⟨c, h1, h2, h3, h4, h5⟩ => ⟨⟨c, h1, h2, h3, h4, h5⟩⟩⟩,
    RealAlgebraicGeometry.continuousSemialgebraicPathIn_equivalence _, h.1,
    fun x => ⟨(h.2 x).1, (h.2 x).2.1⟩⟩

open scoped ContDiff in
/-- Item `C/08_A/prose/036` (`companion/chapters/08_A.tex:113`): "Every continuous
semialgebraic path admits the finite-exception regularity just specified on the same curve; for
finite convex semialgebraic $F$, its actual composition with $F$ is likewise continuous and smooth
off finitely many interior parameters." A path continuous on $[0,1]$ with semialgebraic graph is
itself piecewise $C^1$ (indeed $C^\infty$ off a finite set), and so is $F\circ p$ (continuous on
$[0,1]$, $C^\infty$ off finitely many interior parameters). -/
theorem path_regularity {n : ℕ} :
    (∀ c : ℝ → Vec n, ContinuousOn c (Set.Icc 0 1) →
      RealAlgebraicGeometry.IsSemialgebraicCurveOn c (Set.Icc 0 1) →
      PiecewiseC1 c ∧ ∃ E : Finset ℝ, ∀ t ∈ Set.Ioo (0 : ℝ) 1, t ∉ E → ContDiffAt ℝ ∞ c t) ∧
      ∀ F : Vec n → ℝ, ConvexOn ℝ Set.univ F → RealAlgebraicGeometry.IsSemialgebraicObjective F →
        ∀ c : ℝ → Vec n, ContinuousOn c (Set.Icc 0 1) →
          RealAlgebraicGeometry.IsSemialgebraicCurveOn c (Set.Icc 0 1) →
          ContinuousOn (F ∘ c) (Set.Icc 0 1) ∧
            ∃ E : Finset ℝ, ∀ t ∈ Set.Ioo (0 : ℝ) 1, t ∉ E → ContDiffAt ℝ ∞ (F ∘ c) t := by
  refine ⟨fun c hc hs => ?_, fun F hF hsa c hc hs => ?_⟩
  · obtain ⟨E, hE⟩ := RealAlgebraicGeometry.semialgebraic_curve_smooth_except_finite hs
    exact ⟨⟨hc, E, fun t ht he => (hE t ⟨ht.1.le, ht.2.le⟩ he).of_le (by norm_cast)⟩,
      E, fun t ht he => hE t ⟨ht.1.le, ht.2.le⟩ he⟩
  · obtain ⟨-, h1, h2⟩ :=
      RealAlgebraicGeometry.convex_semialgebraic_objective_curve_piecewise_smooth hF hsa hc hs
    exact ⟨h1, h2⟩

/-- Item `C/08_A/prose/037` (`companion/chapters/08_A.tex:113`): "The objective is constant
on each class." -/
theorem classes_constant {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ Set.univ F)
    (hsa : RealAlgebraicGeometry.IsSemialgebraicObjective F) (x : Vec n) :
    ∀ p ∈ RealAlgebraicGeometry.continuousSemialgebraicComponent {z | IsAffineCritical F z} x,
      ∀ q ∈ RealAlgebraicGeometry.continuousSemialgebraicComponent {z | IsAffineCritical F z} x,
        F p = F q :=
  ((RealAlgebraicGeometry.affine_critical_continuous_semialgebraic_components hF hsa).2 x).2.2

/-- Item `C/08_A/prose/038` (`companion/chapters/08_A.tex:113`): "Ordinary topological
connected components are separately finite and semialgebraic, with constant objective value". The
connected components of $C_{\rm aff}$ are finitely many, each semialgebraic, and $F$ is constant on
each. -/
theorem topological_components {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ Set.univ F)
    (hsa : RealAlgebraicGeometry.IsSemialgebraicObjective F) :
    (connectedComponentIn {x : Vec n | IsAffineCritical F x} ''
        {x | IsAffineCritical F x}).Finite ∧
      (∀ p : Vec n, RealAlgebraicGeometry.IsSemialgebraic
        (connectedComponentIn {x | IsAffineCritical F x} p)) ∧
      ∀ x p q : Vec n, p ∈ connectedComponentIn {z | IsAffineCritical F z} x →
        q ∈ connectedComponentIn {z | IsAffineCritical F z} x → F p = F q :=
  ⟨(RealAlgebraicGeometry.semialgebraic_affine_critical_components hsa).1,
    (RealAlgebraicGeometry.semialgebraic_affine_critical_components hsa).2,
    fun _ _ _ hp hq => RealAlgebraicGeometry.semialgebraic_affine_critical_component_constant hF hsa
      hp hq⟩

/-- Item `C/08_A/prose/039` (`companion/chapters/08_A.tex:115`): "This proposition concerns
affine criticality rather than merely Clarke criticality." Every Clarke-critical point
($0\in\partial F(p)$, for convex $F$ exactly the minimizers) is affine critical; the proposition
controls all affine-critical points below the level $F_*+\epsilon$. -/
theorem clarke_implies_affine {n : ℕ} (F : Vec n → ℝ) (p : Vec n) :
    ((0 : Vec n) ∈ subdifferential F p → IsAffineCritical F p) ∧
      ((0 : Vec n) ∈ subdifferential F p ↔ ∀ z, F p ≤ F z) :=
  ⟨affineCritical_of_zero_mem, zero_mem_iff_global_minimum⟩

/-! ### Section "What remains a conjecture" (lines 121-126) -/

/-- The subspace $U_*$ of display `C/08_A/disp/013`:
$U_*=\{v:(\nabla f_i(x_*)-\nabla f_1(x_*))^Tv=0\ \forall i\in I_*\}$, where $f_1$ is a fixed
branch active at $x_*$ (the subspace does not depend on the choice). -/
def activeTangentSpace {n m : ℕ} (F : Vec n → ℝ) (f : Fin m → Vec n → ℝ) (xstar : Vec n)
    (i₁ : Fin m) : Set (Vec n) :=
  {v | ∀ i ∈ activeIndices F f xstar,
    dot (coordinateGradient (f i) xstar - coordinateGradient (f i₁) xstar) v = 0}

/-- Item `C/08_A/prose/042` (`companion/chapters/08_A.tex:122-126`), OPEN (stated without proof),
with its display `C/08_A/disp/013`: "The recorded general-dimensional conjecture concerns finite
convex $C^{2,1}$ maxima with unique minimizer, compact low sublevels, affinely independent active
gradients, positive optimal weights, and positive weighted Hessian on [$U_*$]. The proposed
conclusion is local full-BFGS convergence for arbitrary SPD initialization."

Reading: $F=\max_{i\le m}f_i$ with convex $C^2$ branches whose Hessians are Lipschitz ($C^{2,1}$),
a unique minimizer $x_*$, a compact sublevel above $F_*$, affinely independent active gradients,
weights $\lambda_i>0$ on $I_*$ (zero elsewhere) with $\sum\lambda_i=1$ and
$\sum\lambda_i\nabla f_i(x_*)=0$, and $v^T(\sum_i\lambda_i\nabla^2f_i(x_*))v>0$ for $0\ne v\in U_*$.
Conclusion: for every pair $0<c_1<c_2<1$ there is $\varepsilon>0$ such that every admissible run
with these constants and $F(x_0)<F_*+\varepsilon$, for every $H_0\succ0$, has $F(x_k)\to F_*$ and
$x_k\to x_*$ (the basin may depend on the line-search constants, not on $H_0$; the planar theorem,
Corollary `art:planar-max` of the article, even gives a basin independent of both). The hypotheses
can all hold (an example at the end of the module: one branch $x^2/2$). -/
def GeneralDimensionalConjecture : Prop :=
  ∀ (n m : ℕ) (f : Fin m → Vec n → ℝ) (F : Vec n → ℝ) (xstar : Vec n) (i₁ : Fin m)
    (lam : Fin m → ℝ),
    (∀ x, IsGreatest (Set.range fun i => f i x) (F x)) →
    (∀ i, ConvexOn ℝ Set.univ (f i)) →
    (∀ i, ContDiff ℝ 2 (f i) ∧ ∃ K : NNReal, LipschitzWith K (fderiv ℝ (fderiv ℝ (f i)))) →
    (∀ x, F xstar ≤ F x) → (∀ x, F x = F xstar → x = xstar) →
    (∃ b, F xstar < b ∧ IsCompact {x | F x ≤ b}) →
    AffineIndependent ℝ
      (fun i : (activeIndices F f xstar : Set (Fin m)) => coordinateGradient (f i) xstar) →
    i₁ ∈ activeIndices F f xstar →
    (∀ i ∈ activeIndices F f xstar, 0 < lam i) → (∀ i, i ∉ activeIndices F f xstar → lam i = 0) →
    ∑ i, lam i = 1 → ∑ i, lam i • coordinateGradient (f i) xstar = 0 →
    (∀ v ∈ activeTangentSpace F f xstar i₁, v ≠ 0 →
      0 < ∑ i, lam i * dot v (RadialHessian.matrix (f i) xstar *ᵥ v)) →
    ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ < c₂ → c₂ < 1 →
      ∃ ε : ℝ, 0 < ε ∧ ∀ R : AdmissibleBFGSRun n F, R.c₁ = c₁ → R.c₂ = c₂ →
        F (R.x 0) < F xstar + ε →
          Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) ∧ Tendsto R.x atTop (𝓝 xstar)

/-- The straightening map $\psi(u,v)=(u,v+8u^2)$ of the example below. -/
def straighten (x : Vec 2) : Vec 2 := ![x 0, x 1 + 8 * x 0 ^ 2]

/-- Its inverse $\psi^{-1}(z)=(z_1,z_2-8z_1^2)$. -/
def unstraighten (z : Vec 2) : Vec 2 := ![z 0, z 1 - 8 * z 0 ^ 2]

theorem unstraighten_straighten (x : Vec 2) : unstraighten (straighten x) = x := by
  ext i
  fin_cases i <;> simp [straighten, unstraighten]

theorem straighten_unstraighten (z : Vec 2) : straighten (unstraighten z) = z := by
  ext i
  fin_cases i <;> simp [straighten, unstraighten]

theorem straighten_contDiff : ContDiff ℝ ⊤ straighten := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · simp only [straighten]
    exact contDiff_apply ℝ ℝ 0
  · simp only [straighten]
    exact (contDiff_apply ℝ ℝ 1).add (contDiff_const.mul ((contDiff_apply ℝ ℝ 0).pow 2))

theorem unstraighten_contDiff : ContDiff ℝ ⊤ unstraighten := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · simp only [unstraighten]
    exact contDiff_apply ℝ ℝ 0
  · simp only [unstraighten]
    exact (contDiff_apply ℝ ℝ 1).sub (contDiff_const.mul ((contDiff_apply ℝ ℝ 0).pow 2))

/-- Item `C/08_A/prose/045` (`companion/chapters/08_A.tex:126`): "Straightening an active
manifold by a nonlinear coordinate change does not preserve ordinary BFGS, and cannot supply the
missing implication." Example: $F(u,v)=\max\{18u^2+v^2+v,\ 2u^2+v^2-v\}=10u^2+v^2+|v+8u^2|$
(finite and convex), whose active manifold (where both branches are active) is the parabola
$v=-8u^2$; the polynomial diffeomorphism $\psi(u,v)=(u,v+8u^2)$ straightens it into the axis
$\{z_2=0\}$. From $x_0=(1,2)$ with $H_0=I$, $\alpha_0=1/30$, the full BFGS step to
$x_1=(-1/5,11/6)$ satisfies Armijo ($c_1=1/4$) and weak Wolfe ($c_2=1/2$), with $F$ differentiable
at $x_0$ and $x_1$ and nonzero gradients $(36,5)$, $(-36/5,14/3)$; but in the coordinates
$z=\psi(x)$, for $\tilde F=F\circ\psi^{-1}$, the image step $\psi(x_1)-\psi(x_0)$ is an ascent
direction ($\nabla\tilde F(\psi(x_0))=(-44,5)$, pairing $407/30>0$), so it is not
$-\alpha H\nabla\tilde F$ for any $H\succ0$, $\alpha>0$: the image of a BFGS step is not a BFGS
step. (The second clause is a remark on proof strategy.) -/
theorem straightening_breaks_bfgs :
    ∃ (F : Vec 2 → ℝ) (ψ ψinv : Vec 2 → Vec 2) (x₀ g₀ x₁ g₁ g' : Vec 2) (H₀ : Mat 2) (α₀ : ℝ),
      (∀ x, F x = max (18 * x 0 ^ 2 + x 1 ^ 2 + x 1) (2 * x 0 ^ 2 + x 1 ^ 2 - x 1)) ∧
      ConvexOn ℝ Set.univ F ∧
      (∀ x, ψ x = ![x 0, x 1 + 8 * x 0 ^ 2]) ∧ (∀ z, ψinv z = ![z 0, z 1 - 8 * z 0 ^ 2]) ∧
      (∀ x, ψinv (ψ x) = x) ∧ (∀ z, ψ (ψinv z) = z) ∧ ContDiff ℝ ⊤ ψ ∧ ContDiff ℝ ⊤ ψinv ∧
      (∀ x, 18 * x 0 ^ 2 + x 1 ^ 2 + x 1 = 2 * x 0 ^ 2 + x 1 ^ 2 - x 1 ↔ ψ x 1 = 0) ∧
      H₀.PosDef ∧ 0 < α₀ ∧ HasFDerivAt F (gradientFunctional g₀) x₀ ∧ g₀ ≠ 0 ∧
      HasFDerivAt F (gradientFunctional g₁) x₁ ∧ g₁ ≠ 0 ∧
      x₁ = x₀ + bfgsStep H₀ g₀ α₀ ∧
      F x₁ ≤ F x₀ + (1 / 4) * dot g₀ (x₁ - x₀) ∧ dot g₁ (x₁ - x₀) ≥ (1 / 2) * dot g₀ (x₁ - x₀) ∧
      HasFDerivAt (F ∘ ψinv) (gradientFunctional g') (ψ x₀) ∧
      ∀ (H : Mat 2) (α : ℝ), H.PosDef → 0 < α → ψ x₁ ≠ ψ x₀ + bfgsStep H g' α := by
  set F : Vec 2 → ℝ :=
    fun x => max (18 * x 0 ^ 2 + x 1 ^ 2 + x 1) (2 * x 0 ^ 2 + x 1 ^ 2 - x 1) with hF
  have hFeq : ∀ x : Vec 2, 0 < x 1 + 8 * x 0 ^ 2 → F x = 18 * x 0 ^ 2 + x 1 ^ 2 + x 1 := by
    intro x hx
    simp only [hF]
    rw [max_eq_left (by linarith : 2 * x 0 ^ 2 + x 1 ^ 2 - x 1 ≤ 18 * x 0 ^ 2 + x 1 ^ 2 + x 1)]
  have hopen : IsOpen {y : Vec 2 | 0 < y 1 + 8 * y 0 ^ 2} :=
    isOpen_lt continuous_const
      ((continuous_apply 1).add (continuous_const.mul ((continuous_apply 0).pow 2)))
  have hgradF : ∀ x : Vec 2, 0 < x 1 + 8 * x 0 ^ 2 →
      HasFDerivAt F (gradientFunctional ![36 * x 0, 2 * x 1 + 1]) x := by
    intro x hx
    have h0 := (ContinuousLinearMap.proj (0 : Fin 2) : Vec 2 →L[ℝ] ℝ).hasFDerivAt (x := x)
    have h1 := (ContinuousLinearMap.proj (1 : Fin 2) : Vec 2 →L[ℝ] ℝ).hasFDerivAt (x := x)
    have hd := (((h0.mul h0).const_mul 18).add (h1.mul h1)).add h1
    simp only [ContinuousLinearMap.proj_apply] at hd
    have hbranch : HasFDerivAt (fun y : Vec 2 => 18 * (y 0 * y 0) + y 1 * y 1 + y 1)
        (gradientFunctional ![36 * x 0, 2 * x 1 + 1]) x := by
      refine hd.congr_fderiv ?_
      ext v
      simp [gradientFunctional_apply, dot, Fin.sum_univ_two]
      ring
    apply hbranch.congr_of_eventuallyEq
    filter_upwards [hopen.mem_nhds hx] with y hy
    show F y = 18 * (y 0 * y 0) + y 1 * y 1 + y 1
    rw [hFeq y hy]
    ring
  have hconv1 : ConvexOn ℝ Set.univ (fun x : Vec 2 => 18 * x 0 ^ 2 + x 1 ^ 2 + x 1) := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hb' : b = 1 - a := by linarith
    subst hb'
    nlinarith [mul_nonneg ha hb, sq_nonneg (x 0 - y 0), sq_nonneg (x 1 - y 1)]
  have hconv2 : ConvexOn ℝ Set.univ (fun x : Vec 2 => 2 * x 0 ^ 2 + x 1 ^ 2 - x 1) := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hb' : b = 1 - a := by linarith
    subst hb'
    nlinarith [mul_nonneg ha hb, sq_nonneg (x 0 - y 0), sq_nonneg (x 1 - y 1)]
  have hG : HasFDerivAt (F ∘ unstraighten) (gradientFunctional ![-44, 5])
      (straighten ![1, 2]) := by
    have hz : straighten ![1, 2] = ![1, 10] := by
      ext i
      fin_cases i <;> norm_num [straighten]
    rw [hz]
    have h0 := (ContinuousLinearMap.proj (0 : Fin 2) : Vec 2 →L[ℝ] ℝ).hasFDerivAt (x := ![1, 10])
    have h1 := (ContinuousLinearMap.proj (1 : Fin 2) : Vec 2 →L[ℝ] ℝ).hasFDerivAt (x := ![1, 10])
    have hw := h1.sub ((h0.mul h0).const_mul 8)
    have hd := (((h0.mul h0).const_mul 18).add (hw.mul hw)).add hw
    simp only [ContinuousLinearMap.proj_apply] at hd
    have hbranch : HasFDerivAt (fun z : Vec 2 => 18 * (z 0 * z 0) +
        (z 1 - 8 * (z 0 * z 0)) * (z 1 - 8 * (z 0 * z 0)) + (z 1 - 8 * (z 0 * z 0)))
        (gradientFunctional ![-44, 5]) ![1, 10] := by
      refine hd.congr_fderiv ?_
      ext v
      simp [gradientFunctional_apply, dot, Fin.sum_univ_two]
      ring
    apply hbranch.congr_of_eventuallyEq
    have hopen' : IsOpen {z : Vec 2 | 0 < z 1} := isOpen_lt continuous_const (continuous_apply 1)
    filter_upwards [hopen'.mem_nhds (show (0 : ℝ) < (![1, 10] : Vec 2) 1 by norm_num)] with z hz
    have hz' : 0 < z 1 := hz
    have hu : unstraighten z = ![z 0, z 1 - 8 * z 0 ^ 2] := rfl
    show F (unstraighten z) = 18 * (z 0 * z 0) +
      (z 1 - 8 * (z 0 * z 0)) * (z 1 - 8 * (z 0 * z 0)) + (z 1 - 8 * (z 0 * z 0))
    rw [hu, hFeq ![z 0, z 1 - 8 * z 0 ^ 2]
      (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]; linarith)]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    ring
  refine ⟨F, straighten, unstraighten, ![1, 2], ![36, 5], ![-1 / 5, 11 / 6], ![-36 / 5, 14 / 3],
    ![-44, 5], 1, 1 / 30, fun _ => rfl, hconv1.sup hconv2, fun _ => rfl, fun _ => rfl,
    unstraighten_straighten, straighten_unstraighten, straighten_contDiff, unstraighten_contDiff,
    fun x => ?_, Matrix.PosDef.one, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hG, ?_⟩
  · simp only [straighten, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
    constructor <;> intro h <;> linarith
  · convert hgradF ![1, 2] (by norm_num) using 2
    ext i
    fin_cases i <;> norm_num
  · intro h
    have := congrFun h 0
    norm_num at this
  · convert hgradF ![-1 / 5, 11 / 6] (by norm_num) using 2
    ext i
    fin_cases i <;> norm_num
  · intro h
    have := congrFun h 0
    norm_num at this
  · ext i
    fin_cases i <;> norm_num [bfgsStep]
  · rw [hFeq ![-1 / 5, 11 / 6] (by norm_num), hFeq ![1, 2] (by norm_num)]
    norm_num [dot, Fin.sum_univ_two]
  · norm_num [dot, Fin.sum_univ_two]
  · intro H α hH hα he
    have hpair : dot ![-44, 5] (straighten ![-1 / 5, 11 / 6] - straighten ![1, 2]) = 407 / 30 := by
      norm_num [dot, Fin.sum_univ_two, straighten]
    have hneg : dot ![-44, 5] (bfgsStep H ![-44, 5] α) < 0 := by
      have hpos : 0 < dot ![-44, 5] (H *ᵥ ![-44, 5]) := by
        have hne : (![-44, 5] : Vec 2) ≠ 0 := by
          intro h0
          have := congrFun h0 0
          norm_num at this
        simpa [dot, dotProduct, star_trivial] using hH.2 _ hne
      simp only [bfgsStep, dot_smul_right]
      nlinarith
    rw [he, add_sub_cancel_left] at hpair
    linarith

/-- Item `C/08_A/prose/056` (`companion/chapters/08_A.tex:139`): "Projecting an affine
combination equal to zero, whose coefficients sum to one, makes that stratum gradient zero." If a
linear map $P$ (the tangential projection) sends every $g_i$ to the same vector $r$ (the stratum
gradient) and $\sum_i\lambda_ig_i=0$ with $\sum_i\lambda_i=1$, then $r=0$. -/
theorem affine_zero_projects {n m : ℕ} (P : Vec n →ₗ[ℝ] Vec n) (g : Fin m → Vec n) (r : Vec n)
    (hP : ∀ i, P (g i) = r) (lam : Fin m → ℝ) (hsum : ∑ i, lam i = 1)
    (hzero : ∑ i, lam i • g i = 0) : r = 0 := by
  calc r = (∑ i, lam i) • r := by rw [hsum, one_smul]
    _ = ∑ i, lam i • P (g i) := by rw [Finset.sum_smul]; simp only [hP]
    _ = P (∑ i, lam i • g i) := by rw [map_sum]; simp only [map_smul]
    _ = 0 := by rw [hzero, map_zero]

/-! ### Non-vacuity -/

/-- At a differentiable point of a finite convex $F$ with gradient $g$, $\gamma=\|g\|$. -/
theorem objectiveDistance_of_gradient {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ Set.univ F)
    {x g : Vec n} (hg : HasFDerivAt F (gradientFunctional g) x) :
    AffineDistance.objectiveDistance F x = ‖euclideanVector g‖ := by
  rw [AffineDistance.objectiveDistance, range_subgradientFamily,
    subdifferential_eq_singleton_of_hasFDerivAt hF hg, Set.image_singleton,
    AffineSubspace.coe_affineSpan_singleton, Metric.infDist_singleton, dist_zero_left]

namespace Example
open BfgsCoverage.Article.Energy.Example

theorem quad_contDiff : ContDiff ℝ 1 quad := by
  unfold quad
  exact ((contDiff_apply ℝ ℝ (0 : Fin 1)).pow 2).div_const 2

theorem quad_coordinateGradient (x : Vec 1) : coordinateGradient quad x = x := by
  funext i
  fin_cases i
  simp [coordinateGradient, (quad_hasGradient x).fderiv, gradientFunctional_apply, dot]

theorem quad_zero : quad 0 = 0 := by simp [quad]

theorem quad_min : ∀ x, quad 0 ≤ quad x := fun x => by
  rw [quad_zero]
  exact quad_nonneg x

theorem quad_active : activeIndices quad (fun _ : Fin 1 => quad) 0 = Finset.univ := by
  ext i
  simp [activeIndices]

theorem quad_card : (activeIndices quad (fun _ : Fin 1 => quad) 0).card = 1 := by
  rw [quad_active, Finset.card_univ, Fintype.card_fin]

theorem quad_semialgebraic : RealAlgebraicGeometry.IsSemialgebraicObjective quad := by
  have h := RealAlgebraicGeometry.polynomial_objective_semialgebraic
    (MvPolynomial.C (1 / 2 : ℝ) * MvPolynomial.X (0 : Fin 1) ^ 2)
  have he : (fun x : Vec 1 => MvPolynomial.eval x
      (MvPolynomial.C (1 / 2 : ℝ) * MvPolynomial.X (0 : Fin 1) ^ 2)) = quad := by
    funext x
    simp [quad]
    ring
  rwa [he] at h

theorem run_tendsto : Tendsto run.x atTop (𝓝 0) := by
  apply tendsto_pi_nhds.mpr
  intro i
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

end Example

open BfgsCoverage.Article.Energy.Example in
/-- The hypotheses of the local statements of lines 49-76 (`local_affine_correctness`,
`zero_extension_solves`, `unique_solution_formula`, `gamma_lsc`, `subfamily_distance_continuous`,
`constant_active_subsequence`, `limit_along_constant_active_set`, `positive_minimum_on_bands`) can
all hold: the one-branch maximum $F=f_0=x^2/2$ on $\R$, $x_*=0$, $I_*=\{0\}$, $\lambda^*=1$ (and the
matrix $A$ is given by its defining equation). -/
example : ∃ (F : Vec 1 → ℝ) (f : Fin 1 → Vec 1 → ℝ) (xstar : Vec 1)
    (lam : Vec (activeIndices F f xstar).card),
    (∀ x, IsGreatest (Set.range fun i => f i x) (F x)) ∧ (∀ i, ConvexOn ℝ Set.univ (f i)) ∧
      (∀ i, ContDiff ℝ 1 (f i)) ∧ (∀ x, F xstar ≤ F x) ∧
      AffineIndependent ℝ (fun i => coordinateGradient (f (activeIndexMap F f xstar i)) xstar) ∧
      (∀ i, 0 < lam i) ∧ ∑ i, lam i = 1 ∧
      ∑ i, lam i • coordinateGradient (f (activeIndexMap F f xstar i)) xstar = 0 := by
  have hsub : Subsingleton (Fin (activeIndices quad (fun _ : Fin 1 => quad) 0).card) := by
    rw [Example.quad_card]
    infer_instance
  refine ⟨quad, fun _ => quad, 0, fun _ => 1, fun x => ⟨⟨0, rfl⟩, ?_⟩, fun _ => quad_convex,
    fun _ => Example.quad_contDiff, Example.quad_min, affineIndependent_of_subsingleton ℝ _,
    fun _ => one_pos, ?_, ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact le_rfl
  · simp [Example.quad_card]
  · simp [Example.quad_coordinateGradient]

open BfgsCoverage.Article.Energy.Example in
/-- The hypotheses of `cluster_values` and `cluster_reduction` can hold: the quadratic run
$x_k=2^{-k}$ stays in the compact $K=\{x^2/2\le1\}$, where (A:AC) holds (every point is
differentiable), and its cluster point $0$ is affine critical. -/
example : ∃ (F : Vec 1 → ℝ) (R : AdmissibleBFGSRun 1 F) (K : Set (Vec 1)) (p : Vec 1),
    IsCompact K ∧ (∀ k, R.x k ∈ K) ∧ (∀ q ∈ K, AffineCorrectAt F q) ∧
      MapClusterPt p atTop R.x ∧ IsAffineCritical F p := by
  refine ⟨quad, run, {x | quad x ≤ 1}, 0, quad_sublevel_compact 1, fun k => ?_,
    fun q _ => affineCorrectAt_of_hasFDerivAt quad_convex (quad_hasGradient q),
    Example.run_tendsto.mapClusterPt,
    affineCritical_of_zero_mem (zero_mem_iff_global_minimum.mpr Example.quad_min)⟩
  have h0 : quad (run.x 0) ≤ 1 := by
    show quad (pt 0) ≤ 1
    simp [quad, pt]
    norm_num
  exact (run.objective_le_initial k).trans h0

open BfgsCoverage.Article.Energy.Example in
/-- The hypotheses of Proposition `A:semialgebraic` and of the proof displays
`C/08_A/disp/011`-`disp/012` can hold: $F(x)=x^2/2$ (a polynomial, hence semialgebraic) with
$F_*=0$, the constant path $p\equiv0$ in $C_{\rm aff}=\{0\}$, $t=1/2$, $g=0$. -/
example : ∃ (F : Vec 1 → ℝ) (Fstar : ℝ) (p : ℝ → Vec 1) (t : ℝ) (v g : Vec 1) (a : ℝ),
    ConvexOn ℝ Set.univ F ∧ RealAlgebraicGeometry.IsSemialgebraicObjective F ∧
      IsLeast (Set.range F) Fstar ∧ (∀ u ∈ Set.Icc (0 : ℝ) 1, IsAffineCritical F (p u)) ∧
      t ∈ Set.Ioo (0 : ℝ) 1 ∧ DifferentiableAt ℝ p t ∧ DifferentiableAt ℝ (F ∘ p) t ∧
      g ∈ subdifferential F (p t) ∧ HasDerivAt p v t ∧ HasDerivAt (F ∘ p) a t := by
  have h0 : (0 : Vec 1) ∈ subdifferential quad 0 := zero_mem_iff_global_minimum.mpr Example.quad_min
  have hc : (quad ∘ fun _ : ℝ => (0 : Vec 1)) = fun _ => (0 : ℝ) := by
    funext u
    exact Example.quad_zero
  refine ⟨quad, 0, fun _ => 0, 1 / 2, 0, 0, 0, quad_convex, Example.quad_semialgebraic,
    quad_isLeast, fun _ _ => affineCritical_of_zero_mem h0, ⟨by norm_num, by norm_num⟩,
    differentiableAt_const _, ?_, h0, hasDerivAt_const _ _, ?_⟩
  · rw [hc]
    exact differentiableAt_const _
  · rw [hc]
    exact hasDerivAt_const _ _

open BfgsCoverage.Article.Energy.Example in
/-- The hypotheses of `gap_gives_visibility` can hold: for $F(x)=x^2/2$, $\gamma(x)=|x|$, so
$\gamma\ge1$ on $S=\{1\}$. -/
example : ∃ (F : Vec 1 → ℝ) (S : Set (Vec 1)) (γ₀ : ℝ), ConvexOn ℝ Set.univ F ∧ 0 < γ₀ ∧
    S.Nonempty ∧ ∀ x ∈ S, γ₀ ≤ AffineDistance.objectiveDistance F x := by
  refine ⟨quad, {fun _ => 1}, 1, quad_convex, one_pos, Set.singleton_nonempty _, fun x hx => ?_⟩
  rw [Set.mem_singleton_iff] at hx
  subst hx
  rw [objectiveDistance_of_gradient quad_convex (quad_hasGradient _), norm_euclideanVector_one]
  norm_num

open BfgsCoverage.Article.Energy.Example in
/-- The hypotheses of the conjecture `GeneralDimensionalConjecture` (item `C/08_A/prose/042`) can
all hold together: $n=m=1$, the single branch $f_0=F=x^2/2$ (convex, $C^2$, with constant second
derivative), the unique minimizer $x_*=0$ with compact sublevels, $I_*=\{0\}$, $i_1=0$,
$\lambda=1$; the one active gradient is affinely independent, $\lambda\nabla f_0(0)=0$, $U_*=\R$,
and the weighted Hessian is $1$. (Admissible runs of this $F$ exist: `run`.) -/
example : ∃ (n m : ℕ) (f : Fin m → Vec n → ℝ) (F : Vec n → ℝ) (xstar : Vec n) (i₁ : Fin m)
    (lam : Fin m → ℝ),
    (∀ x, IsGreatest (Set.range fun i => f i x) (F x)) ∧ (∀ i, ConvexOn ℝ Set.univ (f i)) ∧
    (∀ i, ContDiff ℝ 2 (f i) ∧ ∃ K : NNReal, LipschitzWith K (fderiv ℝ (fderiv ℝ (f i)))) ∧
    (∀ x, F xstar ≤ F x) ∧ (∀ x, F x = F xstar → x = xstar) ∧
    (∃ b, F xstar < b ∧ IsCompact {x | F x ≤ b}) ∧
    AffineIndependent ℝ
      (fun i : (activeIndices F f xstar : Set (Fin m)) => coordinateGradient (f i) xstar) ∧
    i₁ ∈ activeIndices F f xstar ∧
    (∀ i ∈ activeIndices F f xstar, 0 < lam i) ∧ (∀ i, i ∉ activeIndices F f xstar → lam i = 0) ∧
    ∑ i, lam i = 1 ∧ ∑ i, lam i • coordinateGradient (f i) xstar = 0 ∧
    (∀ v ∈ activeTangentSpace F f xstar i₁, v ≠ 0 →
      0 < ∑ i, lam i * dot v (RadialHessian.matrix (f i) xstar *ᵥ v)) := by
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : Vec 1 →L[ℝ] (Vec 1 →L[ℝ] ℝ), ∀ x v, Λ x v = x 0 * v 0 :=
    ⟨(ContinuousLinearMap.proj 0).smulRight (ContinuousLinearMap.proj 0), fun x v => by simp⟩
  have hfd : fderiv ℝ quad = fun x => Λ x := by
    funext x
    rw [(quad_hasGradient x).fderiv]
    refine ContinuousLinearMap.ext fun v => ?_
    rw [gradientFunctional_apply, hΛ]
    simp [dot, Fin.sum_univ_one]
  have hfd2 : fderiv ℝ (fderiv ℝ quad) = fun _ => Λ := by
    rw [hfd]
    funext x
    exact Λ.fderiv
  have hC2 : ContDiff ℝ 2 quad := by
    unfold quad
    exact ((contDiff_apply ℝ ℝ (0 : Fin 1)).pow 2).div_const 2
  have hLip : LipschitzWith 0 (fderiv ℝ (fderiv ℝ quad)) := by
    rw [hfd2]
    exact LipschitzWith.const Λ
  have huniq : ∀ x : Vec 1, quad x = quad 0 → x = 0 := by
    intro x hx
    rw [Example.quad_zero] at hx
    funext i
    fin_cases i
    simp only [quad] at hx
    simpa using hx
  have hmem : ∀ i : Fin 1, i ∈ activeIndices quad (fun _ : Fin 1 => quad) 0 := fun i => by
    rw [Example.quad_active]
    exact Finset.mem_univ i
  have hpos : ∀ v : Vec 1, v ≠ 0 →
      0 < ∑ _i : Fin 1, (1 : ℝ) * dot v (RadialHessian.matrix quad 0 *ᵥ v) := by
    intro v hv
    have hv0 : v 0 ≠ 0 := fun h => hv (funext fun i => by fin_cases i; simpa using h)
    have hq : dot v (RadialHessian.matrix quad 0 *ᵥ v) = v 0 * v 0 := by
      rw [RadialHessian.matrix, RadialHessian.bilinearMatrix_quadratic, hfd2]
      exact hΛ v v
    rw [Fin.sum_univ_one, one_mul, hq]
    exact mul_self_pos.mpr hv0
  refine ⟨1, 1, fun _ => quad, quad, 0, 0, fun _ => 1, fun x => ⟨⟨0, rfl⟩, ?_⟩,
    fun _ => quad_convex, fun _ => ⟨hC2, 0, hLip⟩, Example.quad_min, huniq,
    ⟨1, by rw [Example.quad_zero]; norm_num, quad_sublevel_compact 1⟩,
    affineIndependent_of_subsingleton ℝ _, hmem 0, fun _ _ => one_pos,
    fun i hi => absurd (hmem i) hi, by simp, by simp [Example.quad_coordinateGradient],
    fun v _ hv => hpos v hv⟩
  rintro _ ⟨i, rfl⟩
  exact le_rfl

end BfgsCoverage.Companion.Ch08A
