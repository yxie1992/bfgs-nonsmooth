import BfgsVerification.FixedNormalEndToEnd
import BfgsVerification.FixedNormalSegments
import BfgsVerification.FixedNormalCompositeEndToEnd
import BfgsVerification.NormalSpikeVariableTargets
import BfgsVerification.NormalSpikeExampleTargets
import BfgsVerification.NormalSpikeRational
import BfgsVerification.NormalSpikeMassSupport
import BfgsArticle.AdmissibleRunExistence
import OriginalClaimInterpretation

/-!
# Lean coverage: `companion/chapters/11_U.tex`

Chapter 11 ("Fixed normal geometry in arbitrary dimension"): Theorems 11.1 (one exceptional
hyperplane) and 11.2 (parallel singular interfaces), the composite families of Section 11.1.1,
the displays of the common proof (Section 11.5) and of the weaker-curvature proof (Section 11.6),
the explicit spike example (11.18)-(11.21) with its exact evaluation (Section 11.7.1), the coupled
example of Section 11.7.2, and the claims made in prose. Register:
`editorial/lean_coverage/register/C_11_U.json`.

## Conventions

* `Vec n` carries the sup norm; Euclidean quantities are explicit: $\|x\|^2$ is `sqNorm x`,
  $x^Ty$ is `dot x y`. "Lipschitz" without a constant is `LipschitzOnWith L A Ω` (equivalent for
  the two norms); the Euclidean constant $L_A$ of (11.11) is explicit.
* $P=\{x:a^Tx=b\}$, $S=a^\perp$, $P_Sv$ = `tangentProjection a v` $=v-(a^Tv)a$
  (`setup_notation`); $\partial F(x)$ = `ConvexSubdifferential.subdifferential F x`
  $=\{g:\forall z,\ g^T(z-x)\le F(z)-F(x)\}$; $\operatorname{aff}$ = `affineSpan ℝ`; "$p$ is a
  cluster point of $(x_k)$" = `MapClusterPt p atTop R.x`; "$\mu$-strongly convex on $\Omega$" =
  `EuclideanStrongConvexOn Ω μ F` ($F-\frac\mu2\|x\|^2$ convex on the convex set $\Omega$);
  "locally $C^{1,1}$ on $U$" = `CenteredSmoothSublinear.LocallyC11On U F` (differentiable on $U$,
  derivative locally Lipschitz on $U$), and `ScalarLocallyC11On` for scalar functions.
* An infinite admissible full-BFGS run is `R : AdmissibleBFGSRun n F` (see
  `BfgsCoverage.Article.Energy`); $s_k$, $y_k$, $t_k$, $d_k$, $B_k$ are `R.displacement k`,
  `R.gradientChange k`, `R.curvature k`, `R.d k`, `(R.H k)⁻¹`.
* A point $(u,v)\in\mathbb R^{n-1}\times\mathbb R$ is `Fin.cons v u` (the normal coordinate $v$
  first, as in the library; a fixed permutation of coordinates). The normal is `vnormal m` or
  `NormalSpike.normal m` $=e_v$. Block matrices written in the order $(u,v)$ in the TeX are stated
  entrywise in the order $(v,u)$.
* $a_j=2^{-j}$ ($j\ge2$) is `NormalSpike.scale (j - 2)`, $\eta$ is `NormalSpike.bump`, $k$ is
  `NormalSpike.density`, $r$ of (11.18) is `NormalSpike.sourcePrimitive`, $P$, $Q$ of Section
  11.7.1 are `NormalSpike.massPoly`, `NormalSpike.momentPoly`. The objectives (11.20) and of
  Section 11.7.2 are variables `F` with their defining equations `hF_def`
  (`spike_objective_eq`, `variable_objective_eq`). (RS) and (IR) of Chapter 4 are `RS`, `IR`.

## Standing assumptions

Theorems 11.1 and 11.2 and the prose claims about them are stated with all hypotheses of the
respective theorem written out; hypotheses a proof does not use have names starting with `_`. The
displays of Section 11.5 use the common setting of the proof (see the section comment before
`regularRegion_eq`): it covers both theorems ($b=0$ for 11.2, $E=\{0\}$ for 11.1). The reductio
hypotheses (no affine-critical cluster point; $\ell>F_*$) are omitted from the displays that do not
use them; display `disp/012` is stated with them (`zero_set_parallel`, `zero_set_hyperplane`,
whose hypotheses cannot all hold) and in general forms with satisfiable hypotheses. The displays
of Section 11.6 use the hypotheses of `tangential_family`.

## Items (main declarations)

Theorem 11.1: `one_exceptional_hyperplane`, local basin `hyperplane_local_basin`, derived
tangential growth `tangential_trace_derived`, scope `smooth_hyperplane_witness`. Theorem 11.2:
`parallel_singular_interfaces`, `singular_point_segment`, `singular_point_affine_hull`,
`smooth_point_affine_critical`, `parallel_interfaces_convergence`, `parallel_interfaces_basin`.
Families: `immediate_family`, `immediate_family_tangent`, `tangential_family`,
`quadratic_abs_included`. Section 11.5: `strong_budget`, `tangent_secant`, `plane_monotonicity`,
`zero_set_*`, `frame_columns`, `frame_pairing`, `strip_cocoercivity`, `frame_secant`,
`beta_bound`, `frame_transport`, `residual_bounds`, `transport_hypothesis`. Section 11.6:
`projected_budget`, `composite_secant_projection`, `composite_secant_bound`. Section 11.7:
`spike_scale_bump`, `bump_properties`, `spike_density_def`, `spike_def`, `bump_masses`,
`spike_regularity`, `spike_small_bounds`/`spike_cubic_bound_fails` (corrected discrepancy),
`spike_peak_curvature`, `spike_second_derivative_zero`, `spike_objective_eq`,
`spike_objective_geometry`, `spike_objective_interface`, `spike_objective_convergence`,
`spike_sample_values`, `spike_sample_hessian`, `spike_ir_fails`, `spike_rs_fails_band`,
`spike_rs_fails_nhds`; Section 11.7.1: `series_exact`, `mass_moment_polys`, `partial_bump`,
`smaller_bumps`, `rational_oracle`, `spike_peak_values`; Section 11.7.2: `variable_objective_eq`,
`variable_hessians`, `variable_strongly_convex`, `variable_unique_minimizer`,
`variable_region_geometry`, `variable_local_basin`, `variable_jump`, `variable_nonsplitting`,
`variable_zero_split`, `variable_rs_fails`; literature: `cocoercivity_on_smooth_compact`.

## Corrected discrepancies (15 October 2026)

`disp/026` (M19): "$0\le r(v)\le6v^3$ near zero" was false for every $v<0$
(`spike_cubic_bound_fails`); the display is now followed by "for $v\ge0$", where the bounds hold
(`spike_small_bounds`). `prose/027` (M18): "(6)" referred to no equation of the companion; the
sentence now reads "Thus (11.14) is the transport hypothesis of Theorem~\ref{M:residualtheorem},
with $T=I$, rank-one term $s(\beta e_n)^T$ and" (`transport_hypothesis`); the chapter's seven other
bare references ("Theorems 1 and 2", "(11)" twice, "(16)--(17)", "(18)", "(20)", "(21)"), listed in
the same entry, now carry the prefix "11.". Wording points W8 (line 354, "the source notes"), W10
(line 492) and W11 (lines 111, 416, 422, 424) were applied on the same day.

## Non-vacuity

`spike_run_exists` gives admissible runs on (11.20) from every point off $\{v=0\}$; the examples at
the end show that the hypotheses of Theorems 11.1 and 11.2, of the composite families and of the
common proof setting hold together with such a run, and that the general forms of `disp/012` have
satisfiable hypotheses. For the coupled example, `variable_runs_exist` gives admissible runs with
arbitrarily small initial value for every $\|c\|<1$ (through the convex modification
`cappedObjective`, since the existence theorem does not apply to $F$ directly when $c\neq0$), and
`variable_basin_nonvacuous` combines them with `variable_local_basin`.
-/

noncomputable section
open scoped Topology NNReal BigOperators
open Set Filter Matrix BfgsVerification

namespace BfgsCoverage.Companion.Ch11U

open FixedNormal

/-! ### The setting of Section 11.1 -/

/-- Item `C/11_U/disp/001` (`companion/chapters/11_U.tex:25-27`): the notation
\[ P=\{x:a^Tx=b\},\qquad S=a^\perp,\qquad P_S=I-aa^T \]
for a unit vector $a$ and $b\in\mathbb R$. The coverage theorems write $P$ as the set
`{x | dot a x = b}`, $S$ as `{v | dot a v = 0}` and $P_Sv$ as the library's
`tangentProjection a v` $=v-(a^Tv)a$. This theorem unfolds $P_S$ to the matrix
$I-aa^T$ and shows that it is the orthogonal projection onto $S$: its values lie in $S$, it
fixes $S$, and $v-P_Sv$ is the multiple $(a^Tv)a$ of the normal. -/
theorem setup_notation {n : ℕ} (a : Vec n) (ha : sqNorm a = 1) (v : Vec n) :
    tangentProjection a v = (1 - outer a a) *ᵥ v ∧
      dot a (tangentProjection a v) = 0 ∧
      (dot a v = 0 → tangentProjection a v = v) ∧
      v - tangentProjection a v = dot a v • a := by
  refine ⟨?_, tangentProjection_normal_zero ha v, tangentProjection_eq_self, ?_⟩
  · rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    ext i
    simp only [tangentProjection, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec,
      dotProduct, outer, dot]
    rw [Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  · simp [tangentProjection]

/-- Item `C/11_U/prose/005` (`companion/chapters/11_U.tex:27-28`): "The normal direction is
fixed; the dimension $n-1$ of the tangent space is unrestricted." For a unit vector $a$
(fixed), $S=a^\perp=\{v:a^Tv=0\}$ is a linear subspace of dimension $n-1$, for every $n$. -/
theorem tangent_space_finrank {n : ℕ} (a : Vec n) (ha : sqNorm a = 1) :
    ∃ S : Submodule ℝ (Vec n), (∀ v, v ∈ S ↔ dot a v = 0) ∧ Module.finrank ℝ S = n - 1 := by
  let f : Vec n →ₗ[ℝ] ℝ := (gradientFunctional a : Vec n →L[ℝ] ℝ)
  have hf (v : Vec n) : f v = dot a v := gradientFunctional_apply a v
  refine ⟨LinearMap.ker f, fun v => by rw [LinearMap.mem_ker, hf], ?_⟩
  have hsurj : LinearMap.range f = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    intro t
    refine ⟨t • a, ?_⟩
    rw [map_smul, hf]
    have haa : dot a a = 1 := by simpa only [dot, sqNorm, pow_two] using ha
    rw [haa, smul_eq_mul, mul_one]
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  rw [hsurj, finrank_top, Module.finrank_self, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin] at hrn
  omega

/-! ### Theorem 11.1 -/

/-- `Ω \ P` is the library's regular region for the exceptional scalar set `{0}`. -/
theorem diff_plane_eq_regularRegion {n : ℕ} (Ω : Set (Vec n)) (a : Vec n) (b : ℝ) :
    Ω \ {x | dot a x = b} = regularRegion Ω a b {0} := by
  ext x
  simp only [mem_diff, mem_setOf_eq, regularRegion, mem_inter_iff, normalCoordinate,
    mem_singleton_iff, sub_eq_zero]

/-- Item `C/11_U/heading/001` (`companion/chapters/11_U.tex:30`), Theorem 11.1 (One
exceptional hyperplane), with its displays `disp/002` and `disp/003` (lines 33-51).

Let $a$ be a unit vector, $b\in\mathbb R$, $P=\{x:a^Tx=b\}$ (`hP`), $S=a^\perp$, $P_S=I-aa^T$
(`tangentProjection a`, see `setup_notation`). Let $F:\mathbb R^n\to\mathbb R$ be finite and
convex, with unique minimizer $x_*\in P$. Let $K=\{F\le F(x_0)\}$ be compact. On an open convex
neighborhood $\Omega$ of $K$ assume: (1) $F$ is $\mu$-strongly convex for some $\mu>0$
(`EuclideanStrongConvexOn Ω μ F`: $F-\frac\mu2\|x\|^2$ convex on $\Omega$, Euclidean norm);
(2) all subgradients have the same tangential projection, $P_Sg=A(x)$ for $g\in\partial F(x)$,
where $A$ is Lipschitz continuous on $\Omega$; (3) $F$ is locally $C^{1,1}$ away from $P$, i.e.
on $\Omega\setminus P$. Then every infinite admissible full-BFGS run starting at $x_0$ satisfies
$F(x_k)\to F_*=F(x_*)$ and $x_k\to x_*$.

The library theorem is `AdmissibleBFGSRun.fixed_normal_hyperplane_convergence` (convexity of
$\Omega$ is not needed there; it is part of `EuclideanStrongConvexOn` anyway). -/
theorem one_exceptional_hyperplane {n : ℕ} (F : Vec n → ℝ) (_hF : ConvexOn ℝ univ F)
    (a : Vec n) (ha : sqNorm a = 1) (b : ℝ) (P : Set (Vec n)) (hP : P = {x | dot a x = b})
    (xstar : Vec n) (hmin : ∀ z, F xstar ≤ F z) (hunique : ∀ z, F z = F xstar → z = xstar)
    (hplane : xstar ∈ P)
    (x0 : Vec n) (K : Set (Vec n)) (hK_def : K = {x | F x ≤ F x0}) (hK : IsCompact K)
    (Ω : Set (Vec n)) (hΩ : IsOpen Ω) (_hΩc : Convex ℝ Ω) (hKΩ : K ⊆ Ω)
    (μ : ℝ) (hμ : 0 < μ) (hstrong : EuclideanStrongConvexOn Ω μ F)
    (A : Vec n → Vec n)
    (hA : ∀ x ∈ Ω, ∀ g ∈ ConvexSubdifferential.subdifferential F x,
      tangentProjection a g = A x)
    (L : ℝ≥0) (hLip : LipschitzOnWith L A Ω)
    (hsmooth : CenteredSmoothSublinear.LocallyC11On (Ω \ P) F) :
    ∀ R : AdmissibleBFGSRun n F, R.x 0 = x0 →
      Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) ∧ Tendsto R.x atTop (𝓝 xstar) := by
  intro R hR0
  subst hP hK_def
  have hKR : R.initialSublevel = {x | F x ≤ F x0} := by
    rw [AdmissibleBFGSRun.initialSublevel, hR0]
  rw [diff_plane_eq_regularRegion] at hsmooth
  exact R.fixed_normal_hyperplane_convergence hΩ (hKR ▸ hK) (hKR ▸ hKΩ) hμ hstrong ha b
    (fun x hx g hg => hA x hx g hg) hLip hsmooth xstar hmin hunique hplane

/-- Item `C/11_U/prose/007` (`companion/chapters/11_U.tex:56-58`): "If these hypotheses hold
only in a neighborhood of a unique minimizer, some $\varepsilon>0$ gives the same conclusion for
every start with $F(x_0)<F_*+\varepsilon$." With item `prose/008` (lines 58-59): $\varepsilon$
is chosen before the run, hence before its initial SPD matrix and its fixed line-search pair
$0<c_1<c_2<1$ (both are data of the run `R`).

The hypotheses of Theorem 11.1 on an open convex neighborhood $\Omega$ of the unique minimizer
$x_*\in P$ (no compact sublevel is assumed). Library: `FixedNormal.local_hyperplane_convergence_basin`. -/
theorem hyperplane_local_basin {n : ℕ} (F : Vec n → ℝ) (hF : ConvexOn ℝ univ F)
    (a : Vec n) (ha : sqNorm a = 1) (b : ℝ) (P : Set (Vec n)) (hP : P = {x | dot a x = b})
    (xstar : Vec n) (hmin : ∀ z, F xstar ≤ F z) (hunique : ∀ z, F z = F xstar → z = xstar)
    (hplane : xstar ∈ P)
    (Ω : Set (Vec n)) (hΩ : IsOpen Ω) (_hΩc : Convex ℝ Ω) (hstar : xstar ∈ Ω)
    (μ : ℝ) (hμ : 0 < μ) (hstrong : EuclideanStrongConvexOn Ω μ F)
    (A : Vec n → Vec n)
    (hA : ∀ x ∈ Ω, ∀ g ∈ ConvexSubdifferential.subdifferential F x,
      tangentProjection a g = A x)
    (L : ℝ≥0) (hLip : LipschitzOnWith L A Ω)
    (hsmooth : CenteredSmoothSublinear.LocallyC11On (Ω \ P) F) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ R : AdmissibleBFGSRun n F, F (R.x 0) < F xstar + ε →
      Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) ∧ Tendsto R.x atTop (𝓝 xstar) := by
  subst hP
  rw [diff_plane_eq_regularRegion] at hsmooth
  exact local_hyperplane_convergence_basin hF xstar hmin hunique hΩ hstar hμ hstrong ha b hplane
    (fun x hx g hg => hA x hx g hg) hLip hsmooth

/-- Item `C/11_U/prose/010` (`companion/chapters/11_U.tex:63-65`): "The assumptions concern
the objective. In particular, the claim that a part of $B_k=H_k^{-1}$ has a controlled growth
rate will be derived, not assumed."

Under the hypotheses of Theorem 11.1 (only objective assumptions), for every run starting at
$x_0$ and every matrix $U$ whose columns are an orthonormal basis of $S$ ($U^TU=I$,
$UU^T=P_S$), the tangential part of $B_k=H_k^{-1}$ grows at most linearly:
$\operatorname{tr}(U^TB_kU)\le\operatorname{tr}(U^TB_0U)+Ck$ with $C=nL^2/\mu$ ($L$ the
Lipschitz constant of $A$ in the sup norm). Library: `fixed_normal_hessian_trace_budget`. -/
theorem tangential_trace_derived {n : ℕ} (F : Vec n → ℝ) (_hF : ConvexOn ℝ univ F)
    (a : Vec n) (_ha : sqNorm a = 1) (b : ℝ) (P : Set (Vec n)) (_hP : P = {x | dot a x = b})
    (xstar : Vec n) (_hmin : ∀ z, F xstar ≤ F z) (_hunique : ∀ z, F z = F xstar → z = xstar)
    (_hplane : xstar ∈ P)
    (x0 : Vec n) (K : Set (Vec n)) (hK_def : K = {x | F x ≤ F x0}) (_hK : IsCompact K)
    (Ω : Set (Vec n)) (_hΩ : IsOpen Ω) (_hΩc : Convex ℝ Ω) (hKΩ : K ⊆ Ω)
    (μ : ℝ) (hμ : 0 < μ) (hstrong : EuclideanStrongConvexOn Ω μ F)
    (A : Vec n → Vec n)
    (hA : ∀ x ∈ Ω, ∀ g ∈ ConvexSubdifferential.subdifferential F x,
      tangentProjection a g = A x)
    (L : ℝ≥0) (hLip : LipschitzOnWith L A Ω)
    (_hsmooth : CenteredSmoothSublinear.LocallyC11On (Ω \ P) F)
    (R : AdmissibleBFGSRun n F) (hR0 : R.x 0 = x0)
    {m : ℕ} (U : Matrix (Fin n) (Fin m) ℝ) (hU : Uᵀ * U = 1)
    (hUS : ∀ v, (U * Uᵀ) *ᵥ v = tangentProjection a v) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ,
      (Uᵀ * (R.H k)⁻¹ * U).trace ≤ (Uᵀ * (R.H 0)⁻¹ * U).trace + C * k := by
  subst hK_def
  have hx : ∀ k, R.x k ∈ Ω := fun k => hKΩ (by
    change F (R.x k) ≤ F x0
    rw [← hR0]
    exact R.objective_le_initial k)
  refine ⟨(n : ℝ) * (L : ℝ) ^ 2 / μ, by positivity, fun k => ?_⟩
  exact R.fixed_normal_hessian_trace_budget hμ hstrong hx (fun x hx g hg => hA x hx g hg) hLip
    U hU hUS k

/-- Item `C/11_U/prose/025` (`companion/chapters/11_U.tex:152-154`): "Having $x_*\in P$ makes
every zero of $A$ on $P$ optimal, so genuine nondifferentiability at every exceptional point is
unnecessary there." Under the hypotheses of Theorem 11.1, a point $p\in\Omega\cap P$ with
$A(p)=0$ is the minimizer $x_*$, hence optimal. (Theorem 11.1 has no nondifferentiability
hypothesis on $P$: `one_exceptional_hyperplane`.) Library: `tangent_zero_on_minimizer_plane`. -/
theorem plane_zero_optimal {n : ℕ} (F : Vec n → ℝ) (hF : ConvexOn ℝ univ F)
    (a : Vec n) (_ha : sqNorm a = 1) (b : ℝ) (P : Set (Vec n)) (hP : P = {x | dot a x = b})
    (xstar : Vec n) (hmin : ∀ z, F xstar ≤ F z) (_hunique : ∀ z, F z = F xstar → z = xstar)
    (hplane : xstar ∈ P)
    (x0 : Vec n) (K : Set (Vec n)) (hK_def : K = {x | F x ≤ F x0}) (_hK : IsCompact K)
    (Ω : Set (Vec n)) (_hΩ : IsOpen Ω) (_hΩc : Convex ℝ Ω) (hKΩ : K ⊆ Ω)
    (μ : ℝ) (hμ : 0 < μ) (hstrong : EuclideanStrongConvexOn Ω μ F)
    (A : Vec n → Vec n)
    (hA : ∀ x ∈ Ω, ∀ g ∈ ConvexSubdifferential.subdifferential F x,
      tangentProjection a g = A x)
    (L : ℝ≥0) (_hLip : LipschitzOnWith L A Ω)
    (_hsmooth : CenteredSmoothSublinear.LocallyC11On (Ω \ P) F)
    (p : Vec n) (hpΩ : p ∈ Ω) (hpP : p ∈ P) (hAp : A p = 0) :
    p = xstar ∧ ∀ z, F p ≤ F z := by
  subst hP hK_def
  have hstar : xstar ∈ Ω := hKΩ (hmin x0)
  have hpp : dot a p = dot a xstar := hpP.trans hplane.symm
  have he := tangent_zero_on_minimizer_plane hF hμ hstrong hstar hpΩ hmin hpp
    (fun g hg => (hA p hpΩ g hg).trans hAp)
  exact ⟨he, he ▸ hmin⟩

/-! ### Theorem 11.2 -/

/-- With $b=0$, the library's regular region is $\Omega\setminus\Sigma$ for
$\Sigma=\{x:a^Tx\in E\}$. -/
theorem regularRegion_zero_eq {n : ℕ} (Ω : Set (Vec n)) (a : Vec n) (E : Set ℝ) :
    regularRegion Ω a 0 E = Ω \ {x | dot a x ∈ E} := by
  ext x
  simp only [regularRegion, normalCoordinate, sub_zero, mem_inter_iff, mem_setOf_eq, mem_diff]

/-- The hypothesis $P_S\partial F(x)=\{A(x)\}$ gives $P_Sg=A(x)$ for every subgradient. -/
theorem tangent_of_image_eq {n : ℕ} {F : Vec n → ℝ} {a : Vec n} {A : Vec n → Vec n}
    {Ω : Set (Vec n)}
    (hA : ∀ x ∈ Ω, tangentProjection a '' ConvexSubdifferential.subdifferential F x = {A x}) :
    ∀ x ∈ Ω, ∀ g, Homogeneous.Supports F x g → tangentProjection a g = A x := by
  intro x hx g hg
  have hm : tangentProjection a g ∈ tangentProjection a '' ConvexSubdifferential.subdifferential F x :=
    mem_image_of_mem _ hg
  rw [hA x hx] at hm
  exact hm

/-- A run in the compact sublevel $K=\{F\le c\}$ has a compact initial sublevel inside $K$. -/
theorem initialSublevel_sub {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (c : ℝ)
    (K : Set (Vec n)) (hK_def : K = {x | F x ≤ c}) (hK : IsCompact K) (hrun : ∀ k, R.x k ∈ K) :
    R.initialSublevel ⊆ K ∧ IsCompact R.initialSublevel := by
  have hsub : R.initialSublevel ⊆ K := by
    intro x hx
    have h0 := hrun 0
    rw [hK_def] at h0 ⊢
    exact le_trans (show F x ≤ F (R.x 0) from hx) h0
  have hc : IsClosed R.initialSublevel :=
    isClosed_le (convex_continuous R.convex) continuous_const
  exact ⟨hsub, hK.of_isClosed_subset hc hsub⟩

/-- Item `C/11_U/heading/002` (`companion/chapters/11_U.tex:113`), Theorem 11.2 (Parallel
singular interfaces), with its display `disp/006` (lines 113-133).

Let $F$ be finite convex with attained minimum and compact sublevel $K=\{F\le c\}$. Assume $F$
is $\mu$-strongly convex on an open convex neighborhood $\Omega$ of $K$. Let $a$ be a unit vector
and $E\subset\mathbb R$ closed. On $\Omega$ suppose: the singular set is
$\Sigma=\{x:a^Tx\in E\}$ (`Sg`): every point of $\Sigma$ (in $\Omega$) is genuinely
nondifferentiable, and $F$ is locally $C^{1,1}$ off $\Sigma$ (on $\Omega\setminus\Sigma$); and
$P_S\partial F(x)=\{A(x)\}$ for a Lipschitz field $A$, where $S=a^\perp$. Then the cluster set of
every infinite admissible full-BFGS run in $K$ contains a point $p$ with
$0\in\operatorname{aff}\partial F(p)$ (`MapClusterPt p atTop R.x`: $p$ is a cluster point of
$(x_k)$; `affineSpan ℝ` is the affine hull).

Library: `AdmissibleBFGSRun.parallel_interfaces_affineCritical_cluster_on_sublevel` (the
library writes $\Sigma$ with $r(x)=a^Tx-b$; here $b=0$). -/
theorem parallel_singular_interfaces {n : ℕ} (F : Vec n → ℝ) (_hF : ConvexOn ℝ univ F)
    (_hattained : ∃ xstar, ∀ z, F xstar ≤ F z)
    (c : ℝ) (K : Set (Vec n)) (hK_def : K = {x | F x ≤ c}) (hK : IsCompact K)
    (Ω : Set (Vec n)) (hΩ : IsOpen Ω) (_hΩc : Convex ℝ Ω) (hKΩ : K ⊆ Ω)
    (μ : ℝ) (hμ : 0 < μ) (hstrong : EuclideanStrongConvexOn Ω μ F)
    (a : Vec n) (ha : sqNorm a = 1) (E : Set ℝ) (hE : IsClosed E)
    (Sg : Set (Vec n)) (hSg : Sg = {x | dot a x ∈ E})
    (hsingular : ∀ p ∈ Ω, p ∈ Sg → ¬DifferentiableAt ℝ F p)
    (hsmooth : CenteredSmoothSublinear.LocallyC11On (Ω \ Sg) F)
    (A : Vec n → Vec n)
    (hA : ∀ x ∈ Ω, tangentProjection a '' ConvexSubdifferential.subdifferential F x = {A x})
    (L : ℝ≥0) (hLip : LipschitzOnWith L A Ω) :
    ∀ R : AdmissibleBFGSRun n F, (∀ k, R.x k ∈ K) →
      ∃ p, MapClusterPt p atTop R.x ∧
        (0 : Vec n) ∈ affineSpan ℝ (ConvexSubdifferential.subdifferential F p) := by
  intro R hrun
  subst hSg
  obtain ⟨hsub, hKR⟩ := initialSublevel_sub R c K hK_def hK hrun
  rw [← regularRegion_zero_eq] at hsmooth
  exact R.parallel_interfaces_affineCritical_cluster hΩ hKR (hsub.trans hKΩ) hμ hstrong ha 0
    (tangent_of_image_eq hA) hLip hE hsmooth
    (fun p hp he => hsingular p hp (by simpa only [normalCoordinate, sub_zero] using he))

/-- Item `C/11_U/prose/021` (`companion/chapters/11_U.tex:137-139`): "At a point of $\Sigma$,
the subdifferential is a nontrivial compact segment parallel to $a$, because every subgradient
has the same $S$ projection." Under the hypotheses of Theorem 11.2, at $p\in\Omega\cap\Sigma$:
$\partial F(p)$ is compact and equals the segment $[A(p)+la,\,A(p)+ua]$ with $l<u$ and distinct
endpoints. Library: `nonsmooth_subdifferential_parallel_segment`. -/
theorem singular_point_segment {n : ℕ} (F : Vec n → ℝ) (hF : ConvexOn ℝ univ F)
    (_hattained : ∃ xstar, ∀ z, F xstar ≤ F z)
    (c : ℝ) (K : Set (Vec n)) (_hK_def : K = {x | F x ≤ c}) (_hK : IsCompact K)
    (Ω : Set (Vec n)) (_hΩ : IsOpen Ω) (_hΩc : Convex ℝ Ω) (_hKΩ : K ⊆ Ω)
    (μ : ℝ) (_hμ : 0 < μ) (_hstrong : EuclideanStrongConvexOn Ω μ F)
    (a : Vec n) (ha : sqNorm a = 1) (E : Set ℝ) (_hE : IsClosed E)
    (Sg : Set (Vec n)) (_hSg : Sg = {x | dot a x ∈ E})
    (hsingular : ∀ p ∈ Ω, p ∈ Sg → ¬DifferentiableAt ℝ F p)
    (_hsmooth : CenteredSmoothSublinear.LocallyC11On (Ω \ Sg) F)
    (A : Vec n → Vec n)
    (hA : ∀ x ∈ Ω, tangentProjection a '' ConvexSubdifferential.subdifferential F x = {A x})
    (L : ℝ≥0) (_hLip : LipschitzOnWith L A Ω)
    (p : Vec n) (hpΩ : p ∈ Ω) (hpS : p ∈ Sg) :
    IsCompact (ConvexSubdifferential.subdifferential F p) ∧
      ∃ l u : ℝ, l < u ∧ A p + l • a ≠ A p + u • a ∧
        ConvexSubdifferential.subdifferential F p = segment ℝ (A p + l • a) (A p + u • a) :=
  ⟨ConvexSubdifferential.isCompact_subdifferential hF p,
    (nonsmooth_subdifferential_parallel_segment hF ha (tangent_of_image_eq hA p hpΩ)
      (hsingular p hpΩ hpS)).1⟩

/-- Item `C/11_U/disp/007` (`companion/chapters/11_U.tex:139-143`): under the hypotheses of
Theorem 11.2, at $p\in\Omega\cap\Sigma$,
\[ \operatorname{aff}\partial F(p)=A(p)+\mathbb Ra,\qquad
   0\in\operatorname{aff}\partial F(p)\iff A(p)=0. \]
Library: `nonsmooth_subdifferential_parallel_segment`, `affine_critical_iff_tangent_zero`. -/
theorem singular_point_affine_hull {n : ℕ} (F : Vec n → ℝ) (hF : ConvexOn ℝ univ F)
    (_hattained : ∃ xstar, ∀ z, F xstar ≤ F z)
    (c : ℝ) (K : Set (Vec n)) (_hK_def : K = {x | F x ≤ c}) (_hK : IsCompact K)
    (Ω : Set (Vec n)) (_hΩ : IsOpen Ω) (_hΩc : Convex ℝ Ω) (_hKΩ : K ⊆ Ω)
    (μ : ℝ) (_hμ : 0 < μ) (_hstrong : EuclideanStrongConvexOn Ω μ F)
    (a : Vec n) (ha : sqNorm a = 1) (E : Set ℝ) (_hE : IsClosed E)
    (Sg : Set (Vec n)) (_hSg : Sg = {x | dot a x ∈ E})
    (hsingular : ∀ p ∈ Ω, p ∈ Sg → ¬DifferentiableAt ℝ F p)
    (_hsmooth : CenteredSmoothSublinear.LocallyC11On (Ω \ Sg) F)
    (A : Vec n → Vec n)
    (hA : ∀ x ∈ Ω, tangentProjection a '' ConvexSubdifferential.subdifferential F x = {A x})
    (L : ℝ≥0) (_hLip : LipschitzOnWith L A Ω)
    (p : Vec n) (hpΩ : p ∈ Ω) (hpS : p ∈ Sg) :
    (affineSpan ℝ (ConvexSubdifferential.subdifferential F p) : Set (Vec n)) =
        Set.range (fun t : ℝ => A p + t • a) ∧
      ((0 : Vec n) ∈ affineSpan ℝ (ConvexSubdifferential.subdifferential F p) ↔ A p = 0) :=
  ⟨(nonsmooth_subdifferential_parallel_segment hF ha (tangent_of_image_eq hA p hpΩ)
      (hsingular p hpΩ hpS)).2,
    affine_critical_iff_tangent_zero hF (tangent_of_image_eq hA p hpΩ) (hsingular p hpΩ hpS)⟩

/-- At a point of differentiability of a convex function, $\partial F(p)=\{\nabla F(p)\}$, so
$0\in\operatorname{aff}\partial F(p)$ exactly when $\nabla F(p)=0$. -/
theorem affine_critical_iff_of_hasFDerivAt {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    {p g : Vec n} (hg : HasFDerivAt F (gradientFunctional g) p) :
    (0 : Vec n) ∈ affineSpan ℝ (ConvexSubdifferential.subdifferential F p) ↔ g = 0 := by
  rw [ConvexSubdifferential.subdifferential_eq_singleton_of_hasFDerivAt hF hg,
    AffineSubspace.mem_affineSpan_singleton, eq_comm]

/-- Item `C/11_U/prose/022` (`companion/chapters/11_U.tex:143`): "At a smooth point, affine
criticality is ordinary stationarity." Under the hypotheses of Theorem 11.2, at a point
$p\in\Omega$ where $F$ is differentiable with gradient $g$,
$0\in\operatorname{aff}\partial F(p)\iff g=0$. -/
theorem smooth_point_affine_critical {n : ℕ} (F : Vec n → ℝ) (hF : ConvexOn ℝ univ F)
    (_hattained : ∃ xstar, ∀ z, F xstar ≤ F z)
    (c : ℝ) (K : Set (Vec n)) (_hK_def : K = {x | F x ≤ c}) (_hK : IsCompact K)
    (Ω : Set (Vec n)) (_hΩ : IsOpen Ω) (_hΩc : Convex ℝ Ω) (_hKΩ : K ⊆ Ω)
    (μ : ℝ) (_hμ : 0 < μ) (_hstrong : EuclideanStrongConvexOn Ω μ F)
    (a : Vec n) (_ha : sqNorm a = 1) (E : Set ℝ) (_hE : IsClosed E)
    (Sg : Set (Vec n)) (_hSg : Sg = {x | dot a x ∈ E})
    (_hsingular : ∀ p ∈ Ω, p ∈ Sg → ¬DifferentiableAt ℝ F p)
    (_hsmooth : CenteredSmoothSublinear.LocallyC11On (Ω \ Sg) F)
    (A : Vec n → Vec n)
    (_hA : ∀ x ∈ Ω, tangentProjection a '' ConvexSubdifferential.subdifferential F x = {A x})
    (L : ℝ≥0) (_hLip : LipschitzOnWith L A Ω)
    (p g : Vec n) (_hpΩ : p ∈ Ω) (hg : HasFDerivAt F (gradientFunctional g) p) :
    (0 : Vec n) ∈ affineSpan ℝ (ConvexSubdifferential.subdifferential F p) ↔ g = 0 :=
  affine_critical_iff_of_hasFDerivAt hF hg

/-- Item `C/11_U/prose/023` (`companion/chapters/11_U.tex:145-149`), with display `disp/008`:
"adding $0\in\operatorname{aff}\partial F(p)\implies0\in\partial F(p)$ on $K$ [\dots] gives
convergence to the minimum value and, under uniqueness, convergence of the whole sequence."
Under the hypotheses of Theorem 11.2, with $x_*$ a minimizer (the attained minimum), if the
implication holds at every $p\in K$, then every run in $K$ has $F(x_k)\to F(x_*)$, and
$x_k\to x_*$ when $x_*$ is the unique minimizer. Taking for $K$ a compact low sublevel inside the
structural neighborhood gives the "sufficiently low trapped neighborhood" reading; the basin
form is `parallel_interfaces_basin`. Library:
`parallel_interfaces_convergence_of_affine_correctness`. -/
theorem parallel_interfaces_convergence {n : ℕ} (F : Vec n → ℝ) (_hF : ConvexOn ℝ univ F)
    (xstar : Vec n) (hmin : ∀ z, F xstar ≤ F z)
    (c : ℝ) (K : Set (Vec n)) (hK_def : K = {x | F x ≤ c}) (hK : IsCompact K)
    (Ω : Set (Vec n)) (hΩ : IsOpen Ω) (_hΩc : Convex ℝ Ω) (hKΩ : K ⊆ Ω)
    (μ : ℝ) (hμ : 0 < μ) (hstrong : EuclideanStrongConvexOn Ω μ F)
    (a : Vec n) (ha : sqNorm a = 1) (E : Set ℝ) (hE : IsClosed E)
    (Sg : Set (Vec n)) (hSg : Sg = {x | dot a x ∈ E})
    (hsingular : ∀ p ∈ Ω, p ∈ Sg → ¬DifferentiableAt ℝ F p)
    (hsmooth : CenteredSmoothSublinear.LocallyC11On (Ω \ Sg) F)
    (A : Vec n → Vec n)
    (hA : ∀ x ∈ Ω, tangentProjection a '' ConvexSubdifferential.subdifferential F x = {A x})
    (L : ℝ≥0) (hLip : LipschitzOnWith L A Ω)
    (hcorrect : ∀ p ∈ K,
      (0 : Vec n) ∈ affineSpan ℝ (ConvexSubdifferential.subdifferential F p) →
        (0 : Vec n) ∈ ConvexSubdifferential.subdifferential F p) :
    ∀ R : AdmissibleBFGSRun n F, (∀ k, R.x k ∈ K) →
      Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) ∧
        ((∀ z, F z = F xstar → z = xstar) → Tendsto R.x atTop (𝓝 xstar)) := by
  intro R hrun
  subst hSg
  obtain ⟨hsub, hKR⟩ := initialSublevel_sub R c K hK_def hK hrun
  rw [← regularRegion_zero_eq] at hsmooth
  have h := R.parallel_interfaces_convergence_of_affine_correctness hΩ hKR (hsub.trans hKΩ) hμ
    hstrong ha 0 (tangent_of_image_eq hA) hLip hE hsmooth
    (fun p hp he => hsingular p hp (by simpa only [normalCoordinate, sub_zero] using he))
    (fun p hp hz => hcorrect p (hsub hp) hz) xstar hmin
  exact ⟨h.1, h.2.2⟩

/-- Item `C/11_U/prose/023` (`companion/chapters/11_U.tex:145-149`), local form: "or on a
sufficiently low trapped neighborhood". If the hypotheses of Theorem 11.2 hold on an open convex
neighborhood $\Omega$ of a unique minimizer $x_*$ and
$0\in\operatorname{aff}\partial F(p)\implies0\in\partial F(p)$ holds on $\Omega$, some
$\varepsilon>0$ (chosen before the run) gives $F(x_k)\to F_*$ and $x_k\to x_*$ for every run
with $F(x_0)<F_*+\varepsilon$. Library: `local_parallel_interfaces_convergence_basin`. -/
theorem parallel_interfaces_basin {n : ℕ} (F : Vec n → ℝ) (hF : ConvexOn ℝ univ F)
    (xstar : Vec n) (hmin : ∀ z, F xstar ≤ F z) (hunique : ∀ z, F z = F xstar → z = xstar)
    (Ω : Set (Vec n)) (hΩ : IsOpen Ω) (_hΩc : Convex ℝ Ω) (hstar : xstar ∈ Ω)
    (μ : ℝ) (hμ : 0 < μ) (hstrong : EuclideanStrongConvexOn Ω μ F)
    (a : Vec n) (ha : sqNorm a = 1) (E : Set ℝ) (hE : IsClosed E)
    (Sg : Set (Vec n)) (hSg : Sg = {x | dot a x ∈ E})
    (hsingular : ∀ p ∈ Ω, p ∈ Sg → ¬DifferentiableAt ℝ F p)
    (hsmooth : CenteredSmoothSublinear.LocallyC11On (Ω \ Sg) F)
    (A : Vec n → Vec n)
    (hA : ∀ x ∈ Ω, tangentProjection a '' ConvexSubdifferential.subdifferential F x = {A x})
    (L : ℝ≥0) (hLip : LipschitzOnWith L A Ω)
    (hcorrect : ∀ p ∈ Ω,
      (0 : Vec n) ∈ affineSpan ℝ (ConvexSubdifferential.subdifferential F p) →
        (0 : Vec n) ∈ ConvexSubdifferential.subdifferential F p) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ R : AdmissibleBFGSRun n F, F (R.x 0) < F xstar + ε →
      Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) ∧ Tendsto R.x atTop (𝓝 xstar) := by
  subst hSg
  rw [← regularRegion_zero_eq] at hsmooth
  exact local_parallel_interfaces_convergence_basin hF xstar hmin hunique hΩ hstar hμ hstrong ha 0
    (tangent_of_image_eq hA) hLip hE hsmooth
    (fun p hp he => hsingular p hp (by simpa only [normalCoordinate, sub_zero] using he))
    hcorrect

/-! ### The composite families of Section 11.1.1 and Section 11.6

A point $(u,v)\in\mathbb R^{n-1}\times\mathbb R$ is `Fin.cons v u : Vec (m + 1)` ($n=m+1$; the
normal coordinate $v$ is coordinate `0`), and the normal is `vnormal m` $=e_v$. -/

/-- The unit normal $e_v$ of the hyperplane $v=0$. -/
def vnormal (m : ℕ) : Vec (m + 1) := Pi.single 0 1

theorem dot_vnormal {m : ℕ} (x : Vec (m + 1)) : dot (vnormal m) x = x 0 := by
  simp [vnormal, dot, Pi.single_apply]

theorem sqNorm_vnormal (m : ℕ) : sqNorm (vnormal m) = 1 := by
  simp [vnormal, sqNorm, Pi.single_apply]

theorem normalCoordinate_vnormal {m : ℕ} (x : Vec (m + 1)) :
    normalCoordinate (vnormal m) 0 x = x 0 := by
  rw [normalCoordinate, dot_vnormal, sub_zero]

/-- $P_S(u,v)=(u,0)$ for $S=\mathbb R^{n-1}\times\{0\}$. -/
theorem tangent_vnormal {m : ℕ} (x : Vec (m + 1)) :
    tangentProjection (vnormal m) x = Fin.cons 0 (Fin.tail x) := by
  ext i
  rw [tangentProjection, dot_vnormal]
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [vnormal]
  · simp [vnormal, Fin.tail, Pi.single_apply, Fin.succ_ne_zero]

/-- $\|P_S(u,v)\|^2=\|u\|^2$. -/
theorem sqNorm_tangent_vnormal {m : ℕ} (x : Vec (m + 1)) :
    sqNorm (tangentProjection (vnormal m) x) = sqNorm (Fin.tail x) := by
  rw [tangent_vnormal]
  simp [sqNorm, Fin.sum_univ_succ]

/-- The family's representation $F(u,v)=\psi(u,v)+h(v)$ in the library's form. -/
theorem rep_of_cons {m : ℕ} {F ψ : Vec (m + 1) → ℝ} {h : ℝ → ℝ}
    (hrep : ∀ (u : Vec m) (v : ℝ), F (Fin.cons v u) = ψ (Fin.cons v u) + h v) :
    ∀ x, F x = ψ x + h (normalCoordinate (vnormal m) 0 x) := by
  intro x
  rw [normalCoordinate_vnormal]
  have hx := hrep (Fin.tail x) (x 0)
  rwa [Fin.cons_self_tail] at hx

/-- A minimizer inside an open set on which $F$ is $\mu$-strongly convex is the unique
minimizer of the convex function $F$. -/
theorem unique_of_strong {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    {Ω : Set (Vec n)} (hΩ : IsOpen Ω) {μ : ℝ} (hμ : 0 < μ)
    (hstrong : EuclideanStrongConvexOn Ω μ F) {xstar : Vec n} (hstar : xstar ∈ Ω)
    (hmin : ∀ z, F xstar ≤ F z) : ∀ z, F z = F xstar → z = xstar := by
  intro z hz
  have hseg : ∀ᶠ t in 𝓝 (0 : ℝ), xstar + t • (z - xstar) ∈ Ω := by
    have hc : Continuous (fun t : ℝ => xstar + t • (z - xstar)) := by fun_prop
    have h0 : xstar + (0 : ℝ) • (z - xstar) ∈ Ω := by simpa using hstar
    exact hc.continuousAt.eventually (hΩ.mem_nhds h0)
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), xstar + t • (z - xstar) ∈ Ω ∧ t < 1 ∧ 0 < t := by
    filter_upwards [hseg.filter_mono nhdsWithin_le_nhds,
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨t, htΩ, _ht1, ht0'⟩ := hev.exists
  set w := xstar + t • (z - xstar) with hw
  have hw' : w = (1 - t) • xstar + t • z := by rw [hw]; module
  have hFw : F w ≤ F xstar := by
    have hc := hF.2 (mem_univ xstar) (mem_univ z) (by linarith : 0 ≤ 1 - t) ht0'.le
      (by ring : (1 - t) + t = 1)
    rw [← hw'] at hc
    simp only [smul_eq_mul] at hc
    rw [hz] at hc
    linarith
  have hs := strong_supporting_inequality hstrong hstar htΩ
    (ConvexSubdifferential.zero_mem_iff_global_minimum.mpr hmin)
  have hd0 : dot (0 : Vec n) (w - xstar) = 0 := by simp [dot]
  rw [hd0, zero_add] at hs
  have hsq : sqNorm (w - xstar) ≤ 0 := by
    have := hmin w
    nlinarith [sqNorm_nonneg (w - xstar)]
  have hwz : w - xstar = 0 := (CertificateGeometry.sqNorm_eq_zero_iff _).mp
    (le_antisymm hsq (sqNorm_nonneg _))
  have hwz' : t • (z - xstar) = 0 := by rw [← hwz, hw]; abel
  rcases smul_eq_zero.mp hwz' with h | h
  · exact absurd h ht0'.ne'
  · exact sub_eq_zero.mp h

/-- Item `C/11_U/disp/004` (`companion/chapters/11_U.tex:74-76`): the immediate family
\[ F(u,v)=\psi(u,v)+h(v),\qquad u\in\mathbb R^{n-1},\quad v\in\mathbb R, \]
"where $\psi$ is convex with locally Lipschitz gradient, $h$ is finite convex and locally
$C^{1,1}$ on $\mathbb R\setminus\{0\}$, $F$ is strongly convex on the relevant neighborhood, and
the minimizer has $v_*=0$" (lines 76-79), is covered by Theorem 11.1: for a compact sublevel
$K=\{F\le F(x_0)\}$ inside an open convex neighborhood $\Omega$ on which $F$ is $\mu$-strongly
convex, every infinite admissible run starting at $x_0$ has $F(x_k)\to F_*$, $x_k\to x_*$. The
minimizer is unique (`unique_of_strong`); $H_0\succ0$ is arbitrary, so the objective and the
initial matrix may be fully coupled (`prose/012`). Library:
`AdmissibleBFGSRun.strongly_convex_composite_convergence`. -/
theorem immediate_family {m : ℕ} (F ψ : Vec (m + 1) → ℝ) (h : ℝ → ℝ)
    (hrep : ∀ (u : Vec m) (v : ℝ), F (Fin.cons v u) = ψ (Fin.cons v u) + h v)
    (hψ : ConvexOn ℝ univ ψ) (hψs : CenteredSmoothSublinear.LocallyC11On univ ψ)
    (hh : ConvexOn ℝ univ h) (hhs : ScalarLocallyC11On ({0}ᶜ : Set ℝ) h)
    (x0 : Vec (m + 1)) (K : Set (Vec (m + 1))) (hK_def : K = {x | F x ≤ F x0})
    (hK : IsCompact K) (Ω : Set (Vec (m + 1))) (hΩ : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (hKΩ : K ⊆ Ω) (μ : ℝ) (hμ : 0 < μ) (hstrong : EuclideanStrongConvexOn Ω μ F)
    (xstar : Vec (m + 1)) (hmin : ∀ z, F xstar ≤ F z) (hv : xstar 0 = 0) :
    ∀ R : AdmissibleBFGSRun (m + 1) F, R.x 0 = x0 →
      Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) ∧ Tendsto R.x atTop (𝓝 xstar) := by
  intro R hR0
  subst hK_def
  have hKR : R.initialSublevel = {x | F x ≤ F x0} := by
    rw [AdmissibleBFGSRun.initialSublevel, hR0]
  have hstar : xstar ∈ Ω := hKΩ (hmin x0)
  have hunique := unique_of_strong R.convex hΩ hμ hstrong hstar hmin
  have hrep' := rep_of_cons hrep
  exact R.strongly_convex_composite_convergence hΩ (hKR ▸ hK) (hKR ▸ hKΩ)
    (hψ.subset (subset_univ Ω) hΩc) ⟨hψs.1.mono (subset_univ Ω), hψs.2.mono (subset_univ Ω)⟩
    hh hhs (sqNorm_vnormal m) 0 hμ hstrong (fun x _ => hrep' x) xstar hmin hunique
    (by rw [dot_vnormal, hv])

/-- Item `C/11_U/prose/011` (`companion/chapters/11_U.tex:79-80`): "Here $A=\nabla_u\psi$,
irrespective of the singular normal derivative of $h$." For the immediate family, at every point
$x=(u,v)$ (also where $h$ is not differentiable at $v$), every subgradient $g\in\partial F(x)$
has $u$-components equal to those of $\nabla\psi(x)$: $P_Sg=P_S\nabla\psi(x)$ with
$S=\mathbb R^{n-1}\times\{0\}$. Library: `composite_support_projection`. -/
theorem immediate_family_tangent {m : ℕ} (F ψ : Vec (m + 1) → ℝ) (h : ℝ → ℝ)
    (hrep : ∀ (u : Vec m) (v : ℝ), F (Fin.cons v u) = ψ (Fin.cons v u) + h v)
    (_hψ : ConvexOn ℝ univ ψ) (hψs : CenteredSmoothSublinear.LocallyC11On univ ψ)
    (hh : ConvexOn ℝ univ h) (_hhs : ScalarLocallyC11On ({0}ᶜ : Set ℝ) h)
    (x g : Vec (m + 1)) (hg : g ∈ ConvexSubdifferential.subdifferential F x) :
    tangentProjection (vnormal m) g = tangentProjection (vnormal m) (coordinateGradient ψ x) ∧
      ∀ i : Fin m, g i.succ = coordinateGradient ψ x i.succ := by
  have hp : HasFDerivAt ψ (gradientFunctional (coordinateGradient ψ x)) x :=
    hasFDerivAt_coordinateGradient ((hψs.1 x (mem_univ x)).differentiableAt
      (isOpen_univ.mem_nhds (mem_univ x)))
  have he := composite_support_projection hh isOpen_univ (sqNorm_vnormal m) 0
    (fun y _ => rep_of_cons hrep y) (mem_univ x) hg hp
  refine ⟨he, fun i => ?_⟩
  have hi := congrFun he i.succ
  rw [tangent_vnormal, tangent_vnormal] at hi
  simpa [Fin.tail] using hi

/-- Item `C/11_U/prose/013` (`companion/chapters/11_U.tex:83-87`), with display `disp/005`
(lines 84-86) and items `prose/014`, `prose/016`: the weaker-curvature version. For the family
$F(u,v)=\psi(u,v)+h(v)$ ($\psi$ convex with locally Lipschitz gradient, $h$ finite convex and
locally $C^{1,1}$ off $0$), full strong convexity is replaced by: $\psi(u,v)-\frac\mu2\|u\|^2$ is
convex (on the relevant open convex neighborhood $\Omega$; $\mu>0$; no curvature condition in
$v$), the relevant positive sublevels $\{F\le\ell\}$, $F_*<\ell\le F(x_0)$, are strictly convex,
and the minimizer is unique with $v_*=0$; a compact initial sublevel $K\subset\Omega$ is still
required. Then every infinite admissible run starting at $x_0$ converges:
$F(x_k)\to F_*$, $x_k\to x_*$. Library: `AdmissibleBFGSRun.tangential_composite_convergence`. -/
theorem tangential_family {m : ℕ} (F ψ : Vec (m + 1) → ℝ) (h : ℝ → ℝ)
    (hrep : ∀ (u : Vec m) (v : ℝ), F (Fin.cons v u) = ψ (Fin.cons v u) + h v)
    (hψ : ConvexOn ℝ univ ψ) (hψs : CenteredSmoothSublinear.LocallyC11On univ ψ)
    (hh : ConvexOn ℝ univ h) (hhs : ScalarLocallyC11On ({0}ᶜ : Set ℝ) h)
    (x0 : Vec (m + 1)) (K : Set (Vec (m + 1))) (hK_def : K = {x | F x ≤ F x0})
    (hK : IsCompact K) (Ω : Set (Vec (m + 1))) (hΩ : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (hKΩ : K ⊆ Ω) (μ : ℝ) (hμ : 0 < μ)
    (hstrongT : ConvexOn ℝ Ω (fun x => ψ x - (μ / 2) * sqNorm (Fin.tail x)))
    (xstar : Vec (m + 1)) (hmin : ∀ z, F xstar ≤ F z)
    (hunique : ∀ z, F z = F xstar → z = xstar) (hv : xstar 0 = 0)
    (hcontour : ∀ ℓ : ℝ, F xstar < ℓ → ℓ ≤ F x0 → StrictConvex ℝ {x | F x ≤ ℓ}) :
    ∀ R : AdmissibleBFGSRun (m + 1) F, R.x 0 = x0 →
      Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) ∧ Tendsto R.x atTop (𝓝 xstar) := by
  intro R hR0
  subst hK_def
  have hKR : R.initialSublevel = {x | F x ≤ F x0} := by
    rw [AdmissibleBFGSRun.initialSublevel, hR0]
  have hrep' := rep_of_cons hrep
  have hstrong' : ConvexOn ℝ Ω
      (fun x => ψ x - (μ / 2) * sqNorm (tangentProjection (vnormal m) x)) := by
    simpa only [sqNorm_tangent_vnormal] using hstrongT
  exact R.tangential_composite_convergence hΩ (hKR ▸ hK) (hKR ▸ hKΩ)
    (hψ.subset (subset_univ Ω) hΩc) ⟨hψs.1.mono (subset_univ Ω), hψs.2.mono (subset_univ Ω)⟩
    hh hhs (sqNorm_vnormal m) 0 hμ hstrong' (fun x _ => hrep' x) xstar hmin hunique
    (by rw [dot_vnormal, hv]) (fun ℓ h1 h2 => hcontour ℓ h1 (hR0 ▸ h2))

/-! ### The displays of Section 11.6 (proof of the weaker-curvature version)

The standing assumptions are those of `tangential_family` ("the weaker hypotheses in Section
11.1.1", line 327) and an infinite admissible run `R` starting at $x_0$; $S=\mathbb R^{n-1}\times
\{0\}$, so $P_S$ is `tangentProjection (vnormal m)`. -/

/-- Item `C/11_U/disp/020`, equation (11.16) (`companion/chapters/11_U.tex:328-330`): "Since
$\psi-\mu\|u\|^2/2$ and $h$ are convex,"
\[ d_k-(F_k-F_{k+1})\ge\frac\mu2\|P_Ss_k\|^2. \]
Library: `composite_projected_strong_convex`, `AdmissibleBFGSRun.projected_displacement_budget`. -/
theorem projected_budget {m : ℕ} (F ψ : Vec (m + 1) → ℝ) (h : ℝ → ℝ)
    (hrep : ∀ (u : Vec m) (v : ℝ), F (Fin.cons v u) = ψ (Fin.cons v u) + h v)
    (_hψ : ConvexOn ℝ univ ψ) (_hψs : CenteredSmoothSublinear.LocallyC11On univ ψ)
    (hh : ConvexOn ℝ univ h) (_hhs : ScalarLocallyC11On ({0}ᶜ : Set ℝ) h)
    (x0 : Vec (m + 1)) (K : Set (Vec (m + 1))) (hK_def : K = {x | F x ≤ F x0})
    (_hK : IsCompact K) (Ω : Set (Vec (m + 1))) (_hΩ : IsOpen Ω) (_hΩc : Convex ℝ Ω)
    (hKΩ : K ⊆ Ω) (μ : ℝ) (_hμ : 0 < μ)
    (hstrongT : ConvexOn ℝ Ω (fun x => ψ x - (μ / 2) * sqNorm (Fin.tail x)))
    (xstar : Vec (m + 1)) (_hmin : ∀ z, F xstar ≤ F z)
    (_hunique : ∀ z, F z = F xstar → z = xstar) (_hv : xstar 0 = 0)
    (_hcontour : ∀ ℓ : ℝ, F xstar < ℓ → ℓ ≤ F x0 → StrictConvex ℝ {x | F x ≤ ℓ})
    (R : AdmissibleBFGSRun (m + 1) F) (hR0 : R.x 0 = x0) (k : ℕ) :
    (μ / 2) * sqNorm (tangentProjection (vnormal m) (R.displacement k)) ≤
      R.d k - (F (R.x k) - F (R.x (k + 1))) := by
  subst hK_def
  have hx : ∀ j, R.x j ∈ Ω := fun j => hKΩ (by
    change F (R.x j) ≤ F x0
    rw [← hR0]
    exact R.objective_le_initial j)
  have hstrong' : ConvexOn ℝ Ω
      (fun x => ψ x - (μ / 2) * sqNorm (tangentProjection (vnormal m) x)) := by
    simpa only [sqNorm_tangent_vnormal] using hstrongT
  have hF := composite_projected_strong_convex hh (vnormal m) 0 hstrong'
    (fun x _ => rep_of_cons hrep x)
  exact R.projected_displacement_budget (tangentMap (vnormal m)) hF hx k

/-- Item `C/11_U/disp/021` (`companion/chapters/11_U.tex:333-335`): "At differentiable accepted
points,"
\[ P_Sy=P_S[\nabla\psi(z)-\nabla\psi(x)], \]
for the accepted pair $x=x_k$, $z=x_{k+1}$, $y=y_k=g_{k+1}-g_k$ ($\nabla\psi$ is
`coordinateGradient ψ`). Library: `composite_support_projection`. -/
theorem composite_secant_projection {m : ℕ} (F ψ : Vec (m + 1) → ℝ) (h : ℝ → ℝ)
    (hrep : ∀ (u : Vec m) (v : ℝ), F (Fin.cons v u) = ψ (Fin.cons v u) + h v)
    (_hψ : ConvexOn ℝ univ ψ) (hψs : CenteredSmoothSublinear.LocallyC11On univ ψ)
    (hh : ConvexOn ℝ univ h) (_hhs : ScalarLocallyC11On ({0}ᶜ : Set ℝ) h)
    (x0 : Vec (m + 1)) (K : Set (Vec (m + 1))) (_hK_def : K = {x | F x ≤ F x0})
    (_hK : IsCompact K) (Ω : Set (Vec (m + 1))) (_hΩ : IsOpen Ω) (_hΩc : Convex ℝ Ω)
    (_hKΩ : K ⊆ Ω) (μ : ℝ) (_hμ : 0 < μ)
    (_hstrongT : ConvexOn ℝ Ω (fun x => ψ x - (μ / 2) * sqNorm (Fin.tail x)))
    (xstar : Vec (m + 1)) (_hmin : ∀ z, F xstar ≤ F z)
    (_hunique : ∀ z, F z = F xstar → z = xstar) (_hv : xstar 0 = 0)
    (_hcontour : ∀ ℓ : ℝ, F xstar < ℓ → ℓ ≤ F x0 → StrictConvex ℝ {x | F x ≤ ℓ})
    (R : AdmissibleBFGSRun (m + 1) F) (_hR0 : R.x 0 = x0) (k : ℕ) :
    tangentProjection (vnormal m) (R.gradientChange k) =
      tangentProjection (vnormal m)
        (coordinateGradient ψ (R.x (k + 1)) - coordinateGradient ψ (R.x k)) := by
  have hgrad (x : Vec (m + 1)) : HasFDerivAt ψ (gradientFunctional (coordinateGradient ψ x)) x :=
    hasFDerivAt_coordinateGradient ((hψs.1 x (mem_univ x)).differentiableAt
      (isOpen_univ.mem_nhds (mem_univ x)))
  have hrep' : ∀ y ∈ (univ : Set (Vec (m + 1))), F y = ψ y + h (normalCoordinate (vnormal m) 0 y) :=
    fun y _ => rep_of_cons hrep y
  have h1 := composite_support_projection hh isOpen_univ (sqNorm_vnormal m) 0 hrep' (mem_univ _)
    (convex_supporting_inequality R.convex (R.hasGradient (k + 1))) (hgrad (R.x (k + 1)))
  have h0 := composite_support_projection hh isOpen_univ (sqNorm_vnormal m) 0 hrep' (mem_univ _)
    (convex_supporting_inequality R.convex (R.hasGradient k)) (hgrad (R.x k))
  change tangentMap (vnormal m) (R.g (k + 1) - R.g k) = tangentMap (vnormal m) _
  rw [map_sub, map_sub]
  exact congrArg₂ (fun v w : Vec (m + 1) => v - w) h1 h0

/-- Item `C/11_U/disp/022`, equation (11.17) (`companion/chapters/11_U.tex:336-340`): "Convex
$L$-smoothness of $\psi$ on the compact neighborhood, and monotonicity of the scalar subgradient
of $h$, give"
\[ \|P_Sy\|^2\le L[\nabla\psi(z)-\nabla\psi(x)]^Ts\le Lt \]
for every accepted pair ($x=x_k$, $z=x_{k+1}$, $s=s_k$, $y=y_k$, $t=t_k=y_k^Ts_k$), with one
constant $L>0$ for the run. Library: `exists_cocoercivity_constant_on_compact`,
`composite_secant_curvature_dominates`. -/
theorem composite_secant_bound {m : ℕ} (F ψ : Vec (m + 1) → ℝ) (h : ℝ → ℝ)
    (hrep : ∀ (u : Vec m) (v : ℝ), F (Fin.cons v u) = ψ (Fin.cons v u) + h v)
    (hψ : ConvexOn ℝ univ ψ) (hψs : CenteredSmoothSublinear.LocallyC11On univ ψ)
    (hh : ConvexOn ℝ univ h) (_hhs : ScalarLocallyC11On ({0}ᶜ : Set ℝ) h)
    (x0 : Vec (m + 1)) (K : Set (Vec (m + 1))) (hK_def : K = {x | F x ≤ F x0})
    (hK : IsCompact K) (Ω : Set (Vec (m + 1))) (_hΩ : IsOpen Ω) (_hΩc : Convex ℝ Ω)
    (_hKΩ : K ⊆ Ω) (μ : ℝ) (_hμ : 0 < μ)
    (_hstrongT : ConvexOn ℝ Ω (fun x => ψ x - (μ / 2) * sqNorm (Fin.tail x)))
    (xstar : Vec (m + 1)) (_hmin : ∀ z, F xstar ≤ F z)
    (_hunique : ∀ z, F z = F xstar → z = xstar) (_hv : xstar 0 = 0)
    (_hcontour : ∀ ℓ : ℝ, F xstar < ℓ → ℓ ≤ F x0 → StrictConvex ℝ {x | F x ≤ ℓ})
    (R : AdmissibleBFGSRun (m + 1) F) (hR0 : R.x 0 = x0) :
    ∃ L : ℝ, 0 < L ∧ ∀ k : ℕ,
      sqNorm (tangentProjection (vnormal m) (R.gradientChange k)) ≤
          L * dot (coordinateGradient ψ (R.x (k + 1)) - coordinateGradient ψ (R.x k))
            (R.displacement k) ∧
        L * dot (coordinateGradient ψ (R.x (k + 1)) - coordinateGradient ψ (R.x k))
            (R.displacement k) ≤ L * R.curvature k := by
  subst hK_def
  have hxK : ∀ j, R.x j ∈ {x | F x ≤ F x0} := fun j => by
    change F (R.x j) ≤ F x0
    rw [← hR0]
    exact R.objective_le_initial j
  obtain ⟨L, hL, hcoco⟩ := CenteredSmoothSublinear.exists_cocoercivity_constant_on_compact
    isOpen_univ hψ hψs hK
    (subset_univ _)
  refine ⟨L, hL, fun k => ?_⟩
  have hgrad (x : Vec (m + 1)) : HasFDerivAt ψ (gradientFunctional (coordinateGradient ψ x)) x :=
    hasFDerivAt_coordinateGradient ((hψs.1 x (mem_univ x)).differentiableAt
      (isOpen_univ.mem_nhds (mem_univ x)))
  have hrep' : ∀ y ∈ (univ : Set (Vec (m + 1))), F y = ψ y + h (normalCoordinate (vnormal m) 0 y) :=
    fun y _ => rep_of_cons hrep y
  have he : R.x (k + 1) - R.x k = R.displacement k := by
    rw [R.step]
    simp [AdmissibleBFGSRun.displacement]
  have hproj := composite_secant_projection F ψ h hrep hψ hψs hh _hhs x0 _ rfl hK Ω _hΩ _hΩc
    _hKΩ μ _hμ _hstrongT xstar _hmin _hunique _hv _hcontour R hR0 k
  have hc := hcoco (R.x k) (hxK k) (R.x (k + 1)) (hxK (k + 1))
  rw [he] at hc
  have hdom := composite_secant_curvature_dominates hh isOpen_univ (vnormal m) 0 hrep'
    (mem_univ (R.x k)) (mem_univ (R.x (k + 1)))
    (convex_supporting_inequality R.convex (R.hasGradient k))
    (convex_supporting_inequality R.convex (R.hasGradient (k + 1)))
    (hgrad (R.x k)) (hgrad (R.x (k + 1)))
  rw [he] at hdom
  refine ⟨?_, mul_le_mul_of_nonneg_left hdom hL.le⟩
  rw [hproj]
  exact (sqNorm_tangentProjection_le (sqNorm_vnormal m) _).trans hc

/-- A continuous function that is $\mu$-strongly convex on $\mathbb R^n$ ($\mu>0$) has strictly
convex sublevel sets. -/
theorem strictConvex_sublevel_of_strong {n : ℕ} {F : Vec n → ℝ} (hcont : Continuous F)
    {μ : ℝ} (hμ : 0 < μ) (hstrong : EuclideanStrongConvexOn univ μ F) (ℓ : ℝ) :
    StrictConvex ℝ {x | F x ≤ ℓ} := by
  intro x hx y hy hxy a b ha hb hab
  have hopen : IsOpen {z : Vec n | F z < ℓ} := isOpen_lt hcont continuous_const
  have hsub : {z : Vec n | F z < ℓ} ⊆ {z | F z ≤ ℓ} := fun z (hz : F z < ℓ) =>
    show F z ≤ ℓ from le_of_lt hz
  apply interior_mono hsub
  rw [hopen.interior_eq]
  have hc := hstrong.2 (mem_univ x) (mem_univ y) ha.le hb.le hab
  simp only [smul_eq_mul] at hc
  have ha' : a = 1 - b := by linarith
  have hsq := sqNorm_convex_combination x y b
  rw [← ha'] at hsq
  rw [hsq] at hc
  have hpos : 0 < sqNorm (y - x) := lt_of_le_of_ne (sqNorm_nonneg _)
    (fun h => hxy (sub_eq_zero.mp ((CertificateGeometry.sqNorm_eq_zero_iff _).mp h.symm)).symm)
  have hx' : F x ≤ ℓ := hx
  have hy' : F y ≤ ℓ := hy
  change F (a • x + b • y) < ℓ
  have hab' : 0 < μ / 2 * (b * a * sqNorm (y - x)) := by positivity
  have h1 : a * F x ≤ a * ℓ := mul_le_mul_of_nonneg_left hx' ha.le
  have h2 : b * F y ≤ b * ℓ := mul_le_mul_of_nonneg_left hy' hb.le
  have h4 : a * ℓ + b * ℓ = ℓ := by rw [← add_mul, hab, one_mul]
  nlinarith

/-- Item `C/11_U/prose/030` (`companion/chapters/11_U.tex:352-353`): "A quadratic-plus-absolute-value
objective is included". For $F(u,v)=\frac12(\|u\|^2+v^2)+|v|$ in any dimension $n=m+1$, with
$\psi=\frac12\|x\|^2$ (`NormalSpike.quadratic`) and $h=|\cdot|$: $\psi$ is convex with locally
Lipschitz gradient, $h$ is convex and locally $C^{1,1}$ off $0$, $F$ is $1$-strongly convex,
$\psi-\frac12\|u\|^2$ is convex, $0$ is the unique minimizer (with $v_*=0$), every sublevel is
compact and strictly convex; so both versions of Section 11.1.1 apply and every infinite
admissible run converges: $F(x_k)\to0$, $x_k\to0$. -/
theorem quadratic_abs_included (m : ℕ) (F : Vec (m + 1) → ℝ)
    (hF_def : ∀ (u : Vec m) (v : ℝ), F (Fin.cons v u) = (1 / 2) * (sqNorm u + v ^ 2) + |v|) :
    (∀ (u : Vec m) (v : ℝ),
        F (Fin.cons v u) = NormalSpike.quadratic (Fin.cons v u) + |v|) ∧
      ConvexOn ℝ univ (NormalSpike.quadratic (n := m + 1)) ∧
      CenteredSmoothSublinear.LocallyC11On univ (NormalSpike.quadratic (n := m + 1)) ∧
      ConvexOn ℝ univ (fun v : ℝ => |v|) ∧ ScalarLocallyC11On ({0}ᶜ : Set ℝ) (fun v : ℝ => |v|) ∧
      EuclideanStrongConvexOn univ 1 F ∧
      ConvexOn ℝ univ
        (fun x : Vec (m + 1) => NormalSpike.quadratic x - (1 / 2) * sqNorm (Fin.tail x)) ∧
      (∀ z, F 0 ≤ F z) ∧ (∀ z, F z = F 0 → z = 0) ∧ (0 : Vec (m + 1)) 0 = 0 ∧
      (∀ c, IsCompact {x | F x ≤ c} ∧ StrictConvex ℝ {x | F x ≤ c}) ∧
      ∀ R : AdmissibleBFGSRun (m + 1) F,
        Tendsto (fun k => F (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0) := by
  have hsplit : ∀ (u : Vec m) (v : ℝ),
      F (Fin.cons v u) = NormalSpike.quadratic (Fin.cons v u) + |v| := by
    intro u v
    rw [hF_def, NormalSpike.quadratic]
    have hs : sqNorm (Fin.cons v u : Vec (m + 1)) = v ^ 2 + sqNorm u := by
      simp only [sqNorm, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [hs]
    ring
  have hrep := rep_of_cons (ψ := NormalSpike.quadratic) (h := fun v : ℝ => |v|) hsplit
  have habs : ConvexOn ℝ univ (fun v : ℝ => |v|) := by
    simpa only [Real.norm_eq_abs] using (convexOn_univ_norm : ConvexOn ℝ univ (norm : ℝ → ℝ))
  have habsC : ScalarLocallyC11On ({0}ᶜ : Set ℝ) (fun v : ℝ => |v|) :=
    NormalSpike.scalar_locallyC11_of_contDiffOn isClosed_singleton.isOpen_compl
      (contDiffOn_abs (fun _ h => h))
  have hpen : ConvexOn ℝ univ (fun x : Vec (m + 1) => |normalCoordinate (vnormal m) 0 x|) :=
    convex_normal_composite habs (vnormal m) 0
  have hFeq : F = fun x => NormalSpike.quadratic x + |normalCoordinate (vnormal m) 0 x| :=
    funext hrep
  have hconv : ConvexOn ℝ univ F := by
    rw [hFeq]
    exact NormalSpike.quadratic_convex.add hpen
  have hstrong : EuclideanStrongConvexOn univ 1 F := by
    unfold EuclideanStrongConvexOn
    convert hpen using 1
    ext x
    simp only [hFeq, NormalSpike.quadratic]
    ring
  have hlow (x : Vec (m + 1)) : (1 / 2) * sqNorm x ≤ F x := by
    simp only [hFeq, NormalSpike.quadratic]
    linarith [abs_nonneg (normalCoordinate (vnormal m) 0 x)]
  have hF0 : F 0 = 0 := by
    rw [hFeq]
    simp [NormalSpike.quadratic, sqNorm, normalCoordinate, dot]
  have hmin : ∀ z, F 0 ≤ F z := fun z => by
    rw [hF0]
    exact (mul_nonneg (by norm_num) (sqNorm_nonneg z)).trans (hlow z)
  have hunique : ∀ z, F z = F 0 → z = 0 := by
    intro z hz
    have hb := hlow z
    rw [hz, hF0] at hb
    exact (CertificateGeometry.sqNorm_eq_zero_iff z).mp
      (le_antisymm (by nlinarith [sqNorm_nonneg z]) (sqNorm_nonneg z))
  have hcont : Continuous F := convex_continuous hconv
  have hcpt (c : ℝ) : IsCompact {x | F x ≤ c} :=
    Localization.sublevel_compact hconv 0 hmin hunique c
  have hψT : ConvexOn ℝ univ
      (fun x : Vec (m + 1) => NormalSpike.quadratic x - (1 / 2) * sqNorm (Fin.tail x)) := by
    have hsq : ConvexOn ℝ univ (fun t : ℝ => (1 / 2) * t ^ 2) :=
      (even_two.convexOn_pow).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)
    convert convex_normal_composite hsq (vnormal m) 0 using 1
    ext x
    rw [normalCoordinate_vnormal, NormalSpike.quadratic]
    have hs : sqNorm x = x 0 ^ 2 + sqNorm (Fin.tail x) := by
      simp only [sqNorm, Fin.sum_univ_succ, Fin.tail]
    rw [hs]
    ring
  refine ⟨hsplit, NormalSpike.quadratic_convex, NormalSpike.quadratic_locallyC11, habs, habsC,
    hstrong, hψT, hmin, hunique, rfl, fun c => ⟨hcpt c,
      strictConvex_sublevel_of_strong hcont one_pos hstrong c⟩, fun R => ?_⟩
  have h := immediate_family F NormalSpike.quadratic (fun v : ℝ => |v|) hsplit
    NormalSpike.quadratic_convex NormalSpike.quadratic_locallyC11 habs habsC (R.x 0)
    _ rfl (hcpt _) univ isOpen_univ convex_univ (subset_univ _) 1 one_pos hstrong 0 hmin rfl
    R rfl
  simpa only [hF0] using h

/-! ### The displays of Section 11.5 (the common proof of Theorems 11.1 and 11.2)

Standing assumptions (the "common argument", lines 171 and 191-192): `F` convex, an infinite
admissible run `R` in a compact sublevel $K=\{F\le c\}$, an open convex neighborhood $\Omega$ of
$K$ on which $F$ is $\mu$-strongly convex, a unit vector $a$, $b\in\mathbb R$ with
$r(x)=a^Tx-b$, a field $A$ with $P_Sg=A(x)$ for $g\in\partial F(x)$, $x\in\Omega$, Lipschitz on
$\Omega$, and a closed exceptional scalar set $E$ such that $F$ is locally $C^{1,1}$ on
$\Omega\setminus\{r\in E\}$. Theorem 11.2 is the case $b=0$ (plus nondifferentiability on
$\{r\in E\}$); Theorem 11.1 is the case $E=\{0\}$, $c=F(x_0)$ (plus the unique minimizer
$x_*\in P$). From display (11.12) on, the objects chosen in the proof are added: $U$ (columns an
orthonormal basis of $S$), $\delta>0$ and the cutoff $\tau:\mathbb R\to[0,1]$, Lipschitz with
constant $\operatorname{Lip}(\tau)$ (`Lτ`), zero where $\operatorname{dist}(r,E)\le\delta/4$ and
one where $\operatorname{dist}(r,E)\ge\delta/2$ (written with $|t-e|$, $e\in E$, so that $E=\emptyset$
is included, as in the TeX). The reductio hypotheses (no affine-critical cluster point; $\ell>F_*$)
are not used by displays (11.10), (11.11), (11.12)-(11.15); they are omitted there, which only
strengthens the statements. Display `disp/012` uses them and is stated with them. -/

/-- The library's regular region is $\Omega\setminus\{x:a^Tx-b\in E\}$. -/
theorem regularRegion_eq {n : ℕ} (Ω : Set (Vec n)) (a : Vec n) (b : ℝ) (E : Set ℝ) :
    regularRegion Ω a b E = Ω \ {x | dot a x - b ∈ E} := by
  ext x
  simp only [regularRegion, normalCoordinate, mem_inter_iff, mem_setOf_eq, mem_diff]

/-- The run stays in $\Omega$. -/
theorem run_mem {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) {K Ω : Set (Vec n)}
    (hrun : ∀ k, R.x k ∈ K) (hKΩ : K ⊆ Ω) : ∀ k, R.x k ∈ Ω := fun k => hKΩ (hrun k)

/-- Item `C/11_U/disp/009`, equation (11.10) (`companion/chapters/11_U.tex:180-183`): "Strong
convexity and convexity give"
\[ d_k-(F_k-F_{k+1})\ge\frac\mu2\|s_k\|^2,\qquad t_k\ge\mu\|s_k\|^2. \]
Library: `AdmissibleBFGSRun.strong_displacement_budget`, `strong_curvature_bound`. -/
theorem strong_budget {n : ℕ} (F : Vec n → ℝ) (_hF : ConvexOn ℝ univ F)
    (R : AdmissibleBFGSRun n F)
    (c : ℝ) (K : Set (Vec n)) (_hK_def : K = {x | F x ≤ c}) (_hK : IsCompact K)
    (hrun : ∀ k, R.x k ∈ K)
    (Ω : Set (Vec n)) (_hΩ : IsOpen Ω) (_hΩc : Convex ℝ Ω) (hKΩ : K ⊆ Ω)
    (μ : ℝ) (_hμ : 0 < μ) (hstrong : EuclideanStrongConvexOn Ω μ F)
    (a : Vec n) (_ha : sqNorm a = 1) (b : ℝ) (A : Vec n → Vec n)
    (_hA : ∀ x ∈ Ω, ∀ g ∈ ConvexSubdifferential.subdifferential F x,
      tangentProjection a g = A x)
    (L : ℝ≥0) (_hLip : LipschitzOnWith L A Ω) (E : Set ℝ) (_hE : IsClosed E)
    (_hsmooth : CenteredSmoothSublinear.LocallyC11On (Ω \ {x | dot a x - b ∈ E}) F)
    (k : ℕ) :
    R.d k - (F (R.x k) - F (R.x (k + 1))) ≥ (μ / 2) * sqNorm (R.displacement k) ∧
      R.curvature k ≥ μ * sqNorm (R.displacement k) :=
  ⟨R.strong_displacement_budget hstrong (run_mem R hrun hKΩ) k,
    R.strong_curvature_bound hstrong (run_mem R hrun hKΩ) k⟩

/-- Item `C/11_U/disp/010`, equation (11.11) (`companion/chapters/11_U.tex:195-198`): "The
common tangential projection and its Lipschitz constant $L_A$ imply"
\[ \|P_Sy_k\|^2=\|A(x_{k+1})-A(x_k)\|^2\le L_A^2\|s_k\|^2\le\frac{L_A^2}{\mu}t_k. \]
$L_A\ge0$ is a Euclidean Lipschitz constant of $A$ on $\Omega$
($\|A(z)-A(x)\|\le L_A\|z-x\|$, Euclidean norms `Real.sqrt (sqNorm ·)`). Library:
`AdmissibleBFGSRun.tangent_gradientChange`, `strong_curvature_bound`. -/
theorem tangent_secant {n : ℕ} (F : Vec n → ℝ) (_hF : ConvexOn ℝ univ F)
    (R : AdmissibleBFGSRun n F)
    (c : ℝ) (K : Set (Vec n)) (_hK_def : K = {x | F x ≤ c}) (_hK : IsCompact K)
    (hrun : ∀ k, R.x k ∈ K)
    (Ω : Set (Vec n)) (_hΩ : IsOpen Ω) (_hΩc : Convex ℝ Ω) (hKΩ : K ⊆ Ω)
    (μ : ℝ) (hμ : 0 < μ) (hstrong : EuclideanStrongConvexOn Ω μ F)
    (a : Vec n) (_ha : sqNorm a = 1) (b : ℝ) (A : Vec n → Vec n)
    (hA : ∀ x ∈ Ω, ∀ g ∈ ConvexSubdifferential.subdifferential F x,
      tangentProjection a g = A x)
    (L : ℝ≥0) (_hLip : LipschitzOnWith L A Ω) (E : Set ℝ) (_hE : IsClosed E)
    (_hsmooth : CenteredSmoothSublinear.LocallyC11On (Ω \ {x | dot a x - b ∈ E}) F)
    (LA : ℝ) (_hLA0 : 0 ≤ LA)
    (hLA : ∀ x ∈ Ω, ∀ z ∈ Ω, Real.sqrt (sqNorm (A z - A x)) ≤ LA * Real.sqrt (sqNorm (z - x)))
    (k : ℕ) :
    sqNorm (tangentProjection a (R.gradientChange k)) = sqNorm (A (R.x (k + 1)) - A (R.x k)) ∧
      sqNorm (A (R.x (k + 1)) - A (R.x k)) ≤ LA ^ 2 * sqNorm (R.displacement k) ∧
      LA ^ 2 * sqNorm (R.displacement k) ≤ LA ^ 2 / μ * R.curvature k := by
  have hx := run_mem R hrun hKΩ
  have he : R.x (k + 1) - R.x k = R.displacement k := by
    rw [R.step]
    simp [AdmissibleBFGSRun.displacement]
  refine ⟨by rw [R.tangent_gradientChange hx (fun x hx g hg => hA x hx g hg) k], ?_, ?_⟩
  · have h := hLA _ (hx k) _ (hx (k + 1))
    rw [he] at h
    have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
    rwa [Real.sq_sqrt (sqNorm_nonneg _), mul_pow, Real.sq_sqrt (sqNorm_nonneg _)] at h2
  · have hs := R.strong_curvature_bound hstrong hx k
    have hs' : sqNorm (R.displacement k) ≤ R.curvature k / μ :=
      (le_div_iff₀ hμ).mpr (by linarith)
    calc LA ^ 2 * sqNorm (R.displacement k) ≤ LA ^ 2 * (R.curvature k / μ) :=
          mul_le_mul_of_nonneg_left hs' (sq_nonneg _)
      _ = LA ^ 2 / μ * R.curvature k := by ring

/-- Item `C/11_U/disp/011` (`companion/chapters/11_U.tex:213-215`): "For Theorem 11.1, if
$p\in P$ and $g\in\partial F(p)$, strong monotonicity with $0\in\partial F(x_*)$ gives"
\[ A(p)^T(p-x_*)=g^T(p-x_*)\ge\mu\|p-x_*\|^2. \]
Under the hypotheses of Theorem 11.1, for $p\in\Omega\cap P$ (in the proof $p$ lies in the
cluster set $\Gamma\subset\Omega$). Library: `strong_support_monotonicity`. -/
theorem plane_monotonicity {n : ℕ} (F : Vec n → ℝ) (_hF : ConvexOn ℝ univ F)
    (a : Vec n) (_ha : sqNorm a = 1) (b : ℝ) (P : Set (Vec n)) (hP : P = {x | dot a x = b})
    (xstar : Vec n) (hmin : ∀ z, F xstar ≤ F z) (_hunique : ∀ z, F z = F xstar → z = xstar)
    (hplane : xstar ∈ P)
    (x0 : Vec n) (K : Set (Vec n)) (hK_def : K = {x | F x ≤ F x0}) (_hK : IsCompact K)
    (Ω : Set (Vec n)) (_hΩ : IsOpen Ω) (_hΩc : Convex ℝ Ω) (hKΩ : K ⊆ Ω)
    (μ : ℝ) (_hμ : 0 < μ) (hstrong : EuclideanStrongConvexOn Ω μ F)
    (A : Vec n → Vec n)
    (hA : ∀ x ∈ Ω, ∀ g ∈ ConvexSubdifferential.subdifferential F x,
      tangentProjection a g = A x)
    (L : ℝ≥0) (_hLip : LipschitzOnWith L A Ω)
    (_hsmooth : CenteredSmoothSublinear.LocallyC11On (Ω \ P) F)
    (p : Vec n) (hpΩ : p ∈ Ω) (hpP : p ∈ P)
    (g : Vec n) (hg : g ∈ ConvexSubdifferential.subdifferential F p) :
    dot (A p) (p - xstar) = dot g (p - xstar) ∧ dot g (p - xstar) ≥ μ * sqNorm (p - xstar) := by
  subst hP hK_def
  have hstar : xstar ∈ Ω := hKΩ (hmin x0)
  have hz : Homogeneous.Supports F xstar 0 :=
    ConvexSubdifferential.zero_mem_iff_global_minimum.mpr hmin
  have hmono := strong_support_monotonicity hstrong hstar hpΩ hz hg
  rw [sub_zero] at hmono
  have hpa : dot a (p - xstar) = 0 := by
    have hp' : dot a p = b := hpP
    have hs' : dot a xstar = b := hplane
    change a ⬝ᵥ (p - xstar) = 0
    rw [dotProduct_sub]
    change dot a p - dot a xstar = 0
    rw [hp', hs', sub_self]
  have hgA : g = A p + dot a g • a := by
    rw [← hA p hpΩ g hg, tangentProjection]
    abel
  refine ⟨?_, hmono⟩
  conv_rhs => rw [hgA]
  change A p ⬝ᵥ (p - xstar) = (A p + dot a g • a) ⬝ᵥ (p - xstar)
  rw [add_dotProduct, smul_dotProduct]
  change dot (A p) (p - xstar) = dot (A p) (p - xstar) + dot a g • dot a (p - xstar)
  rw [hpa, smul_zero, add_zero]

/-- The zero set $Z=\{p\in\Gamma:A(p)=0\}$ of a compact $\Gamma\subset\Omega$ on which $A$ is
continuous is compact. -/
theorem zero_set_compact {n : ℕ} {Ω Γ : Set (Vec n)} {A : Vec n → Vec n}
    (hAc : ContinuousOn A Ω) (hΓ : IsCompact Γ) (hΓΩ : Γ ⊆ Ω) :
    IsCompact {p | p ∈ Γ ∧ A p = 0} :=
  hΓ.of_isClosed_subset ((hAc.mono hΓΩ).preimage_isClosed_of_isClosed hΓ.isClosed
    isClosed_singleton) (fun _ hp => hp.1)

/-- General form of display `disp/012` for Theorem 11.2 (lines 208-220): if every point of
$\Omega$ with $r(p)\in E$ is nondifferentiable, $P_S\partial F=A$ on $\Omega$ with $A$
continuous, and the compact set $\Gamma\subset\Omega$ contains no affine-critical point, then
$Z=\{p\in\Gamma:A(p)=0\}$ is compact and $r(Z)\cap E=\emptyset$. -/
theorem zero_set_parallel_general {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    {Ω : Set (Vec n)} (a : Vec n) (b : ℝ) (E : Set ℝ) (A : Vec n → Vec n)
    (hA : ∀ x ∈ Ω, ∀ g ∈ ConvexSubdifferential.subdifferential F x,
      tangentProjection a g = A x)
    (hAc : ContinuousOn A Ω) (hsingular : ∀ p ∈ Ω, dot a p - b ∈ E → ¬DifferentiableAt ℝ F p)
    (Γ : Set (Vec n)) (hΓ : IsCompact Γ) (hΓΩ : Γ ⊆ Ω)
    (hno : ∀ p ∈ Γ, (0 : Vec n) ∉ affineSpan ℝ (ConvexSubdifferential.subdifferential F p))
    (Z : Set (Vec n)) (hZ : Z = {p | p ∈ Γ ∧ A p = 0}) :
    IsCompact Z ∧ Disjoint ((fun x => dot a x - b) '' Z) E := by
  subst hZ
  refine ⟨zero_set_compact hAc hΓ hΓΩ, Set.disjoint_left.mpr ?_⟩
  rintro t ⟨p, ⟨hpΓ, hAp⟩, rfl⟩ hE
  apply hno p hpΓ
  exact (affine_critical_iff_tangent_zero hF (fun g hg => hA p (hΓΩ hpΓ) g hg)
    (hsingular p (hΓΩ hpΓ) hE)).mpr hAp

/-- General form of display `disp/012` for Theorem 11.1 (lines 212-220): with $x_*\in P\cap
\Omega$ a minimizer, $F$ $\mu$-strongly convex on $\Omega$, $P_S\partial F=A$ on $\Omega$ with $A$
continuous, and a compact $\Gamma\subset\Omega$ on which $F$ equals a level $\ell>F_*$, the set
$Z=\{p\in\Gamma:A(p)=0\}$ is compact and $r(Z)\cap\{0\}=\emptyset$. -/
theorem zero_set_hyperplane_general {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    {Ω : Set (Vec n)} {μ : ℝ} (hμ : 0 < μ) (hstrong : EuclideanStrongConvexOn Ω μ F)
    (a : Vec n) (b : ℝ) (A : Vec n → Vec n)
    (hA : ∀ x ∈ Ω, ∀ g ∈ ConvexSubdifferential.subdifferential F x,
      tangentProjection a g = A x)
    (hAc : ContinuousOn A Ω) (xstar : Vec n) (hmin : ∀ z, F xstar ≤ F z) (hstar : xstar ∈ Ω)
    (hplane : dot a xstar = b)
    (Γ : Set (Vec n)) (hΓ : IsCompact Γ) (hΓΩ : Γ ⊆ Ω) (ℓ : ℝ) (hlevel : ∀ p ∈ Γ, F p = ℓ)
    (hℓ : F xstar < ℓ)
    (Z : Set (Vec n)) (hZ : Z = {p | p ∈ Γ ∧ A p = 0}) :
    IsCompact Z ∧ Disjoint ((fun x => dot a x - b) '' Z) {0} := by
  subst hZ
  refine ⟨zero_set_compact hAc hΓ hΓΩ, Set.disjoint_left.mpr ?_⟩
  rintro t ⟨p, ⟨hpΓ, hAp⟩, rfl⟩ h0
  have hpp : dot a p = dot a xstar := by
    have h0' : dot a p - b = 0 := h0
    linarith
  have he := tangent_zero_on_minimizer_plane hF hμ hstrong hstar (hΓΩ hpΓ) hmin hpp
    (fun g hg => (hA p (hΓΩ hpΓ) g hg).trans hAp)
  have hv := hlevel p hpΓ
  rw [he] at hv
  linarith

/-- Item `C/11_U/disp/012` (`companion/chapters/11_U.tex:218-220`), case of Theorem 11.2:
"In either case the compact set $Z=\{p\in\Gamma:A(p)=0\}$ has scalar image $r(Z)$ disjoint from
the closed set $E$." Under the hypotheses of Theorem 11.2 ($r(x)=a^Tx$), for a run in $K$ whose
cluster set $\Gamma$ is assumed (for contradiction, line 187) to contain no affine-critical point.
These hypotheses cannot all hold (Theorem 11.2); the content is the general form
`zero_set_parallel_general`, whose hypotheses are satisfiable. -/
theorem zero_set_parallel {n : ℕ} (F : Vec n → ℝ) (hF : ConvexOn ℝ univ F)
    (_hattained : ∃ xstar, ∀ z, F xstar ≤ F z)
    (c : ℝ) (K : Set (Vec n)) (_hK_def : K = {x | F x ≤ c}) (hK : IsCompact K)
    (Ω : Set (Vec n)) (_hΩ : IsOpen Ω) (_hΩc : Convex ℝ Ω) (hKΩ : K ⊆ Ω)
    (μ : ℝ) (_hμ : 0 < μ) (_hstrong : EuclideanStrongConvexOn Ω μ F)
    (a : Vec n) (_ha : sqNorm a = 1) (E : Set ℝ) (_hE : IsClosed E)
    (Sg : Set (Vec n)) (hSg : Sg = {x | dot a x ∈ E})
    (hsingular : ∀ p ∈ Ω, p ∈ Sg → ¬DifferentiableAt ℝ F p)
    (_hsmooth : CenteredSmoothSublinear.LocallyC11On (Ω \ Sg) F)
    (A : Vec n → Vec n)
    (hA : ∀ x ∈ Ω, tangentProjection a '' ConvexSubdifferential.subdifferential F x = {A x})
    (L : ℝ≥0) (hLip : LipschitzOnWith L A Ω)
    (R : AdmissibleBFGSRun n F) (hrun : ∀ k, R.x k ∈ K)
    (Γ : Set (Vec n)) (hΓ_def : Γ = {p | MapClusterPt p atTop R.x})
    (hno : ∀ p ∈ Γ, (0 : Vec n) ∉ affineSpan ℝ (ConvexSubdifferential.subdifferential F p))
    (Z : Set (Vec n)) (hZ : Z = {p | p ∈ Γ ∧ A p = 0}) :
    IsCompact Z ∧ Disjoint ((fun x => dot a x) '' Z) E := by
  subst hSg
  have hΓK : Γ ⊆ K := by
    rw [hΓ_def]
    exact ClusterSetGeometry.clusterSet_subset_of_closed R.x hK.isClosed hrun
  have hΓ : IsCompact Γ := by
    rw [hΓ_def]
    exact ClusterSetGeometry.isCompact_clusterSet R.x hK hrun
  have h := zero_set_parallel_general hF a 0 E A (fun x hx g hg => tangent_of_image_eq hA x hx g hg)
    hLip.continuousOn (fun p hp he => hsingular p hp (by simpa only [sub_zero] using he))
    Γ hΓ (hΓK.trans hKΩ) hno Z hZ
  simpa only [sub_zero] using h

/-- Item `C/11_U/disp/012` (`companion/chapters/11_U.tex:218-220`), case of Theorem 11.1
($r(x)=a^Tx-b$, $E=\{0\}$): under the hypotheses of Theorem 11.1, for a run starting at $x_0$
whose values converge to $\ell$ with $\ell>F_*$ (assumed for contradiction, line 189),
$Z=\{p\in\Gamma:A(p)=0\}$ is compact and $r(Z)\cap\{0\}=\emptyset$. These hypotheses cannot all
hold (Theorem 11.1); the content is `zero_set_hyperplane_general`. -/
theorem zero_set_hyperplane {n : ℕ} (F : Vec n → ℝ) (hF : ConvexOn ℝ univ F)
    (a : Vec n) (_ha : sqNorm a = 1) (b : ℝ) (P : Set (Vec n)) (hP : P = {x | dot a x = b})
    (xstar : Vec n) (hmin : ∀ z, F xstar ≤ F z) (_hunique : ∀ z, F z = F xstar → z = xstar)
    (hplane : xstar ∈ P)
    (x0 : Vec n) (K : Set (Vec n)) (hK_def : K = {x | F x ≤ F x0}) (hK : IsCompact K)
    (Ω : Set (Vec n)) (_hΩ : IsOpen Ω) (_hΩc : Convex ℝ Ω) (hKΩ : K ⊆ Ω)
    (μ : ℝ) (hμ : 0 < μ) (hstrong : EuclideanStrongConvexOn Ω μ F)
    (A : Vec n → Vec n)
    (hA : ∀ x ∈ Ω, ∀ g ∈ ConvexSubdifferential.subdifferential F x,
      tangentProjection a g = A x)
    (L : ℝ≥0) (hLip : LipschitzOnWith L A Ω)
    (_hsmooth : CenteredSmoothSublinear.LocallyC11On (Ω \ P) F)
    (R : AdmissibleBFGSRun n F) (hR0 : R.x 0 = x0)
    (ℓ : ℝ) (hℓ : Tendsto (fun k => F (R.x k)) atTop (𝓝 ℓ)) (hlt : F xstar < ℓ)
    (Γ : Set (Vec n)) (hΓ_def : Γ = {p | MapClusterPt p atTop R.x})
    (Z : Set (Vec n)) (hZ : Z = {p | p ∈ Γ ∧ A p = 0}) :
    IsCompact Z ∧ Disjoint ((fun x => dot a x - b) '' Z) {0} := by
  subst hP
  have hrun : ∀ k, R.x k ∈ K := fun k => by
    rw [hK_def]
    change F (R.x k) ≤ F x0
    rw [← hR0]
    exact R.objective_le_initial k
  have hΓK : Γ ⊆ K := by
    rw [hΓ_def]
    exact ClusterSetGeometry.clusterSet_subset_of_closed R.x hK.isClosed hrun
  have hΓ : IsCompact Γ := by
    rw [hΓ_def]
    exact ClusterSetGeometry.isCompact_clusterSet R.x hK hrun
  have hstar : xstar ∈ Ω := hKΩ (by rw [hK_def]; exact hmin x0)
  exact zero_set_hyperplane_general hF hμ hstrong a b A hA hLip.continuousOn xstar hmin hstar
    hplane Γ hΓ (hΓK.trans hKΩ) ℓ
    (fun p hp => R.value_of_cluster hℓ (by rw [hΓ_def] at hp; exact hp)) hlt Z hZ

/-- Undisplayed step of the proof (lines 226-230, not a register item): a cutoff
$\tau:\mathbb R\to[0,1]$, Lipschitz, zero where $\operatorname{dist}(r,E)\le\delta/4$ and one
where $\operatorname{dist}(r,E)\ge\delta/2$, exists for every closed $E$ and $\delta>0$; for
$E\neq\emptyset$ it is the piecewise-linear cutoff composed with the distance function
(`distanceCutoff E (δ/4)`), for $E=\emptyset$ it is identically one. -/
theorem cutoff_exists (E : Set ℝ) (_hE : IsClosed E) (δ : ℝ) (hδ : 0 < δ) :
    ∃ τ : ℝ → ℝ, ∃ Lτ : ℝ≥0, LipschitzWith Lτ τ ∧ (∀ t, 0 ≤ τ t ∧ τ t ≤ 1) ∧
      (∀ t e, e ∈ E → |t - e| ≤ δ / 4 → τ t = 0) ∧
      (∀ t, (∀ e ∈ E, δ / 2 ≤ |t - e|) → τ t = 1) := by
  rcases E.eq_empty_or_nonempty with rfl | hEn
  · exact ⟨fun _ => 1, 0, LipschitzWith.const 1, fun _ => ⟨by norm_num, le_rfl⟩,
      fun _ _ he => absurd he (not_mem_empty _), fun _ _ => rfl⟩
  have hδ4 : 0 < δ / 4 := by positivity
  refine ⟨distanceCutoff E (δ / 4), _, distanceCutoff_lipschitz hδ4, distanceCutoff_bounds E _,
    fun t e he hte => distanceCutoff_zero hδ4
      ((Metric.infDist_le_dist_of_mem he).trans (by simpa only [Real.dist_eq] using hte)),
    fun t ht => distanceCutoff_one hδ4 ?_⟩
  have hle : δ / 2 ≤ Metric.infDist t E := by
    rw [Metric.le_infDist hEn]
    intro e he
    simpa only [Real.dist_eq] using ht e he
  linarith

/-- The last frame-coordinate vector $e_n$ of $\mathbb R^{m+1}$ (the frame has $m+1$ columns;
$m=n-1$ when $U$ is a basis of $S$). -/
def lastBasis (m : ℕ) : Vec (m + 1) := Pi.single (Fin.last m) 1

/-- The frame $[\,U,\ ta\,]$: the columns of $U$, then the normal column $ta$ (display (11.12)
with $t=\tau(r(x))$). -/
def frame {n m : ℕ} (U : Matrix (Fin n) (Fin m) ℝ) (a : Vec n) (t : ℝ) :
    Matrix (Fin n) (Fin (m + 1)) ℝ :=
  Matrix.of fun i j => Fin.lastCases (t * a i) (fun j' => U i j') j

theorem frame_castSucc {n m : ℕ} (U : Matrix (Fin n) (Fin m) ℝ) (a : Vec n) (t : ℝ)
    (i : Fin n) (j : Fin m) : frame U a t i (Fin.castSucc j) = U i j := by
  simp [frame]

theorem frame_last {n m : ℕ} (U : Matrix (Fin n) (Fin m) ℝ) (a : Vec n) (t : ℝ) (i : Fin n) :
    frame U a t i (Fin.last m) = t * a i := by
  simp [frame]

/-- Item `C/11_U/disp/013`, equation (11.12) (`companion/chapters/11_U.tex:241-243`): "Let the
columns of $U$ be an orthonormal basis of $S$, and set $V(x)=[\,U,\ \tau(r(x))a\,]$." For
$U$ with $U^TU=I$, $UU^T=P_S$ and $V(x)=$ `frame U a (τ (dot a x - b))`, the first $m$ columns of
$V(x)$ are the columns of $U$ and the last column is $\tau(r(x))a$. -/
theorem frame_columns {n m : ℕ} (a : Vec n) (_ha : sqNorm a = 1) (b : ℝ)
    (U : Matrix (Fin n) (Fin m) ℝ) (_hU : Uᵀ * U = 1)
    (_hUS : ∀ v, (U * Uᵀ) *ᵥ v = tangentProjection a v) (τ : ℝ → ℝ)
    (V : Vec n → Matrix (Fin n) (Fin (m + 1)) ℝ) (hV : ∀ x, V x = frame U a (τ (dot a x - b)))
    (x : Vec n) :
    (∀ i j, V x i (Fin.castSucc j) = U i j) ∧ (∀ i, V x i (Fin.last m) = τ (dot a x - b) * a i) :=
  ⟨fun i j => by rw [hV, frame_castSucc], fun i => by rw [hV, frame_last]⟩

theorem frame_transpose_mulVec {n m : ℕ} (U : Matrix (Fin n) (Fin m) ℝ) (a : Vec n) (t : ℝ)
    (y : Vec n) :
    (frame U a t)ᵀ *ᵥ y = (Fin.snoc (Uᵀ *ᵥ y) (t * dot a y) : Vec (m + 1)) := by
  ext j
  refine Fin.lastCases ?_ (fun j' => ?_) j
  · simp only [Fin.snoc_last, Matrix.mulVec, dotProduct, transpose_apply, frame_last, dot,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · simp only [Fin.snoc_castSucc, Matrix.mulVec, dotProduct, transpose_apply, frame_castSucc]

theorem sqNorm_snoc {m : ℕ} (v : Vec m) (c : ℝ) :
    sqNorm (Fin.snoc v c : Vec (m + 1)) = sqNorm v + c ^ 2 := by
  simp only [sqNorm, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]

theorem frame_pairing_sq {n m : ℕ} (U : Matrix (Fin n) (Fin m) ℝ) (a : Vec n) (t : ℝ)
    (y : Vec n) :
    sqNorm ((frame U a t)ᵀ *ᵥ y) = sqNorm (Uᵀ *ᵥ y) + t ^ 2 * (dot a y) ^ 2 := by
  rw [frame_transpose_mulVec, sqNorm_snoc, mul_pow]

/-- The pairing of the frame with the normal column last equals that of the library's
`cutoffFrame` (normal column first). -/
theorem frame_pairing_eq_cutoffFrame {n m : ℕ} (U : Matrix (Fin n) (Fin m) ℝ) (a : Vec n)
    (t : ℝ) (y : Vec n) :
    sqNorm ((frame U a t)ᵀ *ᵥ y) = sqNorm ((cutoffFrame U a t)ᵀ.mulVec y) := by
  rw [frame_pairing_sq, cutoffFrame_pairing]

/-- Item `C/11_U/disp/014` (`companion/chapters/11_U.tex:246-249`): "At differentiable points,"
\[ \|V(x)^T\nabla F(x)\|^2=\|A(x)\|^2+\tau(r(x))^2|a^T\nabla F(x)|^2. \]
In the common setting, with $U$ and the cutoff $\tau$, for $x\in\Omega$ where $F$ is
differentiable with gradient $g$. Library: `cutoffFrame_pairing_eq_visibility`. -/
theorem frame_pairing {n : ℕ} (F : Vec n → ℝ) (hF : ConvexOn ℝ univ F)
    (R : AdmissibleBFGSRun n F)
    (c : ℝ) (K : Set (Vec n)) (_hK_def : K = {x | F x ≤ c}) (_hK : IsCompact K)
    (_hrun : ∀ k, R.x k ∈ K)
    (Ω : Set (Vec n)) (_hΩ : IsOpen Ω) (_hΩc : Convex ℝ Ω) (_hKΩ : K ⊆ Ω)
    (μ : ℝ) (_hμ : 0 < μ) (_hstrong : EuclideanStrongConvexOn Ω μ F)
    (a : Vec n) (_ha : sqNorm a = 1) (b : ℝ) (A : Vec n → Vec n)
    (hA : ∀ x ∈ Ω, ∀ g ∈ ConvexSubdifferential.subdifferential F x,
      tangentProjection a g = A x)
    (L : ℝ≥0) (_hLip : LipschitzOnWith L A Ω) (E : Set ℝ) (_hE : IsClosed E)
    (_hsmooth : CenteredSmoothSublinear.LocallyC11On (Ω \ {x | dot a x - b ∈ E}) F)
    {m : ℕ} (U : Matrix (Fin n) (Fin m) ℝ) (hU : Uᵀ * U = 1)
    (hUS : ∀ v, (U * Uᵀ) *ᵥ v = tangentProjection a v)
    (δ : ℝ) (_hδ : 0 < δ) (τ : ℝ → ℝ) (Lτ : ℝ≥0) (_hτ : LipschitzWith Lτ τ)
    (_hτ01 : ∀ t, 0 ≤ τ t ∧ τ t ≤ 1)
    (_hτ0 : ∀ t e, e ∈ E → |t - e| ≤ δ / 4 → τ t = 0)
    (_hτ1 : ∀ t, (∀ e ∈ E, δ / 2 ≤ |t - e|) → τ t = 1)
    (x g : Vec n) (hxΩ : x ∈ Ω) (hg : HasFDerivAt F (gradientFunctional g) x) :
    sqNorm ((frame U a (τ (dot a x - b)))ᵀ *ᵥ g) =
      sqNorm (A x) + τ (dot a x - b) ^ 2 * |dot a g| ^ 2 := by
  rw [frame_pairing_sq, tangent_matrix_sqNorm a U hU hUS,
    hA x hxΩ g (convex_supporting_inequality hF hg), sq_abs]

/-- The coordinate gradient is the gradient at a point of differentiability. -/
theorem coordinateGradient_eq {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F) {x g : Vec n}
    (hg : HasFDerivAt F (gradientFunctional g) x) : coordinateGradient F x = g :=
  supporting_vector_eq_gradient
    (convex_supporting_inequality hF (hasFDerivAt_coordinateGradient hg.differentiableAt)) hg

/-- Item `C/11_U/disp/015` (`companion/chapters/11_U.tex:277-279`): "Convex cocoercivity on each
sufficiently small convex chart yields"
\[ \|\nabla F(z)-\nabla F(x)\|^2\le L_\delta\,y^Ts, \]
with $y=\nabla F(z)-\nabla F(x)$, $s=z-x$, for endpoints $x,z\in K$ with $\tau(r(z))\neq0$ that
are sufficiently close ($\|z-x\|<\rho$). In the common setting with the cutoff $\tau$; $L_\delta$
depends on $\delta$. Library: `exists_cutoff_strip_cocoercivity`. -/
theorem strip_cocoercivity {n : ℕ} (F : Vec n → ℝ) (hF : ConvexOn ℝ univ F)
    (R : AdmissibleBFGSRun n F)
    (c : ℝ) (K : Set (Vec n)) (_hK_def : K = {x | F x ≤ c}) (hK : IsCompact K)
    (_hrun : ∀ k, R.x k ∈ K)
    (Ω : Set (Vec n)) (hΩ : IsOpen Ω) (_hΩc : Convex ℝ Ω) (hKΩ : K ⊆ Ω)
    (μ : ℝ) (_hμ : 0 < μ) (_hstrong : EuclideanStrongConvexOn Ω μ F)
    (a : Vec n) (_ha : sqNorm a = 1) (b : ℝ) (A : Vec n → Vec n)
    (_hA : ∀ x ∈ Ω, ∀ g ∈ ConvexSubdifferential.subdifferential F x,
      tangentProjection a g = A x)
    (L : ℝ≥0) (_hLip : LipschitzOnWith L A Ω) (E : Set ℝ) (hE : IsClosed E)
    (hsmooth : CenteredSmoothSublinear.LocallyC11On (Ω \ {x | dot a x - b ∈ E}) F)
    {m : ℕ} (U : Matrix (Fin n) (Fin m) ℝ) (_hU : Uᵀ * U = 1)
    (_hUS : ∀ v, (U * Uᵀ) *ᵥ v = tangentProjection a v)
    (δ : ℝ) (hδ : 0 < δ) (τ : ℝ → ℝ) (Lτ : ℝ≥0) (_hτ : LipschitzWith Lτ τ)
    (_hτ01 : ∀ t, 0 ≤ τ t ∧ τ t ≤ 1)
    (hτ0 : ∀ t e, e ∈ E → |t - e| ≤ δ / 4 → τ t = 0)
    (_hτ1 : ∀ t, (∀ e ∈ E, δ / 2 ≤ |t - e|) → τ t = 1) :
    ∃ Lδ : ℝ, 0 < Lδ ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ K, ∀ z ∈ K, τ (dot a z - b) ≠ 0 → ‖z - x‖ < ρ →
      ∀ g h : Vec n, HasFDerivAt F (gradientFunctional g) x →
        HasFDerivAt F (gradientFunctional h) z → sqNorm (h - g) ≤ Lδ * dot (h - g) (z - x) := by
  rw [← regularRegion_eq] at hsmooth
  obtain ⟨C, hC, ρ, hρ, hb⟩ := exists_cutoff_strip_cocoercivity hF hΩ hK hKΩ a b hE hsmooth
    (by positivity : 0 < δ / 4) hτ0
  refine ⟨C, hC, ρ, hρ, fun x hx z hz hτz hxz g h hg hh => ?_⟩
  have hb' := hb x hx z hz hτz hxz
  rwa [coordinateGradient_eq hF hg, coordinateGradient_eq hF hh] at hb'

/-- Item `C/11_U/disp/016`, equation (11.13) (`companion/chapters/11_U.tex:279-281`):
"Therefore $\|V(z)^Ty\|^2\le C_0t$ for every sufficiently late accepted pair": there is
$C_0\ge0$ with $\|V(x_{k+1})^Ty_k\|^2\le C_0t_k$ for all large $k$. In the common setting with
$U$ and the cutoff $\tau$. Library: `AdmissibleBFGSRun.eventually_fixed_normal_frame_secant`. -/
theorem frame_secant {n : ℕ} (F : Vec n → ℝ) (_hF : ConvexOn ℝ univ F)
    (R : AdmissibleBFGSRun n F)
    (c : ℝ) (K : Set (Vec n)) (hK_def : K = {x | F x ≤ c}) (hK : IsCompact K)
    (hrun : ∀ k, R.x k ∈ K)
    (Ω : Set (Vec n)) (hΩ : IsOpen Ω) (_hΩc : Convex ℝ Ω) (hKΩ : K ⊆ Ω)
    (μ : ℝ) (hμ : 0 < μ) (hstrong : EuclideanStrongConvexOn Ω μ F)
    (a : Vec n) (ha : sqNorm a = 1) (b : ℝ) (A : Vec n → Vec n)
    (hA : ∀ x ∈ Ω, ∀ g ∈ ConvexSubdifferential.subdifferential F x,
      tangentProjection a g = A x)
    (L : ℝ≥0) (hLip : LipschitzOnWith L A Ω) (E : Set ℝ) (hE : IsClosed E)
    (hsmooth : CenteredSmoothSublinear.LocallyC11On (Ω \ {x | dot a x - b ∈ E}) F)
    {m : ℕ} (U : Matrix (Fin n) (Fin m) ℝ) (hU : Uᵀ * U = 1)
    (hUS : ∀ v, (U * Uᵀ) *ᵥ v = tangentProjection a v)
    (δ : ℝ) (hδ : 0 < δ) (τ : ℝ → ℝ) (Lτ : ℝ≥0) (_hτ : LipschitzWith Lτ τ)
    (hτ01 : ∀ t, 0 ≤ τ t ∧ τ t ≤ 1)
    (hτ0 : ∀ t e, e ∈ E → |t - e| ≤ δ / 4 → τ t = 0)
    (_hτ1 : ∀ t, (∀ e ∈ E, δ / 2 ≤ |t - e|) → τ t = 1) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ᶠ k in atTop,
      sqNorm ((frame U a (τ (dot a (R.x (k + 1)) - b)))ᵀ *ᵥ R.gradientChange k) ≤
        C₀ * R.curvature k := by
  obtain ⟨hsub, hKR⟩ := initialSublevel_sub R c K hK_def hK hrun
  rw [← regularRegion_eq] at hsmooth
  obtain ⟨C, hC, hev⟩ := R.eventually_fixed_normal_frame_secant hΩ hKR (hsub.trans hKΩ) hμ
    hstrong ha b (fun x hx g hg => hA x hx g hg) hLip hE hsmooth hτ01
    (by positivity : 0 < δ / 4) hτ0 U hU hUS
  refine ⟨C, hC, ?_⟩
  filter_upwards [hev] with k hk
  rw [frame_pairing_eq_cutoffFrame]
  exact hk

/-- The coefficient $\beta$ of display (11.14): for an endpoint pair $x,z$ with $s=z-x$,
$\beta=[\tau(r(z))-\tau(r(x))]/(a^Ts)$ if $a^Ts\neq0$ and $\beta=0$ if $a^Ts=0$
($r(x)=a^Tx-b$). -/
def cutoffBeta {n : ℕ} (τ : ℝ → ℝ) (a : Vec n) (b : ℝ) (x z : Vec n) : ℝ :=
  if dot a (z - x) ≠ 0 then (τ (dot a z - b) - τ (dot a x - b)) / dot a (z - x) else 0

theorem dot_sub_eq {n : ℕ} (a x z : Vec n) (b : ℝ) :
    dot a (z - x) = (dot a z - b) - (dot a x - b) := by
  change a ⬝ᵥ (z - x) = (a ⬝ᵥ z - b) - (a ⬝ᵥ x - b)
  rw [dotProduct_sub]
  ring

theorem cutoffBeta_eq_cutoffSlope {n : ℕ} (τ : ℝ → ℝ) (a : Vec n) (b : ℝ) (x z : Vec n) :
    cutoffBeta τ a b x z = cutoffSlope τ (dot a x - b) (dot a z - b) := by
  unfold cutoffBeta cutoffSlope
  rw [dot_sub_eq a x z b]
  by_cases h : (dot a z - b) - (dot a x - b) = 0
  · rw [if_neg (not_not.mpr h), if_pos (sub_eq_zero.mp h)]
  · rw [if_pos h, if_neg (fun he => h (sub_eq_zero.mpr he))]

theorem cutoffBeta_mul {n : ℕ} (τ : ℝ → ℝ) (a : Vec n) (b : ℝ) (x z : Vec n) :
    cutoffBeta τ a b x z * dot a (z - x) = τ (dot a z - b) - τ (dot a x - b) := by
  rw [cutoffBeta_eq_cutoffSlope, dot_sub_eq a x z b, cutoffSlope_mul]

/-- Item `C/11_U/disp/017` (`companion/chapters/11_U.tex:292-297`): "For an endpoint pair put
$\beta=[\tau(r(z))-\tau(r(x))]/(a^Ts)$ if $a^Ts\ne0$, $\beta=0$ if $a^Ts=0$. Then
$|\beta|\le\operatorname{Lip}(\tau)$." In the common setting with the cutoff $\tau$, for every
pair $x,z$, $s=z-x$, and every Lipschitz constant `Lτ` of $\tau$. Library: `abs_cutoffSlope_le`. -/
theorem beta_bound {n : ℕ} (F : Vec n → ℝ) (_hF : ConvexOn ℝ univ F)
    (R : AdmissibleBFGSRun n F)
    (c : ℝ) (K : Set (Vec n)) (_hK_def : K = {x | F x ≤ c}) (_hK : IsCompact K)
    (_hrun : ∀ k, R.x k ∈ K)
    (Ω : Set (Vec n)) (_hΩ : IsOpen Ω) (_hΩc : Convex ℝ Ω) (_hKΩ : K ⊆ Ω)
    (μ : ℝ) (_hμ : 0 < μ) (_hstrong : EuclideanStrongConvexOn Ω μ F)
    (a : Vec n) (_ha : sqNorm a = 1) (b : ℝ) (A : Vec n → Vec n)
    (_hA : ∀ x ∈ Ω, ∀ g ∈ ConvexSubdifferential.subdifferential F x,
      tangentProjection a g = A x)
    (L : ℝ≥0) (_hLip : LipschitzOnWith L A Ω) (E : Set ℝ) (_hE : IsClosed E)
    (_hsmooth : CenteredSmoothSublinear.LocallyC11On (Ω \ {x | dot a x - b ∈ E}) F)
    {m : ℕ} (U : Matrix (Fin n) (Fin m) ℝ) (_hU : Uᵀ * U = 1)
    (_hUS : ∀ v, (U * Uᵀ) *ᵥ v = tangentProjection a v)
    (δ : ℝ) (_hδ : 0 < δ) (τ : ℝ → ℝ) (Lτ : ℝ≥0) (hτ : LipschitzWith Lτ τ)
    (_hτ01 : ∀ t, 0 ≤ τ t ∧ τ t ≤ 1)
    (_hτ0 : ∀ t e, e ∈ E → |t - e| ≤ δ / 4 → τ t = 0)
    (_hτ1 : ∀ t, (∀ e ∈ E, δ / 2 ≤ |t - e|) → τ t = 1)
    (x z s : Vec n) (hs : s = z - x) (β : ℝ)
    (hβ : β = if dot a s ≠ 0 then (τ (dot a z - b) - τ (dot a x - b)) / dot a s else 0) :
    |β| ≤ Lτ := by
  have hβ' : β = cutoffBeta τ a b x z := by rw [hβ, hs]; rfl
  rw [hβ', cutoffBeta_eq_cutoffSlope]
  exact abs_cutoffSlope_le hτ _ _

/-- The algebraic identity behind (11.14), for every pair $x,z$. -/
theorem frame_transport_identity {n m : ℕ} (U : Matrix (Fin n) (Fin m) ℝ) (a : Vec n) (b : ℝ)
    (τ : ℝ → ℝ) (x z : Vec n) :
    frame U a (τ (dot a z - b)) =
      frame U a (τ (dot a x - b)) + cutoffBeta τ a b x z • vecMulVec (z - x) (lastBasis m) -
        cutoffBeta τ a b x z • vecMulVec (tangentProjection a (z - x)) (lastBasis m) := by
  have hβ := cutoffBeta_mul τ a b x z
  ext i j
  refine Fin.lastCases ?_ (fun j' => ?_) j
  · simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, frame_last, vecMulVec,
      Matrix.of_apply, lastBasis, Pi.single_eq_same, mul_one, smul_eq_mul, tangentProjection,
      Pi.sub_apply, Pi.smul_apply]
    linear_combination (a i) * hβ.symm
  · simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, frame_castSucc, vecMulVec,
      Matrix.of_apply, lastBasis, smul_eq_mul]
    rw [Pi.single_eq_of_ne (Fin.castSucc_lt_last j').ne]
    ring

/-- Item `C/11_U/disp/018`, equation (11.14) (`companion/chapters/11_U.tex:298-302`): "With
$e_n$ the last frame-coordinate vector,"
\[ V(z)=V(x)+s\,\beta e_n^T-\beta P_Ss\,e_n^T \]
for an endpoint pair $x,z$, $s=z-x$, $\beta$ of display `disp/017` (`cutoffBeta`), $V$ the frame (11.12),
$e_n$ = `lastBasis m`, $ue_n^T$ = `vecMulVec u (lastBasis m)`. In the common setting with $U$ and
the cutoff $\tau$. Library (normal column first): `cutoffFrame_transport`. -/
theorem frame_transport {n : ℕ} (F : Vec n → ℝ) (_hF : ConvexOn ℝ univ F)
    (R : AdmissibleBFGSRun n F)
    (c : ℝ) (K : Set (Vec n)) (_hK_def : K = {x | F x ≤ c}) (_hK : IsCompact K)
    (_hrun : ∀ k, R.x k ∈ K)
    (Ω : Set (Vec n)) (_hΩ : IsOpen Ω) (_hΩc : Convex ℝ Ω) (_hKΩ : K ⊆ Ω)
    (μ : ℝ) (_hμ : 0 < μ) (_hstrong : EuclideanStrongConvexOn Ω μ F)
    (a : Vec n) (_ha : sqNorm a = 1) (b : ℝ) (A : Vec n → Vec n)
    (_hA : ∀ x ∈ Ω, ∀ g ∈ ConvexSubdifferential.subdifferential F x,
      tangentProjection a g = A x)
    (L : ℝ≥0) (_hLip : LipschitzOnWith L A Ω) (E : Set ℝ) (_hE : IsClosed E)
    (_hsmooth : CenteredSmoothSublinear.LocallyC11On (Ω \ {x | dot a x - b ∈ E}) F)
    {m : ℕ} (U : Matrix (Fin n) (Fin m) ℝ) (_hU : Uᵀ * U = 1)
    (_hUS : ∀ v, (U * Uᵀ) *ᵥ v = tangentProjection a v)
    (δ : ℝ) (_hδ : 0 < δ) (τ : ℝ → ℝ) (Lτ : ℝ≥0) (_hτ : LipschitzWith Lτ τ)
    (_hτ01 : ∀ t, 0 ≤ τ t ∧ τ t ≤ 1)
    (_hτ0 : ∀ t e, e ∈ E → |t - e| ≤ δ / 4 → τ t = 0)
    (_hτ1 : ∀ t, (∀ e ∈ E, δ / 2 ≤ |t - e|) → τ t = 1)
    (V : Vec n → Matrix (Fin n) (Fin (m + 1)) ℝ) (hV : ∀ x, V x = frame U a (τ (dot a x - b)))
    (x z s : Vec n) (hs : s = z - x) (β : ℝ) (hβ : β = cutoffBeta τ a b x z) :
    V z = V x + β • vecMulVec s (lastBasis m) - β • vecMulVec (tangentProjection a s) (lastBasis m) := by
  rw [hV, hV, hs, hβ]
  exact frame_transport_identity U a b τ x z

/-- Item `C/11_U/disp/019`, equation (11.15) (`companion/chapters/11_U.tex:302-307`): for every
accepted pair ($x=x_k$, $z=x_{k+1}$, $s=s_k$, $d=d_k$, $\beta=\beta_k$),
\[ R=-\beta P_Ss\,e_n^T\in S,\qquad
   \|R\|_F^2\le\operatorname{Lip}(\tau)^2\|P_Ss\|^2\le\frac{2\operatorname{Lip}(\tau)^2}{\mu}d. \]
"$R\in S$": every column of $R$ lies in $S=a^\perp$; $\|R\|_F^2=\sum_{i,j}R_{ij}^2$. In the
common setting with $U$ and the cutoff $\tau$ (Lipschitz constant `Lτ`). The transport form
"(11.14) is the transport hypothesis of Theorem~\ref{M:residualtheorem}, with $T=I$" is
`transport_hypothesis` (item `prose/027`). Library:
`cutoffResidual_frobSq`, `AdmissibleBFGSRun.fixed_normal_cutoff_residual_budget`. -/
theorem residual_bounds {n : ℕ} (F : Vec n → ℝ) (_hF : ConvexOn ℝ univ F)
    (R : AdmissibleBFGSRun n F)
    (c : ℝ) (K : Set (Vec n)) (_hK_def : K = {x | F x ≤ c}) (_hK : IsCompact K)
    (hrun : ∀ k, R.x k ∈ K)
    (Ω : Set (Vec n)) (_hΩ : IsOpen Ω) (_hΩc : Convex ℝ Ω) (hKΩ : K ⊆ Ω)
    (μ : ℝ) (hμ : 0 < μ) (hstrong : EuclideanStrongConvexOn Ω μ F)
    (a : Vec n) (ha : sqNorm a = 1) (b : ℝ) (A : Vec n → Vec n)
    (_hA : ∀ x ∈ Ω, ∀ g ∈ ConvexSubdifferential.subdifferential F x,
      tangentProjection a g = A x)
    (L : ℝ≥0) (_hLip : LipschitzOnWith L A Ω) (E : Set ℝ) (_hE : IsClosed E)
    (_hsmooth : CenteredSmoothSublinear.LocallyC11On (Ω \ {x | dot a x - b ∈ E}) F)
    {m : ℕ} (U : Matrix (Fin n) (Fin m) ℝ) (_hU : Uᵀ * U = 1)
    (_hUS : ∀ v, (U * Uᵀ) *ᵥ v = tangentProjection a v)
    (δ : ℝ) (_hδ : 0 < δ) (τ : ℝ → ℝ) (Lτ : ℝ≥0) (hτ : LipschitzWith Lτ τ)
    (_hτ01 : ∀ t, 0 ≤ τ t ∧ τ t ≤ 1)
    (_hτ0 : ∀ t e, e ∈ E → |t - e| ≤ δ / 4 → τ t = 0)
    (_hτ1 : ∀ t, (∀ e ∈ E, δ / 2 ≤ |t - e|) → τ t = 1)
    (k : ℕ) (β : ℝ) (hβ : β = cutoffBeta τ a b (R.x k) (R.x (k + 1)))
    (Rk : Matrix (Fin n) (Fin (m + 1)) ℝ)
    (hRk : Rk = -β • vecMulVec (tangentProjection a (R.displacement k)) (lastBasis m)) :
    (∀ j, dot a (fun i => Rk i j) = 0) ∧
      ∑ i, ∑ j, (Rk i j) ^ 2 ≤ (Lτ : ℝ) ^ 2 * sqNorm (tangentProjection a (R.displacement k)) ∧
      (Lτ : ℝ) ^ 2 * sqNorm (tangentProjection a (R.displacement k)) ≤
        2 * (Lτ : ℝ) ^ 2 / μ * R.d k := by
  have hx := run_mem R hrun hKΩ
  set p := tangentProjection a (R.displacement k) with hp
  have hcol (j : Fin (m + 1)) : (fun i => Rk i j) = (-β * lastBasis m j) • p := by
    ext i
    rw [hRk]
    simp only [Matrix.smul_apply, vecMulVec, Matrix.of_apply, smul_eq_mul, Pi.smul_apply]
    ring
  have hfrob : ∑ i, ∑ j, (Rk i j) ^ 2 = β ^ 2 * sqNorm p := by
    rw [hRk]
    simp only [Matrix.smul_apply, vecMulVec, Matrix.of_apply, smul_eq_mul, lastBasis]
    rw [sqNorm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single (Fin.last m)]
    · simp only [Pi.single_eq_same, mul_one]
      ring
    · intro j _ hj
      rw [Pi.single_eq_of_ne hj]
      ring
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hβL : β ^ 2 ≤ (Lτ : ℝ) ^ 2 := by
    have h := abs_cutoffSlope_le hτ (dot a (R.x k) - b) (dot a (R.x (k + 1)) - b)
    rw [← cutoffBeta_eq_cutoffSlope, ← hβ] at h
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) Lτ.coe_nonneg).mpr h
  have hd := R.strong_displacement_sq_le hμ hstrong hx k
  have hpd : sqNorm p ≤ sqNorm (R.displacement k) := sqNorm_tangentProjection_le ha _
  refine ⟨fun j => ?_, ?_, ?_⟩
  · rw [hcol j, dot_smul_right, hp, tangentProjection_normal_zero ha, mul_zero]
  · rw [hfrob]
    exact mul_le_mul_of_nonneg_right hβL (sqNorm_nonneg _)
  · calc (Lτ : ℝ) ^ 2 * sqNorm p ≤ (Lτ : ℝ) ^ 2 * ((2 / μ) * R.d k) :=
          mul_le_mul_of_nonneg_left (hpd.trans hd) (sq_nonneg _)
      _ = 2 * (Lτ : ℝ) ^ 2 / μ * R.d k := by ring

/-- Item `C/11_U/prose/027` (`companion/chapters/11_U.tex:302`), corrected on 15 October 2026 (M18;
before "Thus (6) holds with $T=I$ and", where (6) was no equation of the companion): "Thus (11.14)
is the transport hypothesis of Theorem~\ref{M:residualtheorem}, with $T=I$, rank-one term
$s(\beta e_n)^T$ and $R=\dots$". Along accepted pairs, (11.14) is the transport hypothesis of
Theorem~\ref{M:residualtheorem} (Chapter 2; there $V_{k+1}=V_kT_k+s_kb_k^T+R_k$) for the frames
$V_k=V(x_k)$ of (11.12), with $T_k=I$, rank-one term $s_k(\beta_ke_n)^T$ and
$R_k=-\beta_kP_Ss_k\,e_n^T$; the columns of $R_k$ lie in $S$ and
$\|R_k\|_F^2\le\frac{2\operatorname{Lip}(\tau)^2}{\mu}d_k$ (display (11.15)). In the common
setting with $U$ and the cutoff $\tau$. -/
theorem transport_hypothesis {n : ℕ} (F : Vec n → ℝ) (hF : ConvexOn ℝ univ F)
    (R : AdmissibleBFGSRun n F)
    (c : ℝ) (K : Set (Vec n)) (hK_def : K = {x | F x ≤ c}) (hK : IsCompact K)
    (hrun : ∀ k, R.x k ∈ K)
    (Ω : Set (Vec n)) (hΩ : IsOpen Ω) (hΩc : Convex ℝ Ω) (hKΩ : K ⊆ Ω)
    (μ : ℝ) (hμ : 0 < μ) (hstrong : EuclideanStrongConvexOn Ω μ F)
    (a : Vec n) (ha : sqNorm a = 1) (b : ℝ) (A : Vec n → Vec n)
    (hA : ∀ x ∈ Ω, ∀ g ∈ ConvexSubdifferential.subdifferential F x,
      tangentProjection a g = A x)
    (L : ℝ≥0) (hLip : LipschitzOnWith L A Ω) (E : Set ℝ) (hE : IsClosed E)
    (hsmooth : CenteredSmoothSublinear.LocallyC11On (Ω \ {x | dot a x - b ∈ E}) F)
    {m : ℕ} (U : Matrix (Fin n) (Fin m) ℝ) (hU : Uᵀ * U = 1)
    (hUS : ∀ v, (U * Uᵀ) *ᵥ v = tangentProjection a v)
    (δ : ℝ) (hδ : 0 < δ) (τ : ℝ → ℝ) (Lτ : ℝ≥0) (hτ : LipschitzWith Lτ τ)
    (hτ01 : ∀ t, 0 ≤ τ t ∧ τ t ≤ 1)
    (hτ0 : ∀ t e, e ∈ E → |t - e| ≤ δ / 4 → τ t = 0)
    (hτ1 : ∀ t, (∀ e ∈ E, δ / 2 ≤ |t - e|) → τ t = 1)
    (V : ℕ → Matrix (Fin n) (Fin (m + 1)) ℝ) (hV : ∀ k, V k = frame U a (τ (dot a (R.x k) - b)))
    (β : ℕ → ℝ) (hβ : ∀ k, β k = cutoffBeta τ a b (R.x k) (R.x (k + 1)))
    (Rk : ℕ → Matrix (Fin n) (Fin (m + 1)) ℝ)
    (hRk : ∀ k, Rk k = -β k • vecMulVec (tangentProjection a (R.displacement k)) (lastBasis m))
    (k : ℕ) :
    V (k + 1) = V k * (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) +
        vecMulVec (R.displacement k) (β k • lastBasis m) + Rk k ∧
      (∀ j, dot a (fun i => Rk k i j) = 0) ∧
      ∑ i, ∑ j, (Rk k i j) ^ 2 ≤ 2 * (Lτ : ℝ) ^ 2 / μ * R.d k := by
  have hres := residual_bounds F hF R c K hK_def hK hrun Ω hΩ hΩc hKΩ μ hμ hstrong a ha b A hA
    L hLip E hE hsmooth U hU hUS δ hδ τ Lτ hτ hτ01 hτ0 hτ1 k (β k) (hβ k) (Rk k) (hRk k)
  refine ⟨?_, hres.1, hres.2.1.trans hres.2.2⟩
  have he : R.x (k + 1) - R.x k = R.displacement k := by
    rw [R.step]
    simp [AdmissibleBFGSRun.displacement]
  have ht := frame_transport_identity U a b τ (R.x k) (R.x (k + 1))
  rw [he] at ht
  rw [hV, hV, Matrix.mul_one, ht, hRk, hβ]
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, vecMulVec, Matrix.of_apply,
    smul_eq_mul, Pi.smul_apply, neg_mul]
  ring

/-! ### The conditions (RS) and (IR) of Chapter 4

Forms of (4.RS) and (4.IR) with real constants (`companion/chapters/04_R.tex:53-80`), as used in
Section 11.7; since 15 October 2026 (wording point W19) the chapter prints $C_\eta\ge0$ and
$M_\eta\ge0$, which is equivalent (`Ch04R.RSNonneg_iff`, `Ch04R.IRNonneg_iff`). The companion
coverage modules cannot import each other, so the conditions are restated here. -/

/-- The radial secant condition (RS) of Chapter 4 on a set $K$, with optimizer $x_*$: for every
$\eta>0$ some $C_\eta$ gives $N(x,z)^2\le C_\eta T(x,z)$ for differentiable $x,z\in K$ with
$F_*+\eta\le F(z)\le F(x)$ and $T>0$, where $T=(h-g)^T(z-x)$ and $N=(h-g)^T(z-x_*)$. -/
def RS {n : ℕ} (F : Vec n → ℝ) (xstar : Vec n) (K : Set (Vec n)) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ C : ℝ,
    ∀ x z g h : Vec n, x ∈ K → z ∈ K →
      HasFDerivAt F (gradientFunctional g) x → HasFDerivAt F (gradientFunctional h) z →
      F xstar + η ≤ F z → F z ≤ F x → 0 < dot (h - g) (z - x) →
      (dot (h - g) (z - xstar)) ^ 2 ≤ C * dot (h - g) (z - x)

/-- Inward radial smoothness (IR) of Chapter 4: for every $\eta>0$ there are $M_\eta$ and
$\theta_\eta\in(0,1/2]$ with
$0\le F(x-tr_x)-F(x)+t\nabla F(x)^Tr_x\le\frac{M_\eta}2t^2$, $0\le t\le\theta_\eta$, at every
differentiable $x\in K$ with $F(x)\ge F_*+\eta$ ($r_x=x-x_*$). -/
def IR {n : ℕ} (F : Vec n → ℝ) (xstar : Vec n) (K : Set (Vec n)) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ M θ : ℝ, 0 < θ ∧ θ ≤ 1 / 2 ∧
    ∀ x g : Vec n, x ∈ K → HasFDerivAt F (gradientFunctional g) x → F xstar + η ≤ F x →
      ∀ t : ℝ, 0 ≤ t → t ≤ θ →
        0 ≤ F (x - t • (x - xstar)) - F x + t * dot g (x - xstar) ∧
          F (x - t • (x - xstar)) - F x + t * dot g (x - xstar) ≤ M / 2 * t ^ 2

theorem RS_iff_library {n : ℕ} (F : Vec n → ℝ) (xstar : Vec n) (K : Set (Vec n)) :
    RS F xstar K ↔ RadialCertificate.HasRadialSecantBounds F K xstar := by
  constructor
  · intro h η hη
    obtain ⟨C, hC⟩ := h η hη
    exact ⟨C, fun x z g h hx hz hb ho hg hh ht => hC x z g h hx hz hg hh hb ho ht⟩
  · intro h η hη
    obtain ⟨C, hC⟩ := h η hη
    exact ⟨C, fun x z g h hx hz hg hh hb ho ht => hC x z g h hx hz hb ho hg hh ht⟩

/-! ### Section 11.7: the spike $r$ -/

open NormalSpike in
/-- Item `C/11_U/disp/023` (`companion/chapters/11_U.tex:373-375`): "Let $a_j=2^{-j}$ for
$j\ge2$, and let $\eta(t)=(1-t^2)^2$ for $|t|\le1$, $\eta(t)=0$ for $|t|>1$." The library's
`scale N` is $a_{N+2}$ and `bump` is $\eta$. -/
theorem spike_scale_bump :
    (∀ j : ℕ, 2 ≤ j → scale (j - 2) = (2 : ℝ) ^ (-(j : ℤ))) ∧
      ∀ t : ℝ, bump t = if |t| ≤ 1 then (1 - t ^ 2) ^ 2 else 0 := by
  refine ⟨fun j hj => ?_, bump_eq_source⟩
  rw [scale_eq_source]
  congr 3
  omega

open NormalSpike in
theorem bump_support_subset : Function.support bump ⊆ Ioc (-1) 1 := by
  intro t ht
  rw [Function.mem_support] at ht
  by_contra h
  simp only [mem_Ioc, not_and_or, not_lt, not_le] at h
  apply ht
  rcases h with h | h
  · simp [bump, h]
  · simp [bump, not_le.mpr (by linarith : (-1 : ℝ) < t), not_le.mpr h]

open NormalSpike in
theorem bump_support_eq (a : ℝ) (ha : 0 < a) :
    Function.support (fun v => bump ((v - a) / a ^ 5)) = Function.support (scaledDensity a) := by
  ext v
  simp only [Function.mem_support, scaledDensity]
  constructor
  · intro h
    exact mul_ne_zero (inv_ne_zero (pow_ne_zero 3 ha.ne')) h
  · intro h
    exact right_ne_zero_of_mul h

open NormalSpike in
/-- Item `C/11_U/prose/034` (`companion/chapters/11_U.tex:375-376`): "This nonnegative bump is
$C^1$, has $\eta(0)=1$, and integral $16/15$. Its supports at the following scales are pairwise
disjoint": the supports of $v\mapsto\eta((v-a_j)/a_j^5)$, $j\ge2$, are pairwise disjoint.
Library: `bump_nonneg`, `bump_contDiff`, `bump_total_mass`, `bump_supports_pairwise_disjoint`. -/
theorem bump_properties :
    (∀ t, 0 ≤ bump t) ∧ ContDiff ℝ 1 bump ∧ bump 0 = 1 ∧ (∫ t, bump t) = 16 / 15 ∧
      Pairwise (fun j N : ℕ => Disjoint (Function.support (fun v => bump ((v - scale j) / scale j ^ 5)))
        (Function.support (fun v => bump ((v - scale N) / scale N ^ 5)))) := by
  refine ⟨bump_nonneg, bump_contDiff, by norm_num [bump], ?_, ?_⟩
  · rw [← intervalIntegral.integral_eq_integral_of_support_subset bump_support_subset]
    exact bump_total_mass
  · intro j N hjN
    rw [bump_support_eq _ (scale_pos j), bump_support_eq _ (scale_pos N)]
    exact bump_supports_pairwise_disjoint hjN

open NormalSpike in
/-- Item `C/11_U/disp/024` (`companion/chapters/11_U.tex:377-380`): the density
\[ k(v)=\sum_{j=2}^\infty a_j^{-3}\eta\Bigl(\frac{v-a_j}{a_j^5}\Bigr),\qquad v>0, \]
is the library's `density` (indexed by $j+2$), for $a_j=2^{-j}$ and $\eta$ of display `disp/023`. -/
theorem spike_density_def (a : ℕ → ℝ) (ha : ∀ j, a j = (2 : ℝ) ^ (-(j : ℤ))) (η : ℝ → ℝ)
    (hη : ∀ t, η t = if |t| ≤ 1 then (1 - t ^ 2) ^ 2 else 0) (v : ℝ) (_hv : 0 < v) :
    density v = ∑' j : ℕ, (a (j + 2))⁻¹ ^ 3 * η ((v - a (j + 2)) / a (j + 2) ^ 5) := by
  have hs (j : ℕ) : a (j + 2) = scale j := by rw [ha, scale_eq_source]
  unfold density
  apply tsum_congr
  intro j
  rw [hs, hη, ← bump_eq_source, scaledDensity, inv_pow]

open NormalSpike in
/-- Item `C/11_U/disp/025`, equation (11.18) (`companion/chapters/11_U.tex:380-385`):
\[ r(v)=\int_0^v(v-t)k(t)\,dt\ (v>0),\qquad r(v)=0\ (v\le0). \]
This is literally the library's `sourcePrimitive` (with $k$ = `density`, display `disp/024`). -/
theorem spike_def (v : ℝ) :
    sourcePrimitive v = if 0 < v then ∫ t in (0 : ℝ)..v, (v - t) * density t else 0 := rfl

open NormalSpike in
/-- Item `C/11_U/prose/035` (`companion/chapters/11_U.tex:385`): "Each bump has mass
$(16/15)a_j^2$. The total mass is finite." ($\int a_j^{-3}\eta((v-a_j)/a_j^5)\,dv=
\frac{16}{15}a_j^2$, and $\int k=\frac4{45}<\infty$, $k$ integrable.) Library:
`scaledDensity_total_mass`, `density_total_mass`, `density_integrable`. -/
theorem bump_masses :
    (∀ N : ℕ, (∫ v, scaledDensity (scale N) v) = (16 / 15) * scale N ^ 2) ∧
      MeasureTheory.Integrable density ∧ (∫ v, density v) = 4 / 45 :=
  ⟨fun N => scaledDensity_total_mass _ (scale_pos N) (scale_le_one N), density_integrable,
    density_total_mass⟩

open NormalSpike in
/-- Item `C/11_U/prose/036` (`companion/chapters/11_U.tex:385-388`): "The sum is locally finite
away from zero, so $r$ is convex, $C^1$ globally, and $C^3$ on $(0,\infty)$ and $(-\infty,0)$. In
particular it is locally $C^{1,1}$ away from zero." Locally finite: near every $v\neq0$ all
bumps from some index on vanish. Library: `exists_tail_below_neighborhood`,
`sourcePrimitive_convex`, `sourcePrimitive_contDiff`, `sourcePrimitive_contDiffOn_off_zero`,
`sourcePrimitive_locallyC11_off_zero`. -/
theorem spike_regularity :
    (∀ v : ℝ, v ≠ 0 → ∃ N : ℕ, ∀ᶠ u in 𝓝 v, ∀ j, N ≤ j → scaledDensity (scale j) u = 0) ∧
      ConvexOn ℝ univ sourcePrimitive ∧ ContDiff ℝ 1 sourcePrimitive ∧
      ContDiffOn ℝ 3 sourcePrimitive (Ioi 0) ∧ ContDiffOn ℝ 3 sourcePrimitive (Iio 0) ∧
      ScalarLocallyC11On ({0}ᶜ : Set ℝ) sourcePrimitive := by
  refine ⟨fun v hv => ?_, sourcePrimitive_convex, sourcePrimitive_contDiff,
    sourcePrimitive_contDiffOn_off_zero.mono (fun t ht => ne_of_gt ht),
    sourcePrimitive_contDiffOn_off_zero.mono (fun t ht => ne_of_lt ht),
    sourcePrimitive_locallyC11_off_zero⟩
  rcases lt_or_gt_of_ne hv with hneg | hpos
  · refine ⟨0, ?_⟩
    filter_upwards [eventually_lt_nhds hneg] with u hu j _
    by_contra h
    have hs := scaledDensity_support_positive (scale j) (scale_pos j) (scale_le_one j)
      (Function.mem_support.mpr h)
    exact absurd hs.1 (not_lt.mpr hu.le)
  · obtain ⟨N, hN⟩ := exists_tail_below_neighborhood hpos
    refine ⟨N, ?_⟩
    filter_upwards [hN] with u hu j hj
    exact scaledDensity_above (scale_pos j) (hu j hj)

open NormalSpike in
/-- Item `C/11_U/disp/026` (`companion/chapters/11_U.tex:389-391`), corrected on 15 October 2026
(M19; before "near zero", false for $v<0$): "$0\le r'(v)\le6v^2$, $0\le r(v)\le6v^3$ for
$v\ge0$." Both bounds hold for every $v\ge0$, and the first also for $v<0$. Library:
`SourceSpikePropertiesTarget`, `seriesMass_abs_quadratic_bound`. -/
theorem spike_small_bounds :
    (∀ v : ℝ, 0 ≤ v → 0 ≤ deriv sourcePrimitive v ∧ deriv sourcePrimitive v ≤ 6 * v ^ 2 ∧
      0 ≤ sourcePrimitive v ∧ sourcePrimitive v ≤ 6 * v ^ 3) ∧
      ∀ v : ℝ, 0 ≤ deriv sourcePrimitive v ∧ deriv sourcePrimitive v ≤ 6 * v ^ 2 := by
  obtain ⟨-, -, -, hnn, -, hb, -⟩ := sourceSpikeProperties
  refine ⟨fun v hv => ⟨(hb v hv).1, (hb v hv).2.1, hnn v, (hb v hv).2.2⟩, fun v => ?_⟩
  rw [(sourcePrimitive_hasDerivAt v).deriv]
  exact ⟨seriesMass_nonneg v, (le_abs_self _).trans (seriesMass_abs_quadratic_bound v)⟩

open NormalSpike in
/-- Counterexample for item `C/11_U/disp/026` as printed before its correction of 15 October 2026
(M19): "$0\le r(v)\le6v^3$ near zero" fails at every
$v<0$, where $r(v)=0>6v^3$; so it fails in every neighborhood of zero. -/
theorem spike_cubic_bound_fails :
    (∀ v : ℝ, v < 0 → 6 * v ^ 3 < sourcePrimitive v) ∧
      ∀ ε : ℝ, 0 < ε → ∃ v : ℝ, |v| < ε ∧ ¬ sourcePrimitive v ≤ 6 * v ^ 3 := by
  have h (v : ℝ) (hv : v < 0) : 6 * v ^ 3 < sourcePrimitive v := by
    have h0 : sourcePrimitive v = 0 := by simp [sourcePrimitive, not_lt.mpr hv.le]
    rw [h0]
    have : v ^ 3 < 0 := Odd.pow_neg (by decide) hv
    linarith
  refine ⟨h, fun ε hε => ⟨-(ε / 2), ?_, not_le.mpr (h _ (by linarith))⟩⟩
  rw [abs_neg, abs_of_pos (by linarith)]
  linarith

open NormalSpike in
/-- Item `C/11_U/disp/027`, equation (11.19) (`companion/chapters/11_U.tex:391-393`): "However,
$r''(a_j)=a_j^{-3}\to\infty$." For $a_j$ = `scale N` ($j=N+2$): $r'$ is differentiable at $a_j$
with derivative $a_j^{-3}$, and $r''(a_j)\to\infty$. Library: `sourcePrimitive_second_derivative_peak`,
`sourcePrimitive_second_derivative_peaks_unbounded`. -/
theorem spike_peak_curvature :
    (∀ N : ℕ, HasDerivAt (deriv sourcePrimitive) ((scale N ^ 3)⁻¹) (scale N) ∧
        deriv (deriv sourcePrimitive) (scale N) = (scale N ^ 3)⁻¹) ∧
      Tendsto (fun N => deriv (deriv sourcePrimitive) (scale N)) atTop atTop := by
  refine ⟨fun N => ⟨?_, sourcePrimitive_second_derivative_peak N⟩,
    sourcePrimitive_second_derivative_peaks_unbounded⟩
  have he : deriv sourcePrimitive = seriesMass :=
    funext fun v => (sourcePrimitive_hasDerivAt v).deriv
  rw [he, ← density_peak]
  exact seriesMass_hasDerivAt_pos (scale_pos N)

open NormalSpike in
/-- Item `C/11_U/prose/037` (`companion/chapters/11_U.tex:393-394`): "(The second derivative at
zero itself exists and equals zero, but is not continuous there.)" Library:
`sourcePrimitive_hasSecondDerivAt_zero`, `sourcePrimitive_second_derivative_not_continuousAt_zero`. -/
theorem spike_second_derivative_zero :
    HasDerivAt (deriv sourcePrimitive) 0 0 ∧ deriv (deriv sourcePrimitive) 0 = 0 ∧
      ¬ ContinuousAt (deriv (deriv sourcePrimitive)) 0 :=
  ⟨sourcePrimitive_hasSecondDerivAt_zero, sourcePrimitive_second_derivative_zero,
    sourcePrimitive_second_derivative_not_continuousAt_zero⟩

/-! ### Section 11.7: the objective (11.20)

The objective is a variable `F : Vec (m + 2) → ℝ` ($n=m+2\ge2$) with the defining equation
`hF_def`: $F(u,v)=\frac12\|u\|^2+\frac12v^2+|v|+r(v)$ for $u\in\mathbb R^{m+1}$, where
$(u,v)$ is `Fin.cons v u`. It is the library's `NormalSpike.objective (NormalSpike.normal m)`
(`spike_objective_eq`). -/

theorem normal_eq_vnormal (m : ℕ) : NormalSpike.normal m = vnormal (m + 1) := rfl

/-- Item `C/11_U/disp/028`, equation (11.20) (`companion/chapters/11_U.tex:396-401`): "For any
$n\ge2$, consider $F(u,v)=\frac12\|u\|^2+\frac12v^2+|v|+r(v)$, $u\in\mathbb R^{n-1}$." The
function so defined is `NormalSpike.objective (NormalSpike.normal m)`. -/
theorem spike_objective_eq (m : ℕ) (F : Vec (m + 2) → ℝ)
    (hF_def : ∀ (u : Vec (m + 1)) (v : ℝ),
      F (Fin.cons v u) = (1 / 2) * sqNorm u + (1 / 2) * v ^ 2 + |v| + NormalSpike.sourcePrimitive v) :
    F = NormalSpike.objective (NormalSpike.normal m) := by
  funext x
  rw [← Fin.cons_self_tail x, hF_def, NormalSpike.printed_objective_split]

/-- The objective (11.20) satisfies the hypotheses of Theorem 11.1 (with $a=e_v$, $b=0$,
$P=\{v=0\}$, $x_*=0$, $\Omega=\mathbb R^n$, $\mu=1$, $A=P_S$, every $x_0$) and those of Theorem 11.2
($E=\{0\}$, $\Sigma=P$, $P_S\partial F(x)=\{P_Sx\}$); every point of $P$ is a kink. -/
theorem spike_hypotheses (m : ℕ) (F : Vec (m + 2) → ℝ)
    (hF_def : ∀ (u : Vec (m + 1)) (v : ℝ),
      F (Fin.cons v u) = (1 / 2) * sqNorm u + (1 / 2) * v ^ 2 + |v| + NormalSpike.sourcePrimitive v) :
    ConvexOn ℝ univ F ∧ sqNorm (NormalSpike.normal m) = 1 ∧
      (∀ z, F 0 ≤ F z) ∧ (∀ z, F z = F 0 → z = 0) ∧ dot (NormalSpike.normal m) 0 = 0 ∧
      (∀ c, IsCompact {x | F x ≤ c}) ∧ EuclideanStrongConvexOn univ 1 F ∧
      (∀ x, ∀ g ∈ ConvexSubdifferential.subdifferential F x,
        tangentProjection (NormalSpike.normal m) g = tangentProjection (NormalSpike.normal m) x) ∧
      (∀ x, tangentProjection (NormalSpike.normal m) '' ConvexSubdifferential.subdifferential F x =
        {tangentProjection (NormalSpike.normal m) x}) ∧
      LipschitzWith 1 (tangentProjection (NormalSpike.normal m)) ∧
      CenteredSmoothSublinear.LocallyC11On
        (univ \ {x | dot (NormalSpike.normal m) x = 0}) F ∧
      (∀ p, dot (NormalSpike.normal m) p = 0 → ¬ DifferentiableAt ℝ F p) := by
  have hFe := spike_objective_eq m F hF_def
  subst hFe
  open NormalSpike in
  have hsm : CenteredSmoothSublinear.LocallyC11On
      (univ \ {x | dot (normal m) x = 0}) (objective (normal m)) := by
    rw [diff_plane_eq_regularRegion]
    exact composite_locallyC11_off_interface isOpen_univ quadratic_locallyC11 (normal m) 0
      isClosed_singleton normalPenalty_locallyC11_off_zero
      (fun x _ => by simp only [objective, normalCoordinate, sub_zero])
  open NormalSpike in
  refine ⟨objective_convex _, normal_unit m, objective_minimum _, objective_unique_minimum _,
    by simp [dot], objective_sublevel_compact _, objective_strongConvex _,
    fun x g hg => objective_support_tangent _ (normal_unit m) x g hg, fun x => ?_,
    normal_tangent_lipschitz m, hsm,
    fun p hp => objective_not_differentiable_on_interface _ (normal_unit m) p hp⟩
  open NormalSpike in
  ext w
  simp only [mem_image, mem_singleton_iff]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact objective_support_tangent _ (normal_unit m) x g hg
  · rintro rfl
    obtain ⟨g, hg⟩ := ConvexSubdifferential.subdifferential_nonempty (objective_convex (normal m)) x
    exact ⟨g, hg, objective_support_tangent _ (normal_unit m) x g hg⟩

/-- Item `C/11_U/prose/038` (`companion/chapters/11_U.tex:401`): "It is 1-strongly convex and
coercive, with unique minimizer zero." Library: `objective_strongConvex`, `objective_coercive`,
`objective_minimum`, `objective_unique_minimum`. -/
theorem spike_objective_geometry (m : ℕ) (F : Vec (m + 2) → ℝ)
    (hF_def : ∀ (u : Vec (m + 1)) (v : ℝ),
      F (Fin.cons v u) = (1 / 2) * sqNorm u + (1 / 2) * v ^ 2 + |v| + NormalSpike.sourcePrimitive v) :
    EuclideanStrongConvexOn univ 1 F ∧ Tendsto F (cocompact (Vec (m + 2))) atTop ∧
      (∀ x, F 0 ≤ F x) ∧ (∀ x, F x = F 0 → x = 0) := by
  have hFe := spike_objective_eq m F hF_def
  subst hFe
  exact ⟨NormalSpike.objective_strongConvex _, NormalSpike.objective_coercive _,
    NormalSpike.objective_minimum _, NormalSpike.objective_unique_minimum _⟩

/-- Item `C/11_U/prose/039` (`companion/chapters/11_U.tex:401-403`): "Its only nondifferentiable
hyperplane is $v=0$; its tangential gradient is $u$, which is globally Lipschitz." $F$ is
differentiable exactly off $\{v=0\}$; every subgradient at $(u,v)$ has tangential projection
$P_S(u,v)=(u,0)$; and $P_S$ is Lipschitz (constant $1$). Library: `objective_differentiable_iff`,
`objective_support_tangent`, `normal_tangent_lipschitz`. -/
theorem spike_objective_interface (m : ℕ) (F : Vec (m + 2) → ℝ)
    (hF_def : ∀ (u : Vec (m + 1)) (v : ℝ),
      F (Fin.cons v u) = (1 / 2) * sqNorm u + (1 / 2) * v ^ 2 + |v| + NormalSpike.sourcePrimitive v) :
    (∀ x, DifferentiableAt ℝ F x ↔ x 0 ≠ 0) ∧
      (∀ (u : Vec (m + 1)) (v : ℝ), ∀ g ∈ ConvexSubdifferential.subdifferential F (Fin.cons v u),
        tangentProjection (NormalSpike.normal m) g = Fin.cons 0 u) ∧
      LipschitzWith 1 (tangentProjection (NormalSpike.normal m)) := by
  have hFe := spike_objective_eq m F hF_def
  subst hFe
  refine ⟨fun x => ?_, fun u v g hg => ?_, NormalSpike.normal_tangent_lipschitz m⟩
  · rw [NormalSpike.objective_differentiable_iff _ (NormalSpike.normal_unit m),
      NormalSpike.normal_coordinate]
  · rw [NormalSpike.objective_support_tangent _ (NormalSpike.normal_unit m) _ g hg,
      normal_eq_vnormal, tangent_vnormal, Fin.tail_cons]

/-- Item `C/11_U/prose/040` (`companion/chapters/11_U.tex:403-405`): "Theorem 11.1 therefore
proves global convergence of every admissible full-BFGS run, for arbitrary coupled SPD
initialization." Proved from `one_exceptional_hyperplane` with the hypotheses
`spike_hypotheses` ($\Omega=\mathbb R^n$, any start). Library: `spikeObjectiveConvergence`. -/
theorem spike_objective_convergence (m : ℕ) (F : Vec (m + 2) → ℝ)
    (hF_def : ∀ (u : Vec (m + 1)) (v : ℝ),
      F (Fin.cons v u) = (1 / 2) * sqNorm u + (1 / 2) * v ^ 2 + |v| + NormalSpike.sourcePrimitive v) :
    ∀ R : AdmissibleBFGSRun (m + 2) F,
      Tendsto (fun k => F (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0) := by
  intro R
  obtain ⟨hconv, ha, hmin, huniq, hplane, hcpt, hstrong, hA, -, hLip, hsm, -⟩ :=
    spike_hypotheses m F hF_def
  have hF0 : F 0 = 0 := by
    have h := hF_def 0 0
    have hc : (Fin.cons (0 : ℝ) (0 : Vec (m + 1)) : Vec (m + 2)) = 0 := by
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    rw [hc] at h
    rw [h, NormalSpike.sourcePrimitive]
    simp [sqNorm]
  have h := one_exceptional_hyperplane F hconv (NormalSpike.normal m) ha 0 _ rfl 0 hmin huniq
    hplane (R.x 0) _ rfl (hcpt _) univ isOpen_univ convex_univ (subset_univ _) 1 one_pos hstrong
    (tangentProjection (NormalSpike.normal m)) (fun x _ g hg => hA x g hg) 1
    hLip.lipschitzOnWith hsm R rfl
  rwa [hF0] at h

/-- The sample points $x_j=(u_0,a_j)$: coordinates. -/
theorem sample_dot (m : ℕ) (u0 : Vec (m + 1)) (v : ℝ) :
    dot (NormalSpike.normal m) (Fin.cons v u0 : Vec (m + 2)) = v := by
  rw [NormalSpike.normal_coordinate, Fin.cons_zero]

theorem sample_sqNorm (m : ℕ) (u0 : Vec (m + 1)) (v : ℝ) :
    sqNorm (Fin.cons v u0 : Vec (m + 2)) = v ^ 2 + sqNorm u0 := by
  simp only [sqNorm, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

/-- Item `C/11_U/prose/042` (`companion/chapters/11_U.tex:407-409`): "Fix any sufficiently small
nonzero $u_0$, and take $x_j=(u_0,a_j)$. Their objective values approach the positive level
$\|u_0\|^2/2$." For every $u_0\in\mathbb R^{n-1}$, $F(u_0,a_j)\to\|u_0\|^2/2$, which is positive
when $u_0\neq0$ ($a_j$ = `scale N`). -/
theorem spike_sample_values (m : ℕ) (F : Vec (m + 2) → ℝ)
    (hF_def : ∀ (u : Vec (m + 1)) (v : ℝ),
      F (Fin.cons v u) = (1 / 2) * sqNorm u + (1 / 2) * v ^ 2 + |v| + NormalSpike.sourcePrimitive v)
    (u0 : Vec (m + 1)) :
    Tendsto (fun N => F (Fin.cons (NormalSpike.scale N) u0)) atTop (𝓝 ((1 / 2) * sqNorm u0)) ∧
      (u0 ≠ 0 → 0 < (1 / 2) * sqNorm u0) := by
  refine ⟨?_, fun hu0 => ?_⟩
  · simp_rw [hF_def]
    have hc : Continuous (fun s : ℝ => (1 / 2) * sqNorm u0 + (1 / 2) * s ^ 2 + |s| +
        NormalSpike.sourcePrimitive s) := by
      have := NormalSpike.sourcePrimitive_contDiff.continuous
      fun_prop
    have h := (hc.tendsto 0).comp NormalSpike.scale_tendsto_zero
    have h0 : NormalSpike.sourcePrimitive 0 = 0 := by simp [NormalSpike.sourcePrimitive]
    simpa [Function.comp_def, h0] using h
  · have hpos : 0 < sqNorm u0 := lt_of_le_of_ne (sqNorm_nonneg _)
      (fun h => hu0 ((CertificateGeometry.sqNorm_eq_zero_iff u0).mp h.symm))
    positivity

/-- Item `C/11_U/disp/029`, equation (11.21) (`companion/chapters/11_U.tex:410-413`): "At these
smooth points,"
\[ x_j^T\nabla^2F(x_j)x_j=\|u_0\|^2+a_j^2+a_j^{-1}\longrightarrow\infty. \]
For every $u_0$ and $x_j=(u_0,a_j)$: $F$ is $C^3$ near $x_j$, its Hessian matrix
(`RadialHessian.matrix F x`, the matrix of the second Fréchet derivative) satisfies the identity,
and the right side tends to $\infty$. Library: `objective_contDiffAt_pos`,
`objective_radial_hessian`, `density_peak`. -/
theorem spike_sample_hessian (m : ℕ) (F : Vec (m + 2) → ℝ)
    (hF_def : ∀ (u : Vec (m + 1)) (v : ℝ),
      F (Fin.cons v u) = (1 / 2) * sqNorm u + (1 / 2) * v ^ 2 + |v| + NormalSpike.sourcePrimitive v)
    (u0 : Vec (m + 1)) :
    (∀ N : ℕ, ContDiffAt ℝ 3 F (Fin.cons (NormalSpike.scale N) u0) ∧
      dot (Fin.cons (NormalSpike.scale N) u0)
          ((RadialHessian.matrix F (Fin.cons (NormalSpike.scale N) u0)) *ᵥ
            (Fin.cons (NormalSpike.scale N) u0)) =
        sqNorm u0 + NormalSpike.scale N ^ 2 + (NormalSpike.scale N)⁻¹) ∧
      Tendsto (fun N : ℕ => sqNorm u0 + NormalSpike.scale N ^ 2 + (NormalSpike.scale N)⁻¹)
        atTop atTop := by
  have hFe := spike_objective_eq m F hF_def
  subst hFe
  refine ⟨fun N => ?_, ?_⟩
  · have hv : 0 < dot (NormalSpike.normal m) (Fin.cons (NormalSpike.scale N) u0 : Vec (m + 2)) := by
      rw [sample_dot]; exact NormalSpike.scale_pos N
    refine ⟨NormalSpike.objective_contDiffAt_pos _ _ hv, ?_⟩
    rw [NormalSpike.objective_radial_hessian _ _ hv, sample_dot, sample_sqNorm,
      NormalSpike.density_peak]
    have hn := (NormalSpike.scale_pos N).ne'
    field_simp
    ring
  · have hi : Tendsto (fun N => (NormalSpike.scale N)⁻¹) atTop atTop := by
      apply tendsto_inv_nhdsGT_zero.comp
      exact tendsto_nhdsWithin_iff.mpr
        ⟨NormalSpike.scale_tendsto_zero, Eventually.of_forall NormalSpike.scale_pos⟩
    apply tendsto_atTop_mono (fun N => ?_) hi
    nlinarith [sqNorm_nonneg u0, sq_nonneg (NormalSpike.scale N)]

/-- The second-order limit of a model bound: if $\varphi$ is differentiable near $0$, $\varphi'$
has derivative $D$ at $0$, and $\varphi(t)-\varphi(0)-t\varphi'(0)\le\frac M2t^2$ for
$0\le t\le\theta$, then $D\le M$. -/
theorem second_derivative_le_of_model_bound {φ : ℝ → ℝ} {D M θ : ℝ} (hθ : 0 < θ)
    (hdiff : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ φ t)
    (hD : HasDerivAt (deriv φ) D 0)
    (hbound : ∀ t, 0 ≤ t → t ≤ θ → φ t - φ 0 - t * deriv φ 0 ≤ M / 2 * t ^ 2) : D ≤ M := by
  by_contra hlt
  push_neg at hlt
  set M' := (M + D) / 2 with hM'
  have hM'D : M' < D := by rw [hM']; linarith
  have hMM' : M < M' := by rw [hM']; linarith
  have hev1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), M' < t⁻¹ • (deriv φ (0 + t) - deriv φ 0) :=
    hD.tendsto_slope_zero_right.eventually (lt_mem_nhds hM'D)
  obtain ⟨ε₁, hε₁, h1⟩ := Metric.eventually_nhds_iff.mp hdiff
  obtain ⟨ε₂, hε₂, h2⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hev1)
  set δ := min θ (min ε₁ ε₂) / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hδθ : δ ≤ θ := by
    have := min_le_left θ (min ε₁ ε₂)
    rw [hδ]; linarith
  have hδ1 : δ < ε₁ := by
    have := (min_le_right θ (min ε₁ ε₂)).trans (min_le_left ε₁ ε₂)
    rw [hδ]; linarith [min_le_left θ (min ε₁ ε₂)]
  have hδ2 : δ < ε₂ := by
    have := (min_le_right θ (min ε₁ ε₂)).trans (min_le_right ε₁ ε₂)
    rw [hδ]; linarith [min_le_left θ (min ε₁ ε₂)]
  have hdiffI : ∀ t ∈ Icc (0 : ℝ) δ, DifferentiableAt ℝ φ t := by
    intro t ht
    apply h1
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
    linarith [ht.2]
  let ψ : ℝ → ℝ := fun t => φ t - φ 0 - t * deriv φ 0 - M' / 2 * t ^ 2
  have hψd : ∀ t, DifferentiableAt ℝ φ t →
      HasDerivAt ψ (deriv φ t - deriv φ 0 - M' * t) t := by
    intro t ht
    have h := ((ht.hasDerivAt.sub_const (φ 0)).sub ((hasDerivAt_id t).mul_const (deriv φ 0))).sub
      ((hasDerivAt_pow 2 t).const_mul (M' / 2))
    convert h using 1
    simp only [id_eq, one_mul, Nat.cast_ofNat]
    ring
  have hmono : MonotoneOn ψ (Icc 0 δ) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 δ)
    · intro t ht
      exact (hψd t (hdiffI t ht)).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (hψd t (hdiffI t ⟨ht.1.le, ht.2.le⟩)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hψd t (hdiffI t ⟨ht.1.le, ht.2.le⟩)).deriv]
      have hs := h2 (y := t) (by rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]; linarith [ht.2]) ht.1
      rw [zero_add, smul_eq_mul] at hs
      have hmul := (mul_lt_mul_left ht.1).mpr hs
      rw [← mul_assoc, mul_inv_cancel₀ ht.1.ne', one_mul] at hmul
      linarith
  have hle := hmono ⟨le_refl 0, hδ0.le⟩ ⟨hδ0.le, le_refl δ⟩ hδ0.le
  have hb := hbound δ hδ0.le hδθ
  simp only [ψ, sub_self, zero_mul, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero] at hle
  have hsq : 0 < δ ^ 2 := by positivity
  nlinarith

/-- The inward second-order limit at a sample point: under (11.20), if an inward Taylor estimate
$F(x-t(x-0))-F(x)+t\,g^T(x-0)\le\frac M2t^2$ ($0\le t\le\theta$) holds at $x=x_j=(u_0,a_j)$ with
$g=\nabla F(x)$, then $x^T\nabla^2F(x)x\le M$. -/
theorem spike_inward_bound_hessian (m : ℕ) (F : Vec (m + 2) → ℝ)
    (hF_def : ∀ (u : Vec (m + 1)) (v : ℝ),
      F (Fin.cons v u) = (1 / 2) * sqNorm u + (1 / 2) * v ^ 2 + |v| + NormalSpike.sourcePrimitive v)
    (u0 : Vec (m + 1)) (N : ℕ) (x : Vec (m + 2)) (hx : x = Fin.cons (NormalSpike.scale N) u0)
    (g : Vec (m + 2)) (hg : HasFDerivAt F (gradientFunctional g) x) (M θ : ℝ) (hθ : 0 < θ)
    (hIR : ∀ t : ℝ, 0 ≤ t → t ≤ θ →
      F (x - t • (x - 0)) - F x + t * dot g (x - 0) ≤ M / 2 * t ^ 2) :
    dot x ((RadialHessian.matrix F x) *ᵥ x) ≤ M := by
  have hFe := spike_objective_eq m F hF_def
  subst hFe hx
  set x : Vec (m + 2) := Fin.cons (NormalSpike.scale N) u0 with hxdef
  set a := NormalSpike.normal m
  have hv : 0 < dot a x := by rw [sample_dot]; exact NormalSpike.scale_pos N
  set φ : ℝ → ℝ := fun t => NormalSpike.objective a ((1 - t) • x) with hφ
  have hray (t : ℝ) : HasDerivAt (fun s : ℝ => (1 - s) • x) (-x) t := by
    simpa only [sub_zero, zero_sub, neg_smul, one_smul] using
      (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).smul_const x)
  have hdiff : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ φ t := by
    filter_upwards [eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)] with t ht
    have hpos : 0 < dot a ((1 - t) • x) := by
      rw [dot_smul_right]; exact mul_pos (sub_pos.mpr ht) hv
    exact ((NormalSpike.objective_hasFDerivAt_pos a _ hpos).comp_hasDerivAt t
      (hray t)).differentiableAt
  have hD := NormalSpike.objective_hasSecondDerivAt_inward_ray a x hv
  rw [← NormalSpike.objective_radial_hessian a x hv] at hD
  have hφ0 : φ 0 = NormalSpike.objective a x := by simp [hφ]
  have hd0 : deriv φ 0 = -dot g x := by
    have h := (hg.comp_hasDerivAt_of_eq (0 : ℝ) (hray 0) (by simp)).deriv
    have hφc : (NormalSpike.objective a ∘ fun s : ℝ => (1 - s) • x) = φ := rfl
    rw [hφc] at h
    rw [h, map_neg, gradientFunctional_apply]
  apply second_derivative_le_of_model_bound hθ hdiff hD
  intro t ht0 htθ
  have h := hIR t ht0 htθ
  rw [hφ0, hd0]
  have hx' : x - t • (x - 0) = (1 - t) • x := by module
  rw [hx', sub_zero] at h
  simp only [hφ]
  linarith

/-- Item `C/11_U/prose/043` (`companion/chapters/11_U.tex:413-415`): "A uniform inward Taylor
estimate on that fixed positive band would, by taking its second-order limit at each $x_j$,
bound the left side of (11.21). This is impossible." For $u_0\neq0$, $K=\{F\le b\}$ with
$b>\|u_0\|^2/2$ and the band $\eta=\|u_0\|^2/4$ (eventually containing every $x_j$), no constants
$M,\theta\in(0,1/2]$ give the inward estimate of (IR) on that band (the second-order limit is
`spike_inward_bound_hessian`); in particular (IR) fails on $K$. -/
theorem spike_ir_fails (m : ℕ) (F : Vec (m + 2) → ℝ)
    (hF_def : ∀ (u : Vec (m + 1)) (v : ℝ),
      F (Fin.cons v u) = (1 / 2) * sqNorm u + (1 / 2) * v ^ 2 + |v| + NormalSpike.sourcePrimitive v)
    (u0 : Vec (m + 1)) (hu0 : u0 ≠ 0) (b : ℝ) (hb : (1 / 2) * sqNorm u0 < b) :
    ¬ (∃ M θ : ℝ, 0 < θ ∧ θ ≤ 1 / 2 ∧
        ∀ x g : Vec (m + 2), x ∈ {x | F x ≤ b} → HasFDerivAt F (gradientFunctional g) x →
          F 0 + sqNorm u0 / 4 ≤ F x → ∀ t : ℝ, 0 ≤ t → t ≤ θ →
            0 ≤ F (x - t • (x - 0)) - F x + t * dot g (x - 0) ∧
              F (x - t • (x - 0)) - F x + t * dot g (x - 0) ≤ M / 2 * t ^ 2) ∧
      ¬ IR F 0 {x | F x ≤ b} := by
  have hF0 : F 0 = 0 := by
    rw [spike_objective_eq m F hF_def]
    exact NormalSpike.objective_zero _
  have hpos : 0 < sqNorm u0 := lt_of_le_of_ne (sqNorm_nonneg _)
    (fun h => hu0 ((CertificateGeometry.sqNorm_eq_zero_iff u0).mp h.symm))
  have hband : ¬ (∃ M θ : ℝ, 0 < θ ∧ θ ≤ 1 / 2 ∧
        ∀ x g : Vec (m + 2), x ∈ {x | F x ≤ b} → HasFDerivAt F (gradientFunctional g) x →
          F 0 + sqNorm u0 / 4 ≤ F x → ∀ t : ℝ, 0 ≤ t → t ≤ θ →
            0 ≤ F (x - t • (x - 0)) - F x + t * dot g (x - 0) ∧
              F (x - t • (x - 0)) - F x + t * dot g (x - 0) ≤ M / 2 * t ^ 2) := by
    rintro ⟨M, θ, hθ, -, hM⟩
    obtain ⟨hlim, -⟩ := spike_sample_values m F hF_def u0
    obtain ⟨hhess, hunb⟩ := spike_sample_hessian m F hF_def u0
    have hK : ∀ᶠ N in atTop, F (Fin.cons (NormalSpike.scale N) u0) ≤ b :=
      (hlim.eventually (gt_mem_nhds hb)).mono fun _ h => h.le
    have hB : ∀ᶠ N in atTop, F 0 + sqNorm u0 / 4 ≤ F (Fin.cons (NormalSpike.scale N) u0) := by
      rw [hF0, zero_add]
      exact (hlim.eventually (lt_mem_nhds (by linarith))).mono fun _ h => h.le
    have hbig := hunb.eventually (eventually_gt_atTop M)
    obtain ⟨N, hKN, hBN, hbigN⟩ := (hK.and (hB.and hbig)).exists
    have hFe := spike_objective_eq m F hF_def
    have hv : 0 < dot (NormalSpike.normal m) (Fin.cons (NormalSpike.scale N) u0 : Vec (m + 2)) := by
      rw [sample_dot]; exact NormalSpike.scale_pos N
    have hg : HasFDerivAt F (gradientFunctional (NormalSpike.positiveGradient (NormalSpike.normal m)
        (Fin.cons (NormalSpike.scale N) u0))) (Fin.cons (NormalSpike.scale N) u0) := by
      rw [hFe]; exact NormalSpike.objective_hasFDerivAt_pos _ _ hv
    have hle := spike_inward_bound_hessian m F hF_def u0 N _ rfl _ hg M θ hθ
      (fun t h0 h1 => (hM _ _ hKN hg hBN t h0 h1).2)
    rw [(hhess N).2] at hle
    linarith
  refine ⟨hband, fun hIR => hband ?_⟩
  obtain ⟨M, θ, hθ, hθ', hM⟩ := hIR (sqNorm u0 / 4) (by positivity)
  exact ⟨M, θ, hθ, hθ', hM⟩

open NormalSpike RadialCertificate in
/-- Item `C/11_U/prose/044` (`companion/chapters/11_U.tex:415-416`): "The equivalence of
Theorem~\ref{R:thm:equiv} between inward radial smoothness and RS therefore rules out RS on that
band." (Wording point W11 applied on 15 October 2026; before "The recorded equivalence".) For
$u_0\neq0$, $K=\{F\le b\}$ with $b>\|u_0\|^2/2$ and the band $\eta=\|u_0\|^2/4$ (the band of
`spike_ir_fails`, item `prose/043`), no constant $C$ satisfies the (RS) inequality on that band; in
particular (RS) fails on $K$. The proof uses the pairs $(x_j,(1-t)x_j)$, $0<t\le1/4$, directly (as
the library's `not_radial_secant_sublevel_of_tangent_height`), for an arbitrary $u_0$; the route
through the equivalence (RS)$\Rightarrow$(IR) of Chapter 4 gives the weaker conclusion that (RS)
fails on $K$ (from `spike_ir_fails`). -/
theorem spike_rs_fails_band (m : ℕ) (F : Vec (m + 2) → ℝ)
    (hF_def : ∀ (u : Vec (m + 1)) (v : ℝ),
      F (Fin.cons v u) = (1 / 2) * sqNorm u + (1 / 2) * v ^ 2 + |v| + sourcePrimitive v)
    (u0 : Vec (m + 1)) (hu0 : u0 ≠ 0) (b : ℝ) (hb : (1 / 2) * sqNorm u0 < b) :
    ¬ (∃ C : ℝ, ∀ x z g h : Vec (m + 2), x ∈ {x | F x ≤ b} → z ∈ {x | F x ≤ b} →
        HasFDerivAt F (gradientFunctional g) x → HasFDerivAt F (gradientFunctional h) z →
        F 0 + sqNorm u0 / 4 ≤ F z → F z ≤ F x → 0 < dot (h - g) (z - x) →
        (dot (h - g) (z - 0)) ^ 2 ≤ C * dot (h - g) (z - x)) ∧
      ¬ RS F 0 {x | F x ≤ b} := by
  have hFe := spike_objective_eq m F hF_def
  have hF0 : F 0 = 0 := by rw [hFe]; exact objective_zero _
  have hpos : 0 < sqNorm u0 := lt_of_le_of_ne (sqNorm_nonneg _)
    (fun h => hu0 ((CertificateGeometry.sqNorm_eq_zero_iff u0).mp h.symm))
  have hband : ¬ (∃ C : ℝ, ∀ x z g h : Vec (m + 2), x ∈ {x | F x ≤ b} → z ∈ {x | F x ≤ b} →
        HasFDerivAt F (gradientFunctional g) x → HasFDerivAt F (gradientFunctional h) z →
        F 0 + sqNorm u0 / 4 ≤ F z → F z ≤ F x → 0 < dot (h - g) (z - x) →
        (dot (h - g) (z - 0)) ^ 2 ≤ C * dot (h - g) (z - x)) := by
    rintro ⟨C, hC⟩
    obtain ⟨hlim, -⟩ := spike_sample_values m F hF_def u0
    obtain ⟨hhess, hunb⟩ := spike_sample_hessian m F hF_def u0
    have hK : ∀ᶠ N in atTop, F (Fin.cons (scale N) u0) ≤ b :=
      (hlim.eventually (gt_mem_nhds hb)).mono fun _ h => h.le
    have hbig := hunb.eventually (eventually_gt_atTop (4 * C))
    obtain ⟨N, hKN, hbigN⟩ := (hK.and hbig).exists
    subst hFe
    set x : Vec (m + 2) := Fin.cons (scale N) u0 with hxdef
    have hv : 0 < dot (normal m) x := by rw [sample_dot]; exact scale_pos N
    have hle := radial_curvature_le_of_pair_bound (normal m) x hv (by norm_num : (0 : ℝ) < 1 / 4)
      (by norm_num) (C := C) (fun t ht hthalf => by
        set z := (1 - t) • x with hz
        have htone : t ≤ 1 := by linarith
        have hzpos : 0 < dot (normal m) z := by
          rw [hz, dot_smul_right]; exact mul_pos (by linarith) hv
        have horder : objective (normal m) z ≤ objective (normal m) x := by
          have hp := (objective_convex (normal m)).2 (mem_univ x) (mem_univ 0)
            (show 0 ≤ 1 - t by linarith) ht.le (by ring : (1 - t) + t = 1)
          simp only [smul_zero, add_zero, objective_zero, smul_eq_mul, mul_zero] at hp
          have hn := objective_minimum (normal m) x
          rw [objective_zero] at hn
          exact hp.trans (by nlinarith)
        have hzband : objective (normal m) 0 + sqNorm u0 / 4 ≤ objective (normal m) z := by
          rw [objective_zero, zero_add]
          have hlower := objective_lower_bound (normal m) z
          have hsq : sqNorm z = (1 - t) ^ 2 * (scale N ^ 2 + sqNorm u0) := by
            rw [hz, CertificateGeometry.sqNorm_smul, hxdef, sample_sqNorm]
          rw [hsq] at hlower
          have hfac : (9 / 16 : ℝ) ≤ (1 - t) ^ 2 := by nlinarith
          have hnon := mul_nonneg (sq_nonneg (1 - t)) (sq_nonneg (scale N))
          nlinarith [mul_le_mul_of_nonneg_right hfac hpos.le]
        have hT := (radial_contraction_identities (normal m) x t).1
        have hTpos : 0 < secantCurvature x z (positiveGradient (normal m) x)
            (positiveGradient (normal m) z) := by
          rw [hz, hT]; exact mul_pos ht (radial_difference_positive (normal m) x hv ht htone)
        exact hC x z _ _ hKN (horder.trans hKN) (objective_hasFDerivAt_pos _ _ hv)
          (objective_hasFDerivAt_pos _ _ hzpos) hzband horder hTpos)
    rw [(hhess N).2.symm.trans (by
      rw [objective_radial_hessian _ _ hv])] at hbigN
    linarith
  refine ⟨hband, fun hRS => hband ?_⟩
  obtain ⟨C, hC⟩ := hRS (sqNorm u0 / 4) (by positivity)
  exact ⟨C, hC⟩

/-- Item `C/11_U/prose/045` (`companion/chapters/11_U.tex:416-417`): "Choosing $u_0$ arbitrarily
small gives failure in every neighborhood of the optimizer." (RS) fails on every neighborhood $W$
of $0$ (item `prose/041`, line 407: "RS fails in every neighborhood of zero"). Library:
`NormalSpike.not_radial_secant_neighborhood`. -/
theorem spike_rs_fails_nhds (m : ℕ) (F : Vec (m + 2) → ℝ)
    (hF_def : ∀ (u : Vec (m + 1)) (v : ℝ),
      F (Fin.cons v u) = (1 / 2) * sqNorm u + (1 / 2) * v ^ 2 + |v| + NormalSpike.sourcePrimitive v) :
    ∀ W ∈ 𝓝 (0 : Vec (m + 2)), ¬ RS F 0 W := by
  intro W hW hRS
  rw [spike_objective_eq m F hF_def, RS_iff_library] at hRS
  exact NormalSpike.not_radial_secant_neighborhood m hW hRS

/-! ### Section 11.7.1: exact evaluation of the series -/

open NormalSpike in
/-- Item `C/11_U/prose/052` (`companion/chapters/11_U.tex:433-434`): "There is no need to
truncate (11.18). All bumps below a query can be summed using geometric series, with at most one
partially included bump." Every query $v$ meets the support of at most one bump; for $v>0$ there is
an index $N$ such that every bump $j\ge N$ lies below $v$, and then
$r(v)=\sum_{j<N}\int_0^v(v-t)\,a_j^{-3}\eta((t-a_j)/a_j^5)\,dt+\frac{64}{45}a_N^2v-\frac{128}{105}a_N^3$
($a_j$ = `scale j`, reindexed), the last two terms being the geometric sums of the contributions
$\frac{16}{15}a_j^2v-\frac{16}{15}a_j^3$ of the bumps below $v$. Library:
`at_most_one_partial_bump`, `seriesPrimitive_tail_formula`, `tailMass_eq`, `tailMoment_eq`. -/
theorem series_exact :
    (∀ v : ℝ, {j : ℕ | v ∈ Function.support (scaledDensity (scale j))}.Subsingleton) ∧
      (∀ v : ℝ, 0 < v → ∃ N : ℕ, ∀ j, N ≤ j → scale j + scale j ^ 5 < v) ∧
      ∀ (v : ℝ) (N : ℕ), (∀ j, N ≤ j → scale j + scale j ^ 5 < v) →
        sourcePrimitive v = (∑ j ∈ Finset.range N, ∫ t in (0 : ℝ)..v, (v - t) * scaledDensity (scale j) t) +
          (64 / 45) * scale N ^ 2 * v - (128 / 105) * scale N ^ 3 := by
  refine ⟨at_most_one_partial_bump, fun v hv => (exists_tail_below_neighborhood hv).imp
    fun N hN => hN.self_of_nhds, fun v N hN => ?_⟩
  rw [← seriesPrimitive_eq_source, seriesPrimitive_tail_formula N v hN, tailMass_eq, tailMoment_eq]
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  rw [scaledPrimitive_kernel_integral (scale_pos j) (scale_le_one j)]

open NormalSpike in
/-- Item `C/11_U/disp/030` (`companion/chapters/11_U.tex:435-438`): the polynomials
$P(t)=t-\frac23t^3+\frac15t^5$ and $Q(t)=\frac12t^2-\frac12t^4+\frac16t^6$ are the library's
`massPoly` and `momentPoly`. -/
theorem mass_moment_polys (t : ℝ) :
    massPoly t = t - (2 / 3) * t ^ 3 + (1 / 5) * t ^ 5 ∧
      momentPoly t = (1 / 2) * t ^ 2 - (1 / 2) * t ^ 4 + (1 / 6) * t ^ 6 := ⟨rfl, rfl⟩

open NormalSpike in
/-- Item `C/11_U/disp/031` (`companion/chapters/11_U.tex:440-442`), with item `prose/053`
(lines 438-440): "For a query inside the bump centered at $a=a_j$, with $t=(v-a)/a^5$, the
partial mass is $a^2[P(t)+8/15]$, and its first moment is
$a^3[P(t)+8/15]+a^7[Q(t)-1/6]$." For $a$ = `scale N` and $v\in[a-a^5,a+a^5]$:
$\int_0^v a^{-3}\eta((s-a)/a^5)\,ds$ and $\int_0^v s\,a^{-3}\eta((s-a)/a^5)\,ds$ (the bump vanishes
on $(-\infty,0]$). Library: `scaledMass_integral`, `scaledMass_partial`, `scaledMoment_integral`,
`scaledMoment_partial`. -/
theorem partial_bump (N : ℕ) (a : ℝ) (ha : a = scale N) (v : ℝ) (hv : v ∈ Icc (a - a ^ 5) (a + a ^ 5))
    (t : ℝ) (ht : t = (v - a) / a ^ 5) :
    (∫ s in (0 : ℝ)..v, scaledDensity a s) = a ^ 2 * (massPoly t + 8 / 15) ∧
      (∫ s in (0 : ℝ)..v, s * scaledDensity a s) =
        a ^ 3 * (massPoly t + 8 / 15) + a ^ 7 * (momentPoly t - 1 / 6) := by
  subst ha ht
  refine ⟨?_, ?_⟩
  · rw [scaledMass_integral (scale_pos N) (scale_le_one N), scaledMass_partial (scale_pos N) hv]
  · rw [scaledMoment_integral (scale_pos N) (scale_le_one N), scaledMoment_partial (scale_pos N) hv]

open NormalSpike in
/-- The first moment of one bump: $\int v\,a^{-3}\eta((v-a)/a^5)\,dv=\frac{16}{15}a^3$. -/
theorem bump_first_moment (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    (∫ v, v * scaledDensity a v) = (16 / 15) * a ^ 3 := by
  have hsupp : Function.support (fun v => v * scaledDensity a v) ⊆ Ioc 0 (3 * a) :=
    (Function.support_mul_subset_right _ _).trans (scaledDensity_support_positive a ha ha1)
  rw [← intervalIntegral.integral_eq_integral_of_support_subset hsupp,
    scaledMoment_integral ha ha1]
  have hp : a ^ 5 ≤ a := by
    calc a ^ 5 = a ^ 4 * a := by ring
      _ ≤ 1 * a := mul_le_mul_of_nonneg_right (pow_le_one₀ ha.le ha1) ha.le
      _ = a := one_mul a
  have habove : a + a ^ 5 < 3 * a := by linarith
  rw [scaledMoment, scaledMass_above ha habove, scaledPrimitive_above ha habove]
  ring

open NormalSpike in
/-- Item `C/11_U/prose/054` (`companion/chapters/11_U.tex:442-443`): "All smaller bumps have
total mass $(16/45)a^2$ and first moment $(16/105)a^3$." For $a=a_N$ (`scale N`), the bumps
$j>N$ have total mass $\sum_{j>N}\int a_j^{-3}\eta=\frac{16}{45}a^2$ and total first moment
$\frac{16}{105}a^3$. Library: `smaller_tail_mass`, `smaller_tail_moment`,
`scaledDensity_total_mass`. -/
theorem smaller_bumps (N : ℕ) :
    (∑' j : ℕ, ∫ v, scaledDensity (scale (j + (N + 1))) v) = (16 / 45) * scale N ^ 2 ∧
      (∑' j : ℕ, ∫ v, v * scaledDensity (scale (j + (N + 1))) v) = (16 / 105) * scale N ^ 3 := by
  constructor
  · simp_rw [scaledDensity_total_mass _ (scale_pos _) (scale_le_one _)]
    rw [← smaller_tail_mass, tailMass]
  · simp_rw [bump_first_moment _ (scale_pos _) (scale_le_one _)]
    rw [← smaller_tail_moment, tailMoment]

open NormalSpike in
/-- Item `C/11_U/prose/055` (`companion/chapters/11_U.tex:443-444`): "This gives exact rational
function and derivative values for rational queries." The computable rational functions
`rationalValueOracle`, `rationalDerivativeOracle`, `rationalSecondDerivativeOracle`
($\mathbb Q\to\mathbb Q$) return exactly $r(v)$, $r'(v)$ and $r''(v)$ at every rational $v$.
Library: `rationalSpikeOracle`. -/
theorem rational_oracle (v : ℚ) :
    (rationalValueOracle v : ℝ) = sourcePrimitive v ∧
      (rationalDerivativeOracle v : ℝ) = deriv sourcePrimitive v ∧
      (rationalSecondDerivativeOracle v : ℝ) = deriv (deriv sourcePrimitive) v :=
  rationalSpikeOracle v

open NormalSpike in
/-- Item `C/11_U/disp/032` (`companion/chapters/11_U.tex:444-447`): "At a peak,"
\[ r(a)=\frac{64}{315}a^3+\frac16a^7,\qquad r'(a)=\frac89a^2,\qquad r''(a)=a^{-3}, \]
for $a=a_j$ (`scale N`), identities of the full series (item `prose/056`). Library:
`sourcePrimitive_peak`, `sourcePrimitive_derivative_peak`, `sourcePrimitive_second_derivative_peak`. -/
theorem spike_peak_values (N : ℕ) (a : ℝ) (ha : a = scale N) :
    sourcePrimitive a = (64 / 315) * a ^ 3 + (1 / 6) * a ^ 7 ∧
      deriv sourcePrimitive a = (8 / 9) * a ^ 2 ∧ deriv (deriv sourcePrimitive) a = (a ^ 3)⁻¹ := by
  subst ha
  exact ⟨sourcePrimitive_peak N, sourcePrimitive_derivative_peak N,
    sourcePrimitive_second_derivative_peak N⟩

/-! ### A smooth exceptional hyperplane: the witness for Theorem 11.1's scope -/

theorem gradientFunctional_add_smul {n : ℕ} (x a : Vec n) (c : ℝ) :
    gradientFunctional (x + c • a) = gradientFunctional x + c • gradientFunctional a := by
  ext v
  simp only [gradientFunctional_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  change (x + c • a) ⬝ᵥ v = x ⬝ᵥ v + c * (a ⬝ᵥ v)
  rw [add_dotProduct, smul_dotProduct, smul_eq_mul]

/-- Items `C/11_U/prose/006` (`companion/chapters/11_U.tex:51-54`) and `C/11_U/prose/024`
(lines 151-152), first part. The objective $F(u,v)=\frac12(\|u\|^2+v^2)+r(v)$ ($n=m+2$, $r$ of
(11.18)) satisfies every hypothesis of Theorem 11.1 with $a=e_v$, $b=0$, $P=\{v=0\}$, $x_*=0$,
$\Omega=\mathbb R^n$, $\mu=1$, $A=P_S$ (Lipschitz with constant $1$), and every start; yet it is
differentiable at every point, in particular on $P$ ("the hyperplane itself may include
differentiable points"), its gradient is Lipschitz on no neighborhood of any point of $P$ ("failures
of gradient-Lipschitz regularity", "smooth but not locally $C^{1,1}$ points"), and its normal
second derivative at $(u,a_j)$ is $1+a_j^{-3}\to\infty$ ("no uniform bound on the full
gradient-Lipschitz constants as the hyperplane is approached is required"). Finally, the
hypotheses of Theorem 11.2 fail for it for every vector $a'$, every set $E$ and every open
$\Omega\ni0$
(every point of $\Sigma\cap\Omega$ would have to be a nondifferentiability point while $F$ is
differentiable everywhere, and $F$ is not locally $C^{1,1}$ near $0$): Theorem 11.1 is not a
literal specialization of Theorem 11.2. The actual kinks are `spike_hypotheses` (last
conjunct). -/
theorem smooth_hyperplane_witness (m : ℕ) (F : Vec (m + 2) → ℝ)
    (hF_def : ∀ (u : Vec (m + 1)) (v : ℝ),
      F (Fin.cons v u) = (1 / 2) * (sqNorm u + v ^ 2) + NormalSpike.sourcePrimitive v) :
    (ConvexOn ℝ univ F ∧ (∀ z, F 0 ≤ F z) ∧ (∀ z, F z = F 0 → z = 0) ∧
      dot (NormalSpike.normal m) 0 = 0 ∧ (∀ c, IsCompact {x | F x ≤ c}) ∧
      EuclideanStrongConvexOn univ 1 F ∧
      (∀ x, ∀ g ∈ ConvexSubdifferential.subdifferential F x,
        tangentProjection (NormalSpike.normal m) g = tangentProjection (NormalSpike.normal m) x) ∧
      LipschitzWith 1 (tangentProjection (NormalSpike.normal m)) ∧
      CenteredSmoothSublinear.LocallyC11On (univ \ {x | dot (NormalSpike.normal m) x = 0}) F) ∧
    (∀ x, DifferentiableAt ℝ F x) ∧
    (∀ p, dot (NormalSpike.normal m) p = 0 → ∀ W ∈ 𝓝 p, ∀ C : ℝ≥0,
      ¬ LipschitzOnWith C (fderiv ℝ F) W) ∧
    (∀ (u : Vec (m + 1)) (N : ℕ),
      HasDerivAt (fun t : ℝ => fderiv ℝ F (Fin.cons t u) (NormalSpike.normal m))
        (1 + (NormalSpike.scale N ^ 3)⁻¹) (NormalSpike.scale N)) ∧
    Tendsto (fun N : ℕ => 1 + (NormalSpike.scale N ^ 3)⁻¹) atTop atTop ∧
    (∀ (a' : Vec (m + 2)) (E : Set ℝ) (Ω : Set (Vec (m + 2))), IsOpen Ω → (0 : Vec (m + 2)) ∈ Ω →
      ¬ ((∀ p ∈ Ω, dot a' p ∈ E → ¬ DifferentiableAt ℝ F p) ∧
        CenteredSmoothSublinear.LocallyC11On (Ω \ {x | dot a' x ∈ E}) F)) := by
  set a := NormalSpike.normal m with ha_def
  have ha : sqNorm a = 1 := NormalSpike.normal_unit m
  have haa : dot a a = 1 := by simpa only [dot, sqNorm, pow_two] using ha
  have hFe : F = fun x => NormalSpike.quadratic x + NormalSpike.sourcePrimitive (dot a x) := by
    funext x
    rw [← Fin.cons_self_tail x, hF_def, NormalSpike.quadratic, sample_dot, sample_sqNorm]
    ring
  have hr0 : NormalSpike.sourcePrimitive 0 = 0 := by simp [NormalSpike.sourcePrimitive]
  have hrnn (v : ℝ) : 0 ≤ NormalSpike.sourcePrimitive v := by
    rw [← NormalSpike.seriesPrimitive_eq_source]; exact NormalSpike.seriesPrimitive_nonneg v
  have hpen : ConvexOn ℝ univ (fun x : Vec (m + 2) => NormalSpike.sourcePrimitive (dot a x)) := by
    simpa only [normalCoordinate, sub_zero] using
      convex_normal_composite NormalSpike.sourcePrimitive_convex a 0
  have hconv : ConvexOn ℝ univ F := by rw [hFe]; exact NormalSpike.quadratic_convex.add hpen
  have hstrong : EuclideanStrongConvexOn univ 1 F := by
    unfold EuclideanStrongConvexOn
    convert hpen using 1
    ext x
    simp only [hFe, NormalSpike.quadratic]
    ring
  have hlow (x : Vec (m + 2)) : (1 / 2) * sqNorm x ≤ F x := by
    simp only [hFe, NormalSpike.quadratic]; linarith [hrnn (dot a x)]
  have hF0 : F 0 = 0 := by simp [hFe, NormalSpike.quadratic, sqNorm, dot, hr0]
  have hmin : ∀ z, F 0 ≤ F z := fun z => by
    rw [hF0]; exact (mul_nonneg (by norm_num) (sqNorm_nonneg z)).trans (hlow z)
  have huniq : ∀ z, F z = F 0 → z = 0 := by
    intro z hz
    have hb := hlow z
    rw [hz, hF0] at hb
    exact (CertificateGeometry.sqNorm_eq_zero_iff z).mp
      (le_antisymm (by nlinarith [sqNorm_nonneg z]) (sqNorm_nonneg z))
  have hgrad (x : Vec (m + 2)) : HasFDerivAt F
      (gradientFunctional (x + NormalSpike.seriesMass (dot a x) • a)) x := by
    have hl : HasFDerivAt (dot a) (gradientFunctional a) x := by
      convert (gradientFunctional a).hasFDerivAt (x := x) using 1
      exact funext (fun y => (gradientFunctional_apply a y).symm)
    have h := (NormalSpike.quadratic_hasFDerivAt x).add
      ((NormalSpike.sourcePrimitive_hasDerivAt (dot a x)).comp_hasFDerivAt x hl)
    rw [hFe, gradientFunctional_add_smul]
    convert h using 1
  have hdiff : ∀ x, DifferentiableAt ℝ F x := fun x => (hgrad x).differentiableAt
  have hrep : ∀ y ∈ (univ : Set (Vec (m + 2))),
      F y = NormalSpike.quadratic y + NormalSpike.sourcePrimitive (normalCoordinate a 0 y) := by
    intro y _
    simp only [hFe, normalCoordinate, sub_zero]
  have hsm : CenteredSmoothSublinear.LocallyC11On (univ \ {x | dot a x = 0}) F := by
    rw [diff_plane_eq_regularRegion]
    exact composite_locallyC11_off_interface isOpen_univ NormalSpike.quadratic_locallyC11 a 0
      isClosed_singleton NormalSpike.sourcePrimitive_locallyC11_off_zero hrep
  have hA : ∀ x, ∀ g ∈ ConvexSubdifferential.subdifferential F x,
      tangentProjection a g = tangentProjection a x := fun x g hg =>
    composite_support_projection NormalSpike.sourcePrimitive_convex isOpen_univ ha 0 hrep
      (mem_univ x) hg (NormalSpike.quadratic_hasFDerivAt x)
  -- the normal derivative along the normal line through a point of `P`
  have hfd (p : Vec (m + 2)) (hp : dot a p = 0) (t : ℝ) :
      fderiv ℝ F (p + t • a) a = t + NormalSpike.seriesMass t := by
    have hdt : dot a (p + t • a) = t := by
      rw [NormalSpike.dot_add_smul, hp, haa, mul_one, zero_add]
    rw [(hgrad _).fderiv, gradientFunctional_apply, hdt]
    change (p + t • a + NormalSpike.seriesMass t • a) ⬝ᵥ a = _
    rw [add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct]
    change dot p a + t * dot a a + NormalSpike.seriesMass t * dot a a = _
    rw [haa, show dot p a = dot a p from dotProduct_comm _ _, hp]
    ring
  have hphid (N : ℕ) : HasDerivAt (fun t : ℝ => t + NormalSpike.seriesMass t)
      (1 + (NormalSpike.scale N ^ 3)⁻¹) (NormalSpike.scale N) := by
    rw [← NormalSpike.density_peak]
    exact (hasDerivAt_id _).add (NormalSpike.seriesMass_hasDerivAt_pos (NormalSpike.scale_pos N))
  have hunb : Tendsto (fun N : ℕ => 1 + (NormalSpike.scale N ^ 3)⁻¹) atTop atTop := by
    apply tendsto_atTop_add_const_left
    apply tendsto_inv_nhdsGT_zero.comp
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun N => pow_pos (NormalSpike.scale_pos N) 3⟩
    simpa only [zero_pow (by norm_num : 3 ≠ 0)] using NormalSpike.scale_tendsto_zero.pow 3
  have hnotlip : ∀ p, dot a p = 0 → ∀ W ∈ 𝓝 p, ∀ C : ℝ≥0, ¬ LipschitzOnWith C (fderiv ℝ F) W := by
    intro p hp W hW C hC
    let T : Set ℝ := {t | p + t • a ∈ W}
    have hT : T ∈ 𝓝 (0 : ℝ) := by
      have hc : Continuous (fun t : ℝ => p + t • a) := by fun_prop
      exact hc.continuousAt.preimage_mem_nhds (by simpa using hW)
    have hφL : LipschitzOnWith C (fun t : ℝ => t + NormalSpike.seriesMass t) T := by
      apply LipschitzOnWith.of_dist_le_mul
      intro t ht t' ht'
      rw [← hfd p hp t, ← hfd p hp t', Real.dist_eq, ← ContinuousLinearMap.sub_apply]
      have hn := (fderiv ℝ F (p + t • a) - fderiv ℝ F (p + t' • a)).le_opNorm a
      have hnorm_a : ‖a‖ = 1 := by
        rw [ha_def, NormalSpike.normal, Pi.norm_single, norm_one]
      rw [hnorm_a, mul_one] at hn
      have hl := hC.norm_sub_le ht ht'
      have hd : ‖(p + t • a) - (p + t' • a)‖ = dist t t' := by
        rw [show (p + t • a) - (p + t' • a) = (t - t') • a by module, norm_smul, hnorm_a,
          mul_one, Real.norm_eq_abs, Real.dist_eq]
      rw [hd] at hl
      exact (Real.norm_eq_abs _ ▸ hn).trans hl
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hT
    have hsmall : ∀ᶠ N in atTop, NormalSpike.scale N < ε / 2 :=
      NormalSpike.scale_tendsto_zero.eventually (gt_mem_nhds (half_pos hε))
    have hbig := hunb.eventually (eventually_gt_atTop (C : ℝ))
    obtain ⟨N, hN1, hN2⟩ := (hsmall.and hbig).exists
    have hTN : T ∈ 𝓝 (NormalSpike.scale N) := by
      apply Filter.mem_of_superset (Metric.ball_mem_nhds _ (half_pos hε))
      intro t ht
      apply hball
      rw [Metric.mem_ball, Real.dist_eq] at ht ⊢
      rw [sub_zero]
      have := NormalSpike.scale_pos N
      rw [abs_lt] at ht ⊢
      constructor <;> linarith [ht.1, ht.2]
    have hle := (hphid N).le_of_lipschitzOn hTN hφL
    have hsN := NormalSpike.scale_pos N
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)] at hle
    linarith
  refine ⟨⟨hconv, hmin, huniq, by simp [dot], fun c => Localization.sublevel_compact hconv 0 hmin
      huniq c, hstrong, hA, NormalSpike.normal_tangent_lipschitz m, hsm⟩, hdiff, hnotlip,
    fun u N => ?_, hunb, fun a' E Ω hΩ h0 ⟨hsing, hsmooth⟩ => ?_⟩
  · have hu : (fun t : ℝ => fderiv ℝ F (Fin.cons t u) a) =
        fun t : ℝ => t + NormalSpike.seriesMass t := by
      funext t
      have hp : dot a (Fin.cons 0 u : Vec (m + 2)) = 0 := sample_dot m u 0
      have he : (Fin.cons t u : Vec (m + 2)) = Fin.cons 0 u + t • a := by
        ext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [ha_def, NormalSpike.normal]
        · simp [ha_def, NormalSpike.normal, Pi.single_apply, Fin.succ_ne_zero]
      rw [he, hfd _ hp t]
    rw [hu]
    exact hphid N
  · have hempty : Ω \ {x | dot a' x ∈ E} = Ω := by
      ext x
      simp only [mem_diff, mem_setOf_eq, and_iff_left_iff_imp]
      intro hx hE
      exact hsing x hx hE (hdiff x)
    rw [hempty] at hsmooth
    obtain ⟨C, W, hW, hLipW⟩ := hsmooth.2 h0
    rw [nhdsWithin_eq_nhds.mpr (hΩ.mem_nhds h0)] at hW
    exact hnotlip 0 (by simp [dot]) W hW C hLipW

/-! ### Section 11.7.2: the coupled example

The objective is a variable `F : Vec (m + 2) → ℝ` with the defining equation
$F(u,v)=\frac12(\|u\|^2+v^2)+|(1+c^Tu)v|+r(v)$, for $c\in\mathbb R^{m+1}$ with $\|c\|<1$
(Euclidean: `Real.sqrt (sqNorm c) < 1`). It is the library's `printedVariableObjective m c`. -/

theorem dot_cons_zero {m : ℕ} (c : Vec (m + 1)) (x : Vec (m + 2)) :
    dot (Fin.cons 0 c : Vec (m + 2)) x = dot c (Fin.tail x) := by
  simp only [dot, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, zero_mul, zero_add, Fin.tail]

/-- Item `C/11_U/disp/033` (`companion/chapters/11_U.tex:458-460`): "For a fixed vector
$c\in\mathbb R^{n-1}$ with $\|c\|<1$, another example is
$F(u,v)=\frac12(\|u\|^2+v^2)+|(1+c^Tu)v|+r(v)$." The function so defined is the library's
`printedVariableObjective m c` ($n=m+2$). -/
theorem variable_objective_eq (m : ℕ) (c : Vec (m + 1)) (F : Vec (m + 2) → ℝ)
    (hF_def : ∀ (u : Vec (m + 1)) (v : ℝ),
      F (Fin.cons v u) = (1 / 2) * (sqNorm u + v ^ 2) + |(1 + dot c u) * v| +
        NormalSpike.sourcePrimitive v) :
    F = NormalSpike.printedVariableObjective m c := by
  funext x
  rw [← Fin.cons_self_tail x, hF_def, NormalSpike.printed_variable_formula]

/-- Item `C/11_U/disp/034` (`companion/chapters/11_U.tex:460-463`), with item `prose/060`
(line 463): "The two quadratic functions before adding $r$ have Hessians
$\begin{pmatrix}I&c\\c^T&1\end{pmatrix}$, $\begin{pmatrix}I&-c\\-c^T&1\end{pmatrix}$, both bounded
below by $(1-\|c\|)I$." For $\sigma=\pm1$ and $q_\sigma(u,v)=\frac12(\|u\|^2+v^2)+\sigma(1+c^Tu)v$
(so that $F=\max(q_+,q_-)+r$): $q_\sigma$ is $C^3$ and its Hessian matrix $B$ at every point has
the stated blocks (written in the coordinate order $(v,u)$: $B_{vv}=1$, $B_{vu_j}=B_{u_jv}=\sigma
c_j$, $B_{u_iu_j}=\delta_{ij}$), and $w^TBw\ge(1-\|c\|)\|w\|^2$. Library:
`printed_variable_quadratic_hessian_blocks`, `variableQuadraticBranch_hessian_lower`. -/
theorem variable_hessians (m : ℕ) (c : Vec (m + 1)) (_hc : Real.sqrt (sqNorm c) < 1)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (q : Vec (m + 2) → ℝ)
    (hq : ∀ (u : Vec (m + 1)) (v : ℝ),
      q (Fin.cons v u) = (1 / 2) * (sqNorm u + v ^ 2) + σ * ((1 + dot c u) * v))
    (x : Vec (m + 2)) (B : Mat (m + 2)) (hB : B = RadialHessian.matrix q x) :
    ContDiff ℝ 3 q ∧ B 0 0 = 1 ∧ (∀ j : Fin (m + 1), B 0 j.succ = σ * c j) ∧
      (∀ i : Fin (m + 1), B i.succ 0 = σ * c i) ∧
      (∀ i j : Fin (m + 1), B i.succ j.succ = if i = j then 1 else 0) ∧
      ∀ w : Vec (m + 2), (1 - Real.sqrt (sqNorm c)) * sqNorm w ≤ dot w (B *ᵥ w) := by
  have hqe : q = NormalSpike.variableQuadraticBranch (NormalSpike.normal m) (Fin.cons 0 c) σ := by
    funext y
    rw [← Fin.cons_self_tail y, hq, NormalSpike.variableQuadraticBranch, NormalSpike.quadratic,
      sample_sqNorm, sample_dot, dot_cons_zero, Fin.tail_cons]
    ring
  subst hqe hB
  obtain ⟨h1, h2, h3, h4⟩ := NormalSpike.printed_variable_quadratic_hessian_blocks m c x σ
  have hσ1 : |σ| ≤ 1 := by rcases hσ with rfl | rfl <;> simp
  refine ⟨NormalSpike.variableQuadraticBranch_contDiff _ _ _, h1, h2, h3, h4, fun w => ?_⟩
  have h := NormalSpike.variableQuadraticBranch_hessian_lower (NormalSpike.normal_unit m)
    (NormalSpike.extended_coupling_tangent m c) σ hσ1 x w
  rwa [NormalSpike.extended_coupling_sqNorm] at h

/-- Item `C/11_U/prose/061` (`companion/chapters/11_U.tex:463-464`): "Their maximum plus convex
$r(v)$ is strongly convex": $F=\max(q_+,q_-)+r(v)$ and $F$ is $(1-\|c\|)$-strongly convex, with
$1-\|c\|>0$. Library: `printed_variable_strongConvex`. -/
theorem variable_strongly_convex (m : ℕ) (c : Vec (m + 1)) (hc : Real.sqrt (sqNorm c) < 1)
    (F : Vec (m + 2) → ℝ)
    (hF_def : ∀ (u : Vec (m + 1)) (v : ℝ),
      F (Fin.cons v u) = (1 / 2) * (sqNorm u + v ^ 2) + |(1 + dot c u) * v| +
        NormalSpike.sourcePrimitive v) :
    (∀ (u : Vec (m + 1)) (v : ℝ), F (Fin.cons v u) =
        max ((1 / 2) * (sqNorm u + v ^ 2) + (1 + dot c u) * v)
          ((1 / 2) * (sqNorm u + v ^ 2) - (1 + dot c u) * v) + NormalSpike.sourcePrimitive v) ∧
      0 < 1 - Real.sqrt (sqNorm c) ∧ EuclideanStrongConvexOn univ (1 - Real.sqrt (sqNorm c)) F := by
  refine ⟨fun u v => ?_, sub_pos.mpr hc, ?_⟩
  · rw [hF_def, abs_eq_max_neg, sub_eq_add_neg, max_add_add_left]
  · rw [variable_objective_eq m c F hF_def]
    exact NormalSpike.printed_variable_strongConvex m c

/-- Item `C/11_U/prose/062` (`companion/chapters/11_U.tex:464-465`): "Since the absolute-value
term and $r$ are nonnegative, zero is the unique minimizer." Library: `variableObjective_minimum`,
`variableObjective_unique_minimum`. -/
theorem variable_unique_minimizer (m : ℕ) (c : Vec (m + 1)) (_hc : Real.sqrt (sqNorm c) < 1)
    (F : Vec (m + 2) → ℝ)
    (hF_def : ∀ (u : Vec (m + 1)) (v : ℝ),
      F (Fin.cons v u) = (1 / 2) * (sqNorm u + v ^ 2) + |(1 + dot c u) * v| +
        NormalSpike.sourcePrimitive v) :
    F 0 = 0 ∧ (∀ x, F 0 ≤ F x) ∧ (∀ x, F x = F 0 → x = 0) := by
  rw [variable_objective_eq m c F hF_def]
  exact ⟨NormalSpike.variableObjective_zero _ _, NormalSpike.variableObjective_minimum _ _,
    NormalSpike.variableObjective_unique_minimum _ _⟩

/-- Item `C/11_U/prose/063` (`companion/chapters/11_U.tex:467-470`), with display `disp/035`
(lines 468-470): "On a neighborhood with $|c^Tu|<1/2$, the only exceptional hyperplane is $v=0$,
and the tangential gradient is $A(u,v)=u+c|v|$, which is Lipschitz across that hyperplane." On the
open neighborhood $W=\{(u,v):|c^Tu|<1/2\}$ of $0$: $F$ is differentiable exactly where $v\neq0$,
every subgradient $g$ at $(u,v)$ has $P_Sg=(u+|v|c,0)$, and $A$ is Lipschitz on $\mathbb R^n$.
Library: `variableSpikeGeometry`, `variableTangent_lipschitz`, `printed_variable_tangent_formula`. -/
theorem variable_region_geometry (m : ℕ) (c : Vec (m + 1)) (hc : Real.sqrt (sqNorm c) < 1)
    (F : Vec (m + 2) → ℝ)
    (hF_def : ∀ (u : Vec (m + 1)) (v : ℝ),
      F (Fin.cons v u) = (1 / 2) * (sqNorm u + v ^ 2) + |(1 + dot c u) * v| +
        NormalSpike.sourcePrimitive v)
    (W : Set (Vec (m + 2))) (hW : W = {x | |dot c (Fin.tail x)| < 1 / 2})
    (A : Vec (m + 2) → Vec (m + 2)) (hA : ∀ (u : Vec (m + 1)) (v : ℝ),
      A (Fin.cons v u) = Fin.cons 0 (u + |v| • c)) :
    IsOpen W ∧ (0 : Vec (m + 2)) ∈ W ∧ Convex ℝ W ∧
      (∀ x ∈ W, DifferentiableAt ℝ F x ↔ x 0 ≠ 0) ∧
      (∀ x ∈ W, ∀ g ∈ ConvexSubdifferential.subdifferential F x,
        tangentProjection (NormalSpike.normal m) g = A x) ∧
      ∃ L : ℝ≥0, LipschitzWith L A := by
  have hFe := variable_objective_eq m c F hF_def
  have hAe : A = NormalSpike.variableTangent (NormalSpike.normal m) (Fin.cons 0 c) := by
    funext y
    rw [← Fin.cons_self_tail y, hA, NormalSpike.printed_variable_tangent_formula]
  have hWe : W = NormalSpike.variableRegion (Fin.cons 0 c) := by
    rw [hW]
    ext x
    simp only [NormalSpike.variableRegion, mem_setOf_eq, dot_cons_zero]
  subst hFe hAe hWe
  obtain ⟨-, -, -, -, -, hdiff, htan, -, -⟩ := NormalSpike.variableSpikeGeometry m c hc
  exact ⟨NormalSpike.variableRegion_open _, NormalSpike.variableRegion_zero _,
    NormalSpike.variableRegion_convex _, hdiff, fun x hx g hg => htan x hx g hg,
    NormalSpike.variableTangent_lipschitz _ _⟩

/-- Item `C/11_U/prose/064` (`companion/chapters/11_U.tex:470`): "Theorem 11.1 gives an
objective-dependent local full-BFGS convergence basin for every $\|c\|<1$, including $c=0$."
Proved from the local form of Theorem 11.1 (`hyperplane_local_basin`) on the neighborhood $W$ of
`variable_region_geometry`: some $\varepsilon>0$, depending only on the objective, gives
$F(x_k)\to0$ and $x_k\to0$ for every run with $F(x_0)<\varepsilon$. Library:
`printed_variable_local_fullBFGS`. -/
theorem variable_local_basin (m : ℕ) (c : Vec (m + 1)) (hc : Real.sqrt (sqNorm c) < 1)
    (F : Vec (m + 2) → ℝ)
    (hF_def : ∀ (u : Vec (m + 1)) (v : ℝ),
      F (Fin.cons v u) = (1 / 2) * (sqNorm u + v ^ 2) + |(1 + dot c u) * v| +
        NormalSpike.sourcePrimitive v) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ R : AdmissibleBFGSRun (m + 2) F, F (R.x 0) < ε →
      Tendsto (fun k => F (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0) := by
  have hFe := variable_objective_eq m c F hF_def
  subst hFe
  set a := NormalSpike.normal m
  set chat : Vec (m + 2) := Fin.cons 0 c
  have hca : dot a chat = 0 := NormalSpike.extended_coupling_tangent m c
  have hchat : Real.sqrt (sqNorm chat) < 1 := by rwa [NormalSpike.extended_coupling_sqNorm]
  have hconv := NormalSpike.variableObjective_convex (NormalSpike.normal_unit m) hca
    (Real.sqrt_nonneg _) (Real.sq_sqrt (sqNorm_nonneg _)) hchat.le
  have hstrong := NormalSpike.variableObjective_strongConvex (NormalSpike.normal_unit m) hca
    (Real.sqrt_nonneg _) (Real.sq_sqrt (sqNorm_nonneg _))
  obtain ⟨L, hL⟩ := NormalSpike.variableTangent_lipschitz a chat
  have hsm : CenteredSmoothSublinear.LocallyC11On
      (NormalSpike.variableRegion chat \ {x | dot a x = 0}) (NormalSpike.variableObjective a chat) := by
    rw [diff_plane_eq_regularRegion]
    exact NormalSpike.variableObjective_regular_locallyC11 a chat
  obtain ⟨ε, hε, h⟩ := hyperplane_local_basin (NormalSpike.variableObjective a chat) hconv a
    (NormalSpike.normal_unit m) 0 _ rfl 0 (NormalSpike.variableObjective_minimum a chat)
    (NormalSpike.variableObjective_unique_minimum a chat) (by simp [dot])
    (NormalSpike.variableRegion chat) (NormalSpike.variableRegion_open chat)
    (NormalSpike.variableRegion_convex chat) (NormalSpike.variableRegion_zero chat)
    (1 - Real.sqrt (sqNorm chat)) (sub_pos.mpr hchat)
    (hstrong.subset (subset_univ _) (NormalSpike.variableRegion_convex chat))
    (NormalSpike.variableTangent a chat)
    (fun x hx g hg => NormalSpike.variable_support_tangent (NormalSpike.normal_unit m) hca
      (NormalSpike.variableRegion_positive hx) hg) L hL.lipschitzOnWith hsm
  refine ⟨ε, hε, fun R hR => ?_⟩
  have h0 := NormalSpike.variableObjective_zero a chat
  have hR' : NormalSpike.variableObjective a chat (R.x 0) <
      NormalSpike.variableObjective a chat 0 + ε := by
    rw [h0, zero_add]; exact hR
  have hc := h R hR'
  rw [h0] at hc
  exact hc

/-- Item `C/11_U/prose/065` (`companion/chapters/11_U.tex:472`), first sentence: "If $c\ne0$, the
normal-gradient jump magnitude $2(1+c^Tu)$ varies with $u$ on this neighborhood." At $(u,0)$ with
$|c^Tu|<1/2$ the one-sided derivatives of $v\mapsto F(u,v)$ at $0$ are $\pm(1+c^Tu)$, so the jump
is $2(1+c^Tu)$; for $c\neq0$ two points of the neighborhood have different jumps. -/
theorem variable_jump (m : ℕ) (c : Vec (m + 1)) (_hc : Real.sqrt (sqNorm c) < 1)
    (F : Vec (m + 2) → ℝ)
    (hF_def : ∀ (u : Vec (m + 1)) (v : ℝ),
      F (Fin.cons v u) = (1 / 2) * (sqNorm u + v ^ 2) + |(1 + dot c u) * v| +
        NormalSpike.sourcePrimitive v) :
    (∀ u : Vec (m + 1), |dot c u| < 1 / 2 →
      HasDerivWithinAt (fun v : ℝ => F (Fin.cons v u)) (1 + dot c u) (Ici 0) 0 ∧
        HasDerivWithinAt (fun v : ℝ => F (Fin.cons v u)) (-(1 + dot c u)) (Iic 0) 0 ∧
        (1 + dot c u) - (-(1 + dot c u)) = 2 * (1 + dot c u)) ∧
      (c ≠ 0 → ∃ u₁ u₂ : Vec (m + 1), |dot c u₁| < 1 / 2 ∧ |dot c u₂| < 1 / 2 ∧
        2 * (1 + dot c u₁) ≠ 2 * (1 + dot c u₂)) := by
  have hr0 : deriv NormalSpike.sourcePrimitive 0 = 0 := by
    rw [(NormalSpike.sourcePrimitive_hasDerivAt 0).deriv]
    exact NormalSpike.seriesMass_nonpos le_rfl
  refine ⟨fun u hu => ?_, fun hc0 => ?_⟩
  · have hw : 0 < 1 + dot c u := by have := (abs_lt.mp hu).1; linarith
    have hr := NormalSpike.sourcePrimitive_hasDerivAt 0
    rw [show NormalSpike.seriesMass 0 = 0 from NormalSpike.seriesMass_nonpos le_rfl] at hr
    have hquad (s : ℝ) : HasDerivAt (fun v : ℝ => (1 / 2) * (sqNorm u + v ^ 2) + s * v) s 0 := by
      have h := ((hasDerivAt_pow 2 (0 : ℝ)).const_add (sqNorm u)).const_mul (1 / 2) |>.add
        ((hasDerivAt_id (0 : ℝ)).const_mul s)
      convert h using 1
      simp
    refine ⟨?_, ?_, by ring⟩
    · have h := ((hquad (1 + dot c u)).add hr).hasDerivWithinAt (s := Ici 0)
      rw [add_zero] at h
      apply h.congr
      · intro v hv
        rw [hF_def, abs_of_nonneg (mul_nonneg hw.le hv)]
      · rw [hF_def]
        simp
    · have h := ((hquad (-(1 + dot c u))).add hr).hasDerivWithinAt (s := Iic 0)
      rw [add_zero] at h
      apply h.congr
      · intro v hv
        rw [hF_def, abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hw.le hv)]
        ring
      · rw [hF_def]
        simp
  · have hpos : 0 < sqNorm c := lt_of_le_of_ne (sqNorm_nonneg _)
      (fun h => hc0 ((CertificateGeometry.sqNorm_eq_zero_iff c).mp h.symm))
    refine ⟨0, (1 / (4 * sqNorm c)) • c, ?_, ?_, ?_⟩
    · simp [dot]
    · rw [dot_smul_right, show dot c c = sqNorm c by simp only [dot, sqNorm, pow_two]]
      rw [show 1 / (4 * sqNorm c) * sqNorm c = 1 / 4 by field_simp; ring]
      norm_num [abs_of_pos]
    · rw [dot_smul_right, show dot c c = sqNorm c by simp only [dot, sqNorm, pow_two]]
      rw [show 1 / (4 * sqNorm c) * sqNorm c = 1 / 4 by field_simp; ring]
      simp [dot]

/-- Item `C/11_U/prose/066` (`companion/chapters/11_U.tex:472`), second sentence: "More
precisely, on no open neighborhood of zero can this objective equal $S(u,v)+h(v)$ with $S$
differentiable and $h$ an arbitrary scalar function" (for $c\neq0$). Library:
`printed_variable_no_local_smooth_scalar_split`, proved by the central difference of the next
sentence (`variable_central_difference`). -/
theorem variable_nonsplitting (m : ℕ) (c : Vec (m + 1)) (_hc : Real.sqrt (sqNorm c) < 1)
    (hc0 : c ≠ 0) (F : Vec (m + 2) → ℝ)
    (hF_def : ∀ (u : Vec (m + 1)) (v : ℝ),
      F (Fin.cons v u) = (1 / 2) * (sqNorm u + v ^ 2) + |(1 + dot c u) * v| +
        NormalSpike.sourcePrimitive v) :
    ∀ U : Set (Vec (m + 2)), IsOpen U → (0 : Vec (m + 2)) ∈ U →
      ∀ (S : Vec (m + 2) → ℝ) (h : ℝ → ℝ), DifferentiableOn ℝ S U →
        ¬ ∀ (u : Vec (m + 1)) (v : ℝ), (Fin.cons v u : Vec (m + 2)) ∈ U →
          F (Fin.cons v u) = S (Fin.cons v u) + h v := by
  intro U hU h0 S h hS hrep
  rw [variable_objective_eq m c F hF_def] at hrep
  apply NormalSpike.printed_variable_no_local_smooth_scalar_split m c hc0 hU h0 S h hS
  intro x hx
  have hx' := hrep (Fin.tail x) (x 0) (by rwa [Fin.cons_self_tail])
  rwa [Fin.cons_self_tail] at hx'

/-- Item `C/11_U/prose/069` (`companion/chapters/11_U.tex:474-477`), with display `disp/036`:
"When $c=0$, the objective has the explicit global decomposition
$S(u,v)=\frac12(\|u\|^2+v^2)$, $h(v)=|v|+r(v)$, with $S$ smooth." Library:
`OriginalClaimInterpretation.zero_coupling_split`, `quadratic_smooth`. -/
theorem variable_zero_split (m : ℕ) (F : Vec (m + 2) → ℝ)
    (hF_def : ∀ (u : Vec (m + 1)) (v : ℝ),
      F (Fin.cons v u) = (1 / 2) * (sqNorm u + v ^ 2) + |(1 + dot (0 : Vec (m + 1)) u) * v| +
        NormalSpike.sourcePrimitive v)
    (S : Vec (m + 2) → ℝ) (hS : ∀ (u : Vec (m + 1)) (v : ℝ), S (Fin.cons v u) = (1 / 2) * (sqNorm u + v ^ 2))
    (h : ℝ → ℝ) (hh : ∀ v, h v = |v| + NormalSpike.sourcePrimitive v) :
    (∀ (u : Vec (m + 1)) (v : ℝ), F (Fin.cons v u) = S (Fin.cons v u) + h v) ∧ ContDiff ℝ ⊤ S := by
  have hSe : S = NormalSpike.quadratic := by
    funext x
    rw [← Fin.cons_self_tail x, hS, NormalSpike.quadratic, sample_sqNorm]
    ring
  refine ⟨fun u v => ?_, hSe ▸ OriginalClaimInterpretation.quadratic_smooth⟩
  rw [hF_def, hS, hh]
  simp [dot]
  ring

/-- Item `C/11_U/prose/071` (`companion/chapters/11_U.tex:478`): "The spike argument still makes
(RS) fail in every neighborhood of zero for all $\|c\|<1$, including the zero case." Library:
`printed_variable_no_radial_secant`. -/
theorem variable_rs_fails (m : ℕ) (c : Vec (m + 1)) (hc : Real.sqrt (sqNorm c) < 1)
    (F : Vec (m + 2) → ℝ)
    (hF_def : ∀ (u : Vec (m + 1)) (v : ℝ),
      F (Fin.cons v u) = (1 / 2) * (sqNorm u + v ^ 2) + |(1 + dot c u) * v| +
        NormalSpike.sourcePrimitive v) :
    ∀ W ∈ 𝓝 (0 : Vec (m + 2)), ¬ RS F 0 W := by
  intro W hW hRS
  rw [variable_objective_eq m c F hF_def, RS_iff_library] at hRS
  exact NormalSpike.printed_variable_no_radial_secant m c hc hW hRS

/-! ### Relation to earlier work -/

/-- Item `C/11_U/prose/075` (`companion/chapters/11_U.tex:490`): "The smooth-region estimates use
classical cocoercivity; see the open-domain Baillon--Haddad theorem~\cite{WW}, Theorem~2.5." The
cocoercivity that the proof of display (11.13) uses (display `disp/015`): for a convex
$\psi:\mathbb R^n\to\mathbb R$ that is locally $C^{1,1}$ on an open set $U$ and a compact
$K\subset U$, some $L>0$ gives $\|\nabla\psi(y)-\nabla\psi(x)\|^2\le
L(\nabla\psi(y)-\nabla\psi(x))^T(y-x)$ for $x,y\in K$. Proved in the library from the descent
lemma on small balls (`exists_cocoercivity_constant_on_smooth_compact`); the optimal-constant
result of~\cite{WW} (Theorem 2.5, for functions convex only on an open convex set) is not needed
and not formalized. -/
theorem cocoercivity_on_smooth_compact {n : ℕ} {ψ : Vec n → ℝ} {U K : Set (Vec n)}
    (hU : IsOpen U) (hconvex : ConvexOn ℝ univ ψ)
    (hsmooth : CenteredSmoothSublinear.LocallyC11On U ψ) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ L : ℝ, 0 < L ∧ ∀ x ∈ K, ∀ y ∈ K, ∀ g h : Vec n, HasFDerivAt ψ (gradientFunctional g) x →
      HasFDerivAt ψ (gradientFunctional h) y → sqNorm (h - g) ≤ L * dot (h - g) (y - x) := by
  obtain ⟨L, hL, hc⟩ := exists_cocoercivity_constant_on_smooth_compact hU hconvex hsmooth hK hKU
  refine ⟨L, hL, fun x hx y hy g h hg hh => ?_⟩
  have h' := hc x hx y hy
  rwa [coordinateGradient_eq hconvex hg, coordinateGradient_eq hconvex hh] at h'

/-! ### Non-vacuity

Admissible runs exist on the objective (11.20) from every point off the hyperplane $v=0$, for
every $H_0\succ0$ and all $0<c_1<c_2<1$ (`spike_run_exists`, from the general existence theorem
`AdmissibleRunExistence.exists_admissible_run`). The examples below show that the standing
assumptions of the theorems of this module hold together for this objective and such a run. -/

/-- Admissible runs exist on the objective (11.20) from every $x_0$ with $v_0\neq0$, for every
$H_0\succ0$ and all $0<c_1<c_2<1$. -/
theorem spike_run_exists (m : ℕ) (F : Vec (m + 2) → ℝ)
    (hF_def : ∀ (u : Vec (m + 1)) (v : ℝ),
      F (Fin.cons v u) = (1 / 2) * sqNorm u + (1 / 2) * v ^ 2 + |v| + NormalSpike.sourcePrimitive v)
    (x0 : Vec (m + 2)) (hx0 : x0 0 ≠ 0) (H0 : Mat (m + 2)) (hH0 : H0.PosDef)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₁₂ : c₁ < c₂) (hc₂ : c₂ < 1) :
    ∃ R : AdmissibleBFGSRun (m + 2) F, R.x 0 = x0 ∧ R.H 0 = H0 ∧ R.c₁ = c₁ ∧ R.c₂ = c₂ := by
  have hFe := spike_objective_eq m F hF_def
  subst hFe
  set a := NormalSpike.normal m
  have hdiff (y : Vec (m + 2)) : DifferentiableAt ℝ (NormalSpike.objective a) y ↔ y 0 ≠ 0 := by
    rw [NormalSpike.objective_differentiable_iff _ (NormalSpike.normal_unit m),
      NormalSpike.normal_coordinate]
  have hbdd : BddBelow (range (NormalSpike.objective a)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨y, rfl⟩
    have h := NormalSpike.objective_minimum a y
    rwa [NormalSpike.objective_zero] at h
  have hline : ∀ x p : Vec (m + 2), DifferentiableAt ℝ (NormalSpike.objective a) x → p ≠ 0 →
      {t : ℝ | ¬ DifferentiableAt ℝ (NormalSpike.objective a) (x + t • p)}.Countable := by
    intro x p hx _
    rw [hdiff] at hx
    apply (Set.subsingleton_of_forall_eq (-(x 0) / p 0) ?_).countable
    intro t ht
    rw [mem_setOf_eq, hdiff, not_not] at ht
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ht
    have hp0 : p 0 ≠ 0 := by
      intro hp
      rw [hp, mul_zero, add_zero] at ht
      exact hx ht
    field_simp
    linarith
  have hstat : ∀ y g, HasFDerivAt (NormalSpike.objective a) (gradientFunctional g) y → g ≠ 0 := by
    intro y g hg hg0
    rw [hg0] at hg
    have hy := global_minimum_of_zero_gradient (NormalSpike.objective_convex a) hg
    have hy0 : y = 0 := NormalSpike.objective_unique_minimum a y
      (le_antisymm (hy 0) (NormalSpike.objective_minimum a y))
    have hd := (hdiff y).mp hg.differentiableAt
    rw [hy0] at hd
    exact hd rfl
  obtain ⟨R, h0, -, hH, h1, h2⟩ := AdmissibleRunExistence.exists_admissible_run
    (NormalSpike.objective_convex a) hbdd hline hstat
    (hasFDerivAt_coordinateGradient ((hdiff x0).mpr hx0)) hH0 hc₁ hc₁₂ hc₂
  exact ⟨R, h0, hH, h1, h2⟩

/-- The objective (11.20) in dimension $2$, with its defining equation. -/
theorem spike_objective_def2 :
    ∀ (u : Vec 1) (v : ℝ), NormalSpike.objective (NormalSpike.normal 0) (Fin.cons v u) =
      (1 / 2) * sqNorm u + (1 / 2) * v ^ 2 + |v| + NormalSpike.sourcePrimitive v :=
  fun u v => NormalSpike.printed_objective_split 0 v u

/-- A run on (11.20) in dimension $2$ from $x_0=e_v$, with $H_0=I$, $c_1=1/4$, $c_2=1/2$. -/
theorem spike_run2 : ∃ R : AdmissibleBFGSRun 2 (NormalSpike.objective (NormalSpike.normal 0)),
    R.x 0 = Pi.single 0 1 := by
  obtain ⟨R, h0, -⟩ := spike_run_exists 0 _ spike_objective_def2 (Pi.single 0 1) (by simp) 1
    Matrix.PosDef.one (1 / 4) (1 / 2) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨R, h0⟩

/-- Non-vacuity of Theorem 11.1 (`one_exceptional_hyperplane`), of its consequences
`hyperplane_local_basin`, `tangential_trace_derived`, `plane_zero_optimal`, `plane_monotonicity`
and `zero_set_hyperplane_general`: the objective (11.20) ($n=2$, $a=e_v$, $b=0$, $x_*=0$,
$\Omega=\mathbb R^2$, $\mu=1$, $A=P_S$) satisfies all hypotheses, with an admissible run starting at
$x_0=e_v$. -/
example : ∃ (F : Vec 2 → ℝ) (a : Vec 2) (P : Set (Vec 2)) (x0 : Vec 2) (A : Vec 2 → Vec 2),
    ConvexOn ℝ univ F ∧ sqNorm a = 1 ∧ P = {x | dot a x = 0} ∧
      (∀ z, F 0 ≤ F z) ∧ (∀ z, F z = F 0 → z = 0) ∧ (0 : Vec 2) ∈ P ∧
      IsCompact {x | F x ≤ F x0} ∧ EuclideanStrongConvexOn univ 1 F ∧
      (∀ x ∈ (univ : Set (Vec 2)), ∀ g ∈ ConvexSubdifferential.subdifferential F x,
        tangentProjection a g = A x) ∧
      LipschitzOnWith 1 A univ ∧ CenteredSmoothSublinear.LocallyC11On (univ \ P) F ∧
      ∃ R : AdmissibleBFGSRun 2 F, R.x 0 = x0 := by
  obtain ⟨hconv, ha, hmin, huniq, hplane, hcpt, hstrong, hA, -, hLip, hsm, -⟩ :=
    spike_hypotheses 0 _ spike_objective_def2
  obtain ⟨R, hR⟩ := spike_run2
  exact ⟨_, NormalSpike.normal 0, _, Pi.single 0 1, tangentProjection (NormalSpike.normal 0),
    hconv, ha, rfl, hmin, huniq, hplane, hcpt _, hstrong, fun x _ g hg => hA x g hg,
    hLip.lipschitzOnWith, hsm, R, hR⟩

/-- Non-vacuity of Theorem 11.2 (`parallel_singular_interfaces`) and of its consequences
(`parallel_interfaces_convergence`, `parallel_interfaces_basin`): the objective (11.20) ($n=2$)
with $c=F(e_v)$, $K=\{F\le c\}$, $\Omega=\mathbb R^2$, $\mu=1$, $a=e_v$, $E=\{0\}$,
$\Sigma=\{v=0\}$ (every point a kink), $A=P_S$, a run in $K$, and the added hypothesis
$0\in\operatorname{aff}\partial F(p)\implies0\in\partial F(p)$ (at every $p$). -/
example : ∃ (F : Vec 2 → ℝ) (a : Vec 2) (c : ℝ) (Sg : Set (Vec 2)) (A : Vec 2 → Vec 2),
    ConvexOn ℝ univ F ∧ (∃ xstar, ∀ z, F xstar ≤ F z) ∧ IsCompact {x | F x ≤ c} ∧
      EuclideanStrongConvexOn univ 1 F ∧ sqNorm a = 1 ∧ IsClosed ({0} : Set ℝ) ∧
      Sg = {x | dot a x ∈ ({0} : Set ℝ)} ∧
      (∀ p ∈ (univ : Set (Vec 2)), p ∈ Sg → ¬ DifferentiableAt ℝ F p) ∧
      CenteredSmoothSublinear.LocallyC11On (univ \ Sg) F ∧
      (∀ x ∈ (univ : Set (Vec 2)),
        tangentProjection a '' ConvexSubdifferential.subdifferential F x = {A x}) ∧
      LipschitzOnWith 1 A univ ∧
      (∀ p : Vec 2, (0 : Vec 2) ∈ affineSpan ℝ (ConvexSubdifferential.subdifferential F p) →
        (0 : Vec 2) ∈ ConvexSubdifferential.subdifferential F p) ∧
      ∃ R : AdmissibleBFGSRun 2 F, ∀ k, R.x k ∈ {x | F x ≤ c} := by
  obtain ⟨hconv, ha, hmin, -, -, hcpt, hstrong, hA, himage, hLip, hsm, hkink⟩ :=
    spike_hypotheses 0 _ spike_objective_def2
  obtain ⟨R, hR⟩ := spike_run2
  have hcorrect : ∀ p : Vec 2,
      (0 : Vec 2) ∈ affineSpan ℝ (ConvexSubdifferential.subdifferential
        (NormalSpike.objective (NormalSpike.normal 0)) p) →
      (0 : Vec 2) ∈ ConvexSubdifferential.subdifferential
        (NormalSpike.objective (NormalSpike.normal 0)) p := by
    intro p hp
    by_cases hd : DifferentiableAt ℝ (NormalSpike.objective (NormalSpike.normal 0)) p
    · have hg := hasFDerivAt_coordinateGradient hd
      have h0 := (affine_critical_iff_of_hasFDerivAt hconv hg).mp hp
      rw [ConvexSubdifferential.subdifferential_eq_singleton_of_hasFDerivAt hconv hg, h0]
      exact mem_singleton _
    · have htan := (affine_critical_iff_tangent_zero hconv (fun g hg => hA p g hg) hd).mp hp
      have hp0 : dot (NormalSpike.normal 0) p = 0 := by
        by_contra hne
        exact hd (NormalSpike.objective_differentiable_off_interface _ p hne)
      have hpz : p = 0 := by
        rw [tangentProjection, hp0, zero_smul, sub_zero] at htan
        exact htan
      rw [hpz]
      exact ConvexSubdifferential.zero_mem_iff_global_minimum.mpr hmin
  refine ⟨_, NormalSpike.normal 0, NormalSpike.objective (NormalSpike.normal 0) (Pi.single 0 1),
    {x | dot (NormalSpike.normal 0) x ∈ ({0} : Set ℝ)}, tangentProjection (NormalSpike.normal 0),
    hconv, ⟨0, hmin⟩, hcpt _, hstrong, ha, isClosed_singleton, rfl,
    fun p _ hp => hkink p hp, ?_, fun x _ => himage x, hLip.lipschitzOnWith, hcorrect, R,
    fun k => ?_⟩
  · simpa only [mem_singleton_iff] using hsm
  · rw [← hR]
    exact R.objective_le_initial k

/-- Non-vacuity of the composite families (`immediate_family`, `tangential_family` and the
displays `disp/020`-`disp/022`): the objective (11.20) ($n=2$) is
$\psi(u,v)+h(v)$ with $\psi=\frac12\|x\|^2$ and $h(v)=|v|+r(v)$, and satisfies both the strong and
the tangential hypotheses ($\mu=1$, strictly convex sublevels, unique minimizer $0$ with $v_*=0$),
with an admissible run. -/
example : ∃ (F ψ : Vec 2 → ℝ) (h : ℝ → ℝ),
    (∀ (u : Vec 1) (v : ℝ), F (Fin.cons v u) = ψ (Fin.cons v u) + h v) ∧
      ConvexOn ℝ univ ψ ∧ CenteredSmoothSublinear.LocallyC11On univ ψ ∧ ConvexOn ℝ univ h ∧
      ScalarLocallyC11On ({0}ᶜ : Set ℝ) h ∧ EuclideanStrongConvexOn univ 1 F ∧
      ConvexOn ℝ univ (fun x : Vec 2 => ψ x - (1 / 2) * sqNorm (Fin.tail x)) ∧
      (∀ z, F 0 ≤ F z) ∧ (∀ z, F z = F 0 → z = 0) ∧ (0 : Vec 2) 0 = 0 ∧
      (∀ ℓ, IsCompact {x | F x ≤ ℓ} ∧ StrictConvex ℝ {x | F x ≤ ℓ}) ∧
      ∃ R : AdmissibleBFGSRun 2 F, R.x 0 = Pi.single 0 1 := by
  obtain ⟨hconv, -, hmin, huniq, -, hcpt, hstrong, -⟩ := spike_hypotheses 0 _ spike_objective_def2
  obtain ⟨R, hR⟩ := spike_run2
  have hψT : ConvexOn ℝ univ
      (fun x : Vec 2 => NormalSpike.quadratic x - (1 / 2) * sqNorm (Fin.tail x)) := by
    have hsq : ConvexOn ℝ univ (fun t : ℝ => (1 / 2) * t ^ 2) :=
      (even_two.convexOn_pow).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)
    convert convex_normal_composite hsq (vnormal 1) 0 using 1
    ext x
    rw [normalCoordinate_vnormal, NormalSpike.quadratic]
    have hs : sqNorm x = x 0 ^ 2 + sqNorm (Fin.tail x) := by
      simp only [sqNorm, Fin.sum_univ_succ, Fin.tail]
    rw [hs]
    ring
  refine ⟨_, NormalSpike.quadratic, NormalSpike.normalPenalty, fun u v => ?_,
    NormalSpike.quadratic_convex, NormalSpike.quadratic_locallyC11, NormalSpike.normalPenalty_convex,
    NormalSpike.normalPenalty_locallyC11_off_zero, hstrong, hψT, hmin, huniq, rfl,
    fun ℓ => ⟨hcpt ℓ, strictConvex_sublevel_of_strong (convex_continuous hconv) one_pos hstrong ℓ⟩,
    R, hR⟩
  rw [NormalSpike.printed_objective_split, NormalSpike.quadratic, sample_sqNorm,
    NormalSpike.normalPenalty]
  ring

/-- Non-vacuity of the common setting of Section 11.5 with the objects of the proof (displays
`disp/009`-`disp/019`, `transport_hypothesis`): the objective (11.20) ($n=2$), a run, $K$ its
initial sublevel, $\Omega=\mathbb R^2$, $\mu=1$, $a=e_v$, $b=0$, $A=P_S$, $E=\{0\}$, an orthonormal
basis $U$ of $S$, $\delta=1$ and a cutoff $\tau$ (`cutoff_exists`). -/
example : ∃ (F : Vec 2 → ℝ) (R : AdmissibleBFGSRun 2 F) (c : ℝ) (a : Vec 2) (A : Vec 2 → Vec 2)
    (r : ℕ) (U : Matrix (Fin 2) (Fin r) ℝ) (τ : ℝ → ℝ) (Lτ : ℝ≥0),
    ConvexOn ℝ univ F ∧ IsCompact {x | F x ≤ c} ∧ (∀ k, R.x k ∈ {x | F x ≤ c}) ∧
      EuclideanStrongConvexOn univ 1 F ∧ sqNorm a = 1 ∧
      (∀ x ∈ (univ : Set (Vec 2)), ∀ g ∈ ConvexSubdifferential.subdifferential F x,
        tangentProjection a g = A x) ∧
      LipschitzOnWith 1 A univ ∧
      CenteredSmoothSublinear.LocallyC11On (univ \ {x | dot a x - 0 ∈ ({0} : Set ℝ)}) F ∧
      Uᵀ * U = 1 ∧ (∀ v, (U * Uᵀ) *ᵥ v = tangentProjection a v) ∧
      LipschitzWith Lτ τ ∧ (∀ t, 0 ≤ τ t ∧ τ t ≤ 1) ∧
      (∀ t e, e ∈ ({0} : Set ℝ) → |t - e| ≤ 1 / 4 → τ t = 0) ∧
      (∀ t, (∀ e ∈ ({0} : Set ℝ), 1 / 2 ≤ |t - e|) → τ t = 1) := by
  obtain ⟨hconv, ha, -, -, -, hcpt, hstrong, hA, -, hLip, hsm, -⟩ :=
    spike_hypotheses 0 _ spike_objective_def2
  obtain ⟨R, -⟩ := spike_run2
  obtain ⟨r, U, hU, -, hproj⟩ := exists_tangent_matrix ha
  obtain ⟨τ, Lτ, hτ, h01, h0, h1⟩ := cutoff_exists {0} isClosed_singleton 1 one_pos
  refine ⟨_, R, NormalSpike.objective (NormalSpike.normal 0) (R.x 0), NormalSpike.normal 0,
    tangentProjection (NormalSpike.normal 0), r, U, τ, Lτ, hconv, hcpt _,
    fun k => R.objective_le_initial k, hstrong, ha, fun x _ g hg => hA x g hg,
    hLip.lipschitzOnWith, ?_, hU, hproj, hτ, h01, h0, h1⟩
  simpa only [sub_zero, mem_singleton_iff] using hsm

/-- Non-vacuity of the examples of Section 11.7.2 for $c=0$ (where the objective is (11.20)),
and of the general forms of display `disp/012`: a compact set $\Gamma$ without affine-critical
points and a level set above the minimum value exist for (11.20). -/
example : ∃ (F : Vec 2 → ℝ) (Γ : Set (Vec 2)),
    (∀ (u : Vec 1) (v : ℝ),
      F (Fin.cons v u) = (1 / 2) * (sqNorm u + v ^ 2) + |(1 + dot (0 : Vec 1) u) * v| +
        NormalSpike.sourcePrimitive v) ∧
      IsCompact Γ ∧ Γ.Nonempty ∧
      (∀ p ∈ Γ, (0 : Vec 2) ∉ affineSpan ℝ (ConvexSubdifferential.subdifferential F p)) ∧
      ∃ R : AdmissibleBFGSRun 2 F, R.x 0 = Pi.single 0 1 := by
  have hdef : ∀ (u : Vec 1) (v : ℝ),
      NormalSpike.objective (NormalSpike.normal 0) (Fin.cons v u) =
        (1 / 2) * (sqNorm u + v ^ 2) + |(1 + dot (0 : Vec 1) u) * v| +
          NormalSpike.sourcePrimitive v := by
    intro u v
    rw [spike_objective_def2]
    simp [dot]
    ring
  obtain ⟨R, hR⟩ := spike_run2
  have hconv := NormalSpike.objective_convex (NormalSpike.normal 0)
  have hp : HasFDerivAt (NormalSpike.objective (NormalSpike.normal 0))
      (gradientFunctional (NormalSpike.positiveGradient (NormalSpike.normal 0) (Pi.single 0 1)))
      (Pi.single 0 1) :=
    NormalSpike.objective_hasFDerivAt_pos _ _ (by simp [NormalSpike.normal_coordinate])
  refine ⟨_, {Pi.single 0 1}, hdef, isCompact_singleton, singleton_nonempty _, ?_, R, hR⟩
  intro p hp'
  rw [mem_singleton_iff] at hp'
  subst hp'
  rw [affine_critical_iff_of_hasFDerivAt hconv hp]
  intro h0
  have := congrFun h0 0
  simp only [NormalSpike.positiveGradient, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Pi.zero_apply, NormalSpike.normal, Pi.single_eq_same, mul_one,
    NormalSpike.normal_coordinate] at this
  have hd : dot (Pi.single 0 1 : Vec 2) (Pi.single 0 1) = 1 := by simp [dot, Pi.single_apply]
  rw [hd] at this
  linarith [NormalSpike.seriesMass_nonneg 1]

/-! ### Non-vacuity of the coupled example for every $\|c\|<1$

The general existence theorem does not apply to the coupled objective $F$ directly when $c\neq0$:
$F$ is differentiable at the points with $v=0$, $c^Tu=-1$, and lines through them inside
$\{v=0\}$ consist of kinks. The convex function $G=F+(|1+c^Tu|-(1+c^Tu))$ equals $F$ where
$1+c^Tu\ge0$, is differentiable exactly off $\{v=0\}\cup\{1+c^Tu=0\}$, and satisfies the
hypotheses of the existence theorem; a run of $G$ in a low sublevel is a run of $F$. -/

/-- The modified objective $G=F+(|1+c^Tu|-(1+c^Tu))$. -/
def cappedObjective (m : ℕ) (c : Vec (m + 1)) (x : Vec (m + 2)) : ℝ :=
  NormalSpike.variableObjective (NormalSpike.normal m) (Fin.cons 0 c) x +
    (|1 + dot (Fin.cons 0 c : Vec (m + 2)) x| - (1 + dot (Fin.cons 0 c : Vec (m + 2)) x))

theorem dot_linear_differentiable {n : ℕ} (b : Vec n) : Differentiable ℝ (dot b) := by
  have h : dot b = gradientFunctional b := funext fun y => (gradientFunctional_apply b y).symm
  rw [h]
  exact (gradientFunctional b).differentiable

theorem capped_facts (m : ℕ) (c : Vec (m + 1)) (hc : Real.sqrt (sqNorm c) < 1) :
    let a := NormalSpike.normal m
    let ch : Vec (m + 2) := Fin.cons 0 c
    ConvexOn ℝ univ (cappedObjective m c) ∧
      (∀ x, 0 ≤ 1 + dot ch x → cappedObjective m c x = NormalSpike.variableObjective a ch x) ∧
      (∀ x, (1 / 2) * sqNorm x ≤ cappedObjective m c x) ∧ cappedObjective m c 0 = 0 ∧
      (∀ y, dot a y ≠ 0 → 1 + dot ch y ≠ 0 → DifferentiableAt ℝ (cappedObjective m c) y) ∧
      (∀ y, DifferentiableAt ℝ (cappedObjective m c) y → dot a y ≠ 0 ∧ 1 + dot ch y ≠ 0) := by
  intro a ch
  have hca : dot a ch = 0 := NormalSpike.extended_coupling_tangent m c
  have hac : dot ch a = 0 := by rw [show dot ch a = dot a ch from dotProduct_comm _ _, hca]
  have haa : dot a a = 1 := by
    simpa only [dot, sqNorm, pow_two] using NormalSpike.normal_unit m
  have hch : Real.sqrt (sqNorm ch) < 1 := by rwa [NormalSpike.extended_coupling_sqNorm]
  have hpsi (y : ℝ) : 0 ≤ |1 + y| - (1 + y) := sub_nonneg.mpr (le_abs_self _)
  have hFconv := NormalSpike.variableObjective_convex (NormalSpike.normal_unit m) hca
    (Real.sqrt_nonneg _) (Real.sq_sqrt (sqNorm_nonneg _)) hch.le
  have hh : ConvexOn ℝ univ (fun t : ℝ => |1 + t| - (1 + t)) := by
    refine ⟨convex_univ, fun x _ y _ p q hp hq hpq => ?_⟩
    simp only [smul_eq_mul]
    have he : 1 + (p * x + q * y) = p * (1 + x) + q * (1 + y) := by
      linear_combination hpq.symm
    rw [he]
    have h1 := abs_add (p * (1 + x)) (q * (1 + y))
    rw [abs_mul, abs_mul, abs_of_nonneg hp, abs_of_nonneg hq] at h1
    nlinarith
  have hψ : ConvexOn ℝ univ (fun x : Vec (m + 2) => |1 + dot ch x| - (1 + dot ch x)) := by
    simpa only [normalCoordinate, sub_zero] using convex_normal_composite hh ch 0
  have hform (y : Vec (m + 2)) : cappedObjective m c y =
      NormalSpike.quadratic y + |(1 + dot ch y) * dot a y| + NormalSpike.sourcePrimitive (dot a y) +
        (|1 + dot ch y| - (1 + dot ch y)) := rfl
  have hlow (x : Vec (m + 2)) : (1 / 2) * sqNorm x ≤ cappedObjective m c x := by
    have h1 := NormalSpike.variableObjective_lower_bound a ch x
    have h2 := hpsi (dot ch x)
    unfold cappedObjective
    linarith
  -- the scalar profile of `G` along a line, used for the kinks
  have habs0 : ¬ DifferentiableAt ℝ (fun t : ℝ => |t|) 0 := not_differentiableAt_abs_zero
  refine ⟨hFconv.add hψ, fun x hx => ?_, hlow, ?_, fun y hv hw => ?_, fun y hy => ?_⟩
  · unfold cappedObjective
    rw [abs_of_nonneg hx, sub_self, add_zero]
  · simp [cappedObjective, NormalSpike.variableObjective, NormalSpike.quadratic, sqNorm, dot,
      NormalSpike.sourcePrimitive]
  · have hd1 : DifferentiableAt ℝ (fun y => (1 + dot ch y) * dot a y) y :=
      ((dot_linear_differentiable ch y).const_add 1).mul (dot_linear_differentiable a y)
    have hd2 : DifferentiableAt ℝ (fun y => 1 + dot ch y) y :=
      (dot_linear_differentiable ch y).const_add 1
    have hq : DifferentiableAt ℝ (@NormalSpike.quadratic (m + 2)) y :=
      (NormalSpike.quadratic_contDiff.differentiable (by decide)) y
    have hr : DifferentiableAt ℝ (fun y => NormalSpike.sourcePrimitive (dot a y)) y :=
      (NormalSpike.sourcePrimitive_hasDerivAt _).differentiableAt.comp y (dot_linear_differentiable a y)
    have h := ((hq.add (hd1.abs (mul_ne_zero hw hv))).add hr).add ((hd2.abs hw).sub hd2)
    exact h.congr_of_eventuallyEq (Eventually.of_forall fun z => hform z)
  · constructor
    · intro hv
      have hw : 1 + dot ch y ≠ 0 ∨ 1 + dot ch y = 0 := (em (1 + dot ch y = 0)).symm.imp id id
      -- along the normal direction: `G (y + t a) = q(t) + |1 + cᵀu| |t| + r(t) + const`
      have hpath : DifferentiableAt ℝ (fun t : ℝ => y + t • a) 0 :=
        (differentiableAt_const y).add (differentiableAt_id.smul_const a)
      have hcomp : DifferentiableAt ℝ (fun t : ℝ => cappedObjective m c (y + t • a)) 0 := by
        have hy' : DifferentiableAt ℝ (cappedObjective m c) (y + (0 : ℝ) • a) := by
          simpa only [zero_smul, add_zero] using hy
        exact hy'.comp (0 : ℝ) hpath
      have hq : DifferentiableAt ℝ (fun t : ℝ => NormalSpike.quadratic (y + t • a)) 0 :=
        ((NormalSpike.quadratic_contDiff.differentiable (by decide)) _).comp (0 : ℝ) hpath
      have hr : DifferentiableAt ℝ NormalSpike.sourcePrimitive 0 :=
        (NormalSpike.sourcePrimitive_hasDerivAt 0).differentiableAt
      have hd := (hcomp.sub hq).sub hr
      have heq : (fun t : ℝ => cappedObjective m c (y + t • a) - NormalSpike.quadratic (y + t • a) -
          NormalSpike.sourcePrimitive t) =
          fun t => |1 + dot ch y| * |t| + (|1 + dot ch y| - (1 + dot ch y)) := by
        funext t
        rw [hform, NormalSpike.dot_add_smul, NormalSpike.dot_add_smul, hv, hac, haa]
        simp only [mul_zero, add_zero, zero_add, mul_one, abs_mul]
        ring
      rw [heq] at hd
      rcases hw with hw | hw
      · apply habs0
        have h2 := (hd.sub_const (|1 + dot ch y| - (1 + dot ch y))).const_mul (|1 + dot ch y|)⁻¹
        convert h2 using 1
        funext t
        field_simp
      · -- if also `1 + cᵀu = 0`, use the second kink (below)
        have hc0 : (ch : Vec (m + 2)) ≠ 0 := by
          intro h0
          rw [h0] at hw
          simp [dot] at hw
        have hpos : 0 < sqNorm ch := lt_of_le_of_ne (sqNorm_nonneg _)
          (fun h => hc0 ((CertificateGeometry.sqNorm_eq_zero_iff _).mp h.symm))
        set w : Vec (m + 2) := (sqNorm ch)⁻¹ • ch with hw_def
        have hcw : dot ch w = 1 := by
          rw [hw_def, dot_smul_right, show dot ch ch = sqNorm ch by simp only [dot, sqNorm, pow_two]]
          field_simp
        have haw : dot a w = 0 := by rw [hw_def, dot_smul_right, hca, mul_zero]
        have hpath2 : DifferentiableAt ℝ (fun t : ℝ => y + t • w) 0 :=
          (differentiableAt_const y).add (differentiableAt_id.smul_const w)
        have hcomp2 : DifferentiableAt ℝ (fun t : ℝ => cappedObjective m c (y + t • w)) 0 := by
          have hy' : DifferentiableAt ℝ (cappedObjective m c) (y + (0 : ℝ) • w) := by
            simpa only [zero_smul, add_zero] using hy
          exact hy'.comp (0 : ℝ) hpath2
        have hq2 : DifferentiableAt ℝ (fun t : ℝ => NormalSpike.quadratic (y + t • w)) 0 :=
          ((NormalSpike.quadratic_contDiff.differentiable (by decide)) _).comp (0 : ℝ) hpath2
        have hd2 := (hcomp2.sub hq2).add (differentiableAt_id (x := (0 : ℝ)))
        have heq2 : (fun t : ℝ => cappedObjective m c (y + t • w) -
            NormalSpike.quadratic (y + t • w) + id t) =
            fun t => (|dot a y| + 1) * |t| + NormalSpike.sourcePrimitive (dot a y) := by
          funext t
          rw [hform, NormalSpike.dot_add_smul, NormalSpike.dot_add_smul, hcw, haw]
          have hw' : 1 + dot ch y + t * 1 = t := by linarith
          rw [show 1 + (dot ch y + t * 1) = 1 + dot ch y + t * 1 by ring, hw', mul_zero, add_zero,
            abs_mul]
          simp only [id]
          ring
        rw [heq2] at hd2
        apply habs0
        have h2 := (hd2.sub_const (NormalSpike.sourcePrimitive (dot a y))).const_mul
          (|dot a y| + 1)⁻¹
        convert h2 using 1
        funext t
        have : (|dot a y| + 1) ≠ 0 := by positivity
        field_simp
    · intro hw
      have hc0 : (ch : Vec (m + 2)) ≠ 0 := by
        intro h0
        rw [h0] at hw
        simp [dot] at hw
      have hpos : 0 < sqNorm ch := lt_of_le_of_ne (sqNorm_nonneg _)
        (fun h => hc0 ((CertificateGeometry.sqNorm_eq_zero_iff _).mp h.symm))
      set w : Vec (m + 2) := (sqNorm ch)⁻¹ • ch with hw_def
      have hcw : dot ch w = 1 := by
        rw [hw_def, dot_smul_right, show dot ch ch = sqNorm ch by simp only [dot, sqNorm, pow_two]]
        field_simp
      have haw : dot a w = 0 := by rw [hw_def, dot_smul_right, hca, mul_zero]
      have hpath2 : DifferentiableAt ℝ (fun t : ℝ => y + t • w) 0 :=
        (differentiableAt_const y).add (differentiableAt_id.smul_const w)
      have hcomp2 : DifferentiableAt ℝ (fun t : ℝ => cappedObjective m c (y + t • w)) 0 := by
        have hy' : DifferentiableAt ℝ (cappedObjective m c) (y + (0 : ℝ) • w) := by
          simpa only [zero_smul, add_zero] using hy
        exact hy'.comp (0 : ℝ) hpath2
      have hq2 : DifferentiableAt ℝ (fun t : ℝ => NormalSpike.quadratic (y + t • w)) 0 :=
        ((NormalSpike.quadratic_contDiff.differentiable (by decide)) _).comp (0 : ℝ) hpath2
      have hd2 := (hcomp2.sub hq2).add (differentiableAt_id (x := (0 : ℝ)))
      have heq2 : (fun t : ℝ => cappedObjective m c (y + t • w) -
          NormalSpike.quadratic (y + t • w) + id t) =
          fun t => (|dot a y| + 1) * |t| + NormalSpike.sourcePrimitive (dot a y) := by
        funext t
        rw [hform, NormalSpike.dot_add_smul, NormalSpike.dot_add_smul, hcw, haw]
        have hw' : 1 + dot ch y + t * 1 = t := by linarith
        rw [show 1 + (dot ch y + t * 1) = 1 + dot ch y + t * 1 by ring, hw', mul_zero, add_zero,
          abs_mul]
        simp only [id]
        ring
      rw [heq2] at hd2
      apply habs0
      have h2 := (hd2.sub_const (NormalSpike.sourcePrimitive (dot a y))).const_mul
        (|dot a y| + 1)⁻¹
      convert h2 using 1
      funext t
      have : (|dot a y| + 1) ≠ 0 := by positivity
      field_simp

/-- Admissible runs exist on the coupled objective of Section 11.7.2 for every $\|c\|<1$ with
initial value below any prescribed $\varepsilon>0$ (they start at $x_0=t_0e_v$, $H_0=I$,
$c_1=1/4$, $c_2=1/2$): runs of `cappedObjective` from the low sublevel stay where it equals $F$. -/
theorem variable_runs_exist (m : ℕ) (c : Vec (m + 1)) (hc : Real.sqrt (sqNorm c) < 1)
    (F : Vec (m + 2) → ℝ)
    (hF_def : ∀ (u : Vec (m + 1)) (v : ℝ),
      F (Fin.cons v u) = (1 / 2) * (sqNorm u + v ^ 2) + |(1 + dot c u) * v| +
        NormalSpike.sourcePrimitive v) :
    ∀ ε : ℝ, 0 < ε → ∃ R : AdmissibleBFGSRun (m + 2) F, F (R.x 0) < ε := by
  intro ε hε
  have hFe := variable_objective_eq m c F hF_def
  subst hFe
  obtain ⟨hGconv, hGeq, hGlow, hG0, hGdiff, hGnd⟩ := capped_facts m c hc
  set a := NormalSpike.normal m with ha_def
  set ch : Vec (m + 2) := Fin.cons 0 c with hch_def
  have hca : dot a ch = 0 := NormalSpike.extended_coupling_tangent m c
  have hac : dot ch a = 0 := by rw [show dot ch a = dot a ch from dotProduct_comm _ _, hca]
  have haa : dot a a = 1 := by
    simpa only [dot, sqNorm, pow_two] using NormalSpike.normal_unit m
  have hc1 : sqNorm ch < 1 := by
    rw [hch_def, NormalSpike.extended_coupling_sqNorm]
    have h := (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mp hc
    simpa using h
  have hch' : Real.sqrt (sqNorm ch) < 1 := by rwa [hch_def, NormalSpike.extended_coupling_sqNorm]
  have hFconv : ConvexOn ℝ univ (NormalSpike.printedVariableObjective m c) :=
    NormalSpike.variableObjective_convex (NormalSpike.normal_unit m) hca
      (Real.sqrt_nonneg _) (Real.sq_sqrt (sqNorm_nonneg _)) hch'.le
  have hF0 : NormalSpike.printedVariableObjective m c 0 = 0 := NormalSpike.variableObjective_zero _ _
  -- a starting point `t₀ e_v` with small value
  have hcont : Continuous (fun t : ℝ => NormalSpike.printedVariableObjective m c (t • a)) :=
    (convex_continuous hFconv).comp (continuous_id.smul continuous_const)
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      NormalSpike.printedVariableObjective m c (t • a) < min ε (1 / 2) ∧ 0 < t := by
    have h0 : NormalSpike.printedVariableObjective m c ((0 : ℝ) • a) < min ε (1 / 2) := by
      rw [zero_smul, hF0]; exact lt_min hε (by norm_num)
    exact ((hcont.continuousAt.eventually (gt_mem_nhds h0)).filter_mono nhdsWithin_le_nhds).and
      self_mem_nhdsWithin
  obtain ⟨t₀, hval, ht₀⟩ := hsmall.exists
  have hdot0 : dot ch (t₀ • a) = 0 := by rw [dot_smul_right, hac, mul_zero]
  have hG0' : cappedObjective m c (t₀ • a) = NormalSpike.printedVariableObjective m c (t₀ • a) :=
    hGeq _ (by rw [hdot0]; norm_num)
  have hdiff0 : DifferentiableAt ℝ (cappedObjective m c) (t₀ • a) :=
    hGdiff _ (by rw [dot_smul_right, haa, mul_one]; exact ht₀.ne') (by rw [hdot0]; norm_num)
  -- the hypotheses of the existence theorem for `G`
  have hbdd : BddBelow (range (cappedObjective m c)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨y, rfl⟩
    exact (mul_nonneg (by norm_num) (sqNorm_nonneg y)).trans (hGlow y)
  have hsub1 (x p : Vec (m + 2)) (hx : dot a x ≠ 0) :
      {t : ℝ | dot a (x + t • p) = 0}.Subsingleton := by
    intro t₁ h₁ t₂ h₂
    simp only [mem_setOf_eq, NormalSpike.dot_add_smul] at h₁ h₂
    have hp : dot a p ≠ 0 := fun hp => hx (by rw [hp, mul_zero, add_zero] at h₁; exact h₁)
    have h3 : (t₁ - t₂) * dot a p = 0 := by linarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right hp)
  have hsub2 (x p : Vec (m + 2)) (hx : 1 + dot ch x ≠ 0) :
      {t : ℝ | 1 + dot ch (x + t • p) = 0}.Subsingleton := by
    intro t₁ h₁ t₂ h₂
    simp only [mem_setOf_eq, NormalSpike.dot_add_smul] at h₁ h₂
    have hp : dot ch p ≠ 0 := fun hp => hx (by rw [hp, mul_zero, add_zero] at h₁; linarith)
    have h3 : (t₁ - t₂) * dot ch p = 0 := by linarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right hp)
  have hline : ∀ x p : Vec (m + 2), DifferentiableAt ℝ (cappedObjective m c) x → p ≠ 0 →
      {t : ℝ | ¬ DifferentiableAt ℝ (cappedObjective m c) (x + t • p)}.Countable := by
    intro x p hx _
    obtain ⟨hx1, hx2⟩ := hGnd x hx
    apply ((hsub1 x p hx1).countable.union (hsub2 x p hx2).countable).mono
    intro t ht
    by_contra hn
    simp only [mem_union, mem_setOf_eq, not_or] at hn
    exact ht (hGdiff _ hn.1 hn.2)
  have hstat : ∀ y g, HasFDerivAt (cappedObjective m c) (gradientFunctional g) y → g ≠ 0 := by
    intro y g hg hg0
    rw [hg0] at hg
    have hy := global_minimum_of_zero_gradient hGconv hg
    have hle := (hGlow y).trans (hy 0)
    rw [hG0] at hle
    have hy0 : y = 0 := (CertificateGeometry.sqNorm_eq_zero_iff y).mp
      (le_antisymm (by nlinarith [sqNorm_nonneg y]) (sqNorm_nonneg y))
    have hd := (hGnd y hg.differentiableAt).1
    rw [hy0] at hd
    exact hd (by simp [dot])
  obtain ⟨R, hR0, -, -, -, -⟩ := AdmissibleRunExistence.exists_admissible_run hGconv hbdd hline hstat
    (hasFDerivAt_coordinateGradient hdiff0) Matrix.PosDef.one (by norm_num : (0 : ℝ) < 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1 / 2) (by norm_num)
  -- the run stays where `G = F`
  have hO : IsOpen {y : Vec (m + 2) | 0 < 1 + dot ch y} :=
    isOpen_lt continuous_const (continuous_const.add (dot_linear_differentiable ch).continuous)
  have hin : ∀ k, R.x k ∈ {y : Vec (m + 2) | 0 < 1 + dot ch y} := by
    intro k
    have hv : cappedObjective m c (R.x k) < 1 / 2 := by
      have h1 := R.objective_le_initial k
      rw [hR0, hG0'] at h1
      exact h1.trans_lt (hval.trans_le (min_le_right _ _))
    have hsq : sqNorm (R.x k) < 1 := by nlinarith [hGlow (R.x k)]
    have hcs := dot_sq_le_sqNorm_mul_sqNorm ch (R.x k)
    have hlt : (dot ch (R.x k)) ^ 2 < 1 := by
      calc (dot ch (R.x k)) ^ 2 ≤ sqNorm ch * sqNorm (R.x k) := hcs
        _ ≤ 1 * sqNorm (R.x k) :=
          mul_le_mul_of_nonneg_right hc1.le (sqNorm_nonneg _)
        _ < 1 := by rw [one_mul]; exact hsq
    have habs : |dot ch (R.x k)| < 1 := by
      rw [← sq_lt_one_iff_abs_lt_one]; exact hlt
    show 0 < 1 + dot ch (R.x k)
    linarith [neg_abs_le (dot ch (R.x k))]
  have heqk (k : ℕ) : NormalSpike.printedVariableObjective m c (R.x k) =
      cappedObjective m c (R.x k) := (hGeq _ (hin k).le).symm
  refine ⟨AdmissibleBFGSRun.mk hFconv R.x R.H R.g R.α R.c₁ R.c₂ R.c₁_pos R.c₁_lt_c₂ R.c₂_lt_one
      R.initial_posDef R.alpha_pos R.gradient_nonzero (fun k => ?_) R.step R.update (fun k => ?_)
      R.weak_wolfe, ?_⟩
  · apply (R.hasGradient k).congr_of_eventuallyEq
    filter_upwards [hO.mem_nhds (hin k)] with y hy
    exact (hGeq y (le_of_lt hy)).symm
  · rw [heqk, heqk]
    exact R.armijo k
  · change NormalSpike.printedVariableObjective m c (R.x 0) < ε
    rw [hR0]
    exact hval.trans_le (min_le_left _ _)

/-- Non-vacuity of item `prose/064` (`variable_local_basin`) for every $\|c\|<1$: the basin
contains initial points of admissible runs, and those runs converge. -/
theorem variable_basin_nonvacuous (m : ℕ) (c : Vec (m + 1)) (hc : Real.sqrt (sqNorm c) < 1)
    (F : Vec (m + 2) → ℝ)
    (hF_def : ∀ (u : Vec (m + 1)) (v : ℝ),
      F (Fin.cons v u) = (1 / 2) * (sqNorm u + v ^ 2) + |(1 + dot c u) * v| +
        NormalSpike.sourcePrimitive v) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ R : AdmissibleBFGSRun (m + 2) F, F (R.x 0) < ε ∧
      Tendsto (fun k => F (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0) := by
  obtain ⟨ε, hε, h⟩ := variable_local_basin m c hc F hF_def
  obtain ⟨R, hR⟩ := variable_runs_exist m c hc F hF_def ε hε
  exact ⟨ε, hε, R, hR, h R hR⟩

end BfgsCoverage.Companion.Ch11U
