import BfgsVerification.PlanarQuadraticTargets
import BfgsVerification.PlanarMaxHessianBasin
import BfgsVerification.PlanarAllEndpoints
import BfgsVerification.ScalarResidualFamilies
import BfgsVerification.EuclideanResidualLineSearch
import BfgsVerification.PlanarCornerFiniteness
import BfgsVerification.CenteredSmoothSublinear
import BfgsVerification.UnexcitedMetric

/-!
# Lean coverage: `paper/sections/local.tex`

Section `art:local` ("Local convergence: geometry that survives near a minimizer"): Lemma
`art:localization`, the proof of Theorem `art:polyhedral` (the theorem itself is in
`paper/statements/positive_partition.tex`, module `BfgsArticle.Coverage.Article.PositivePartition`),
Corollaries `art:plq` and `art:local-centered`, the lasso and Euclidean-residual reductions, the
affine-critical set, Theorem `art:planar-cluster`, Corollaries `art:planar-convergence` and
`art:planar-max`, Theorem `art:nonradial-example`, their proofs' displays, and the prose claims of
the section. Register: `editorial/lean_coverage/register/A_local.json`.

## Conventions

* `Vec n = Fin n → ℝ` carries the sup norm; every Euclidean quantity is explicit:
  `‖euclideanVector v‖` is the Euclidean norm $\|v\|$, `sqNorm v` is $\|v\|^2$, `dot a b` is
  $a^Tb$. Open Euclidean balls are written `{x | ‖euclideanVector (x - c)‖ < r}`. Where a statement
  only needs "a ball" or "sufficiently close", the sup-norm `Metric.ball` is used (all norms on
  $\R^n$ are equivalent).
* "$F:\R^n\to\R$ finite and convex" is `ConvexOn ℝ univ F`; "$x_*$ is the unique minimizer" is
  `hmin : ∀ x, F xstar ≤ F x` and `huniq : ∀ x, F x = F xstar → x = xstar`; in Theorem
  `art:planar-cluster`, "$F$ attains its minimum $F_*$" is `IsLeast (Set.range F) Fstar`.
* An (infinite) admissible full-BFGS run (Definition `art:admissible`, arbitrary $H_0\succ0$,
  fixed constants $0<c_1<c_2<1$) is `R : AdmissibleBFGSRun n F` with iterates `R.x k`, gradients
  `R.g k`, matrices `R.H k`, constants `R.c₁`, `R.c₂`, $q_k$ = `R.q k`, $d_k=\alpha_kq_k$ =
  `R.d k`. "Chosen before the run and its initial matrix" is the quantifier order
  `∃ ε, ... ∀ R : AdmissibleBFGSRun n F, ...`.
* $\nabla f(x)$ is `coordinateGradient f x` (coordinates of the Fréchet derivative);
  $C^{1,1}_{\rm loc}(V)$ is `CenteredSmoothSublinear.LocallyC11On V f`
  (`DifferentiableOn ℝ f V ∧ LocallyLipschitzOn V (fderiv ℝ f)`); $\partial F(p)$ is
  `ConvexSubdifferential.subdifferential F p`; $\mathcal C_{\rm aff}$ is
  `{p | AffineCriticalObjective.IsAffineCritical F p}` (display `disp/006`); a cluster point $p$ of
  the iterates is `MapClusterPt p atTop R.x`; eligibility of a pair (`energy.tex:242-245`) is
  `TransportedCertificate.EligiblePair F c₁ c₂ x z g h`.
* Objects introduced by the text ($\delta$, $B_r(x_*)$, $B_\rho(x_*)$, $L$, $\psi$, $\gamma$, $I_0$, $\sigma$,
  $A(x)$, $E_k$, $v(u)$, $D$, the branches $f_i$ and $F$ of the example) are variables with their
  defining equations as hypotheses. A hypothesis whose name starts with `_` is a standing
  assumption that the Lean proof does not use.

## Items

| Item | Lines | Lean |
|---|---|---|
| `lemma/art:localization` | 16-22 | `localization` |
| `disp/001`, `disp/002` | 26-33 | `localization_sphere_min`, `localization_radial_lower` |
| `disp/003`, `disp/004` | 61-70 | `polyhedral_radial_derivative`, `polyhedral_inward_taylor` |
| `corollary/art:plq` | 78-83 | `plq`, `plq_loss_regularizer` |
| `corollary/art:local-centered` | 101-108 | `local_centered` |
| `disp/005` | 122-129 | `lasso_decomposition` |
| `disp/006` | 157-160 | `affineCritical_set_eq` (definition) |
| `theorem/art:planar-cluster` | 212-227 | `planar_cluster` |
| `disp/007`, `disp/008`, `disp/009` | 238-267 | `planar_cluster_segment_values`, `planar_cluster_field`, `planar_cluster_energy` |
| `corollary/art:planar-convergence` | 274-279 | `planar_convergence` |
| `corollary/art:planar-max` | 301-320 | `planar_max`, `planar_max_hessian_contours` |
| `disp/012` | 326-328 | `planar_max_barycentric` |
| `theorem/art:nonradial-example` | 367-382 | `nonradial_example` |
| `disp/014` to `disp/017` | 391-424 | `example_coefficients`, `example_tie_expansion`, `example_radial_jump`, `example_pair_values` |

Prose items (`prose/005`, `007`-`010`, `012`-`018`, `021`-`024`, `026`-`028`, `031`, `033`,
`035`, `037`, `038`, `044`) are covered by the theorems whose docstrings cite them (for example
`hessian_bound_strict_contours` for `prose/026`, `planar_max_balance_continuous` for `prose/037`). Undisplayed
quantitative steps of the proof of Theorem `art:nonradial-example` are checked by
`example_model_facts`, `example_box_facts`, `example_tie` and `example_ratio_limits`.

## Non-vacuity

The `example`s at the end show that the standing assumptions of the lemma, of the displays of
the proof of Theorem `art:polyhedral`, of the lasso and Euclidean-residual statements, of
Corollary `art:local-centered`, of Theorem `art:planar-cluster` / Corollary
`art:planar-convergence` and of Corollary `art:planar-max` can hold (the planar ones by the
objective of Theorem `art:nonradial-example`); `plq_different_hessians` does this for Corollary
`art:plq`. For Theorem `art:planar-cluster`, Corollary `art:planar-convergence` and the displays
`disp/007`, `disp/009` one example also exhibits an actual admissible run starting in $K$: the
library's run `UnexcitedMetric.run` for $F(u,v)=u^2+|v|$ with $b=1$. The assumptions of
`planar_cluster_field` include the contradiction hypothesis of the proof of Theorem
`art:planar-cluster` (no affine-critical cluster point), so they cannot all hold: that is what
that proof shows.
-/

noncomputable section
open Set Filter Topology Matrix BfgsVerification
open scoped ContDiff

namespace BfgsCoverage.Article.Local

/-! ### Helpers: Euclidean quantities on `Vec n` -/

/-- $\|v\|^2$ for the Euclidean norm. -/
theorem euclid_norm_sq {n : ℕ} (v : Vec n) : ‖euclideanVector v‖ ^ 2 = sqNorm v :=
  FrameNorms.euclidean_norm_sq (euclideanVector v)

/-- `euclideanVector` is additive. -/
theorem euclideanVector_sub {n : ℕ} (x y : Vec n) :
    euclideanVector (x - y) = euclideanVector x - euclideanVector y := rfl

/-- `euclideanVector` is homogeneous. -/
theorem euclideanVector_smul {n : ℕ} (c : ℝ) (x : Vec n) :
    euclideanVector (c • x) = c • euclideanVector x := rfl

/-- Cauchy--Schwarz with Euclidean norms. -/
theorem dot_le_euclid {n : ℕ} (a b : Vec n) :
    dot a b ≤ ‖euclideanVector a‖ * ‖euclideanVector b‖ := by
  rw [← AffineCriticalObjective.euclidean_pairing_eq_dot]
  exact real_inner_le_norm _ _

/-- The Euclidean norm is continuous on `Vec n`. -/
theorem continuous_euclid_norm {n : ℕ} : Continuous fun v : Vec n => ‖euclideanVector v‖ :=
  (PiLp.continuous_equiv_symm 2 _).norm

/-- The open Euclidean ball is open and convex. -/
theorem euclid_ball_open_convex {n : ℕ} (c : Vec n) (r : ℝ) :
    IsOpen {x : Vec n | ‖euclideanVector (x - c)‖ < r} ∧
      Convex ℝ {x : Vec n | ‖euclideanVector (x - c)‖ < r} := by
  refine ⟨isOpen_lt (continuous_euclid_norm.comp (continuous_id.sub continuous_const))
    continuous_const, ?_⟩
  intro x hx y hy s t hs ht hst
  have he : s • x + t • y - c = s • (x - c) + t • (y - c) := by
    calc s • x + t • y - c = s • x + t • y - (s + t) • c := by rw [hst, one_smul]
      _ = s • (x - c) + t • (y - c) := by module
  show ‖euclideanVector (s • x + t • y - c)‖ < r
  rw [he, show euclideanVector (s • (x - c) + t • (y - c)) =
    s • euclideanVector (x - c) + t • euclideanVector (y - c) from rfl]
  calc ‖s • euclideanVector (x - c) + t • euclideanVector (y - c)‖
      ≤ s * ‖euclideanVector (x - c)‖ + t * ‖euclideanVector (y - c)‖ := by
        refine (norm_add_le _ _).trans (le_of_eq ?_)
        rw [norm_smul, norm_smul, Real.norm_of_nonneg hs, Real.norm_of_nonneg ht]
    _ ≤ s * max ‖euclideanVector (x - c)‖ ‖euclideanVector (y - c)‖ +
          t * max ‖euclideanVector (x - c)‖ ‖euclideanVector (y - c)‖ :=
        add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) hs)
          (mul_le_mul_of_nonneg_left (le_max_right _ _) ht)
    _ = max ‖euclideanVector (x - c)‖ ‖euclideanVector (y - c)‖ := by rw [← add_mul, hst, one_mul]
    _ < r := max_lt hx hy

/-! ### Lemma `art:localization` and its proof -/

/-- Item `A/local/lemma/art:localization` (`paper/sections/local.tex:16-22`), Lemma
`art:localization` ("A common local basin").

Let $F:\R^n\to\R$ be finite and convex with a unique minimizer $x_*$. Every sublevel is compact.
For each neighborhood $U$ of $x_*$, there is $\varepsilon>0$ such that
$\{F\le F(x_*)+\varepsilon\}\subset U$. Thus any admissible run starting in that sublevel stays
in $U$, independently of its initial SPD matrix (`ε` is chosen before the run `R`). -/
theorem localization {n : ℕ} (F : Vec n → ℝ) (hF : ConvexOn ℝ univ F) (xstar : Vec n)
    (hmin : ∀ x, F xstar ≤ F x) (huniq : ∀ x, F x = F xstar → x = xstar) :
    (∀ c : ℝ, IsCompact {x | F x ≤ c}) ∧
      ∀ U ∈ 𝓝 xstar, ∃ ε : ℝ, 0 < ε ∧ {x | F x ≤ F xstar + ε} ⊆ U ∧
        ∀ R : AdmissibleBFGSRun n F, F (R.x 0) ≤ F xstar + ε → ∀ k, R.x k ∈ U := by
  refine ⟨Localization.sublevel_compact hF xstar hmin huniq, fun U hU => ?_⟩
  obtain ⟨ε, hε, hsub⟩ := Localization.neighborhood_basin hF xstar hmin huniq hU
  exact ⟨ε, hε, hsub, fun R hR k => hsub ((R.objective_le_initial k).trans hR)⟩

/-- Item `A/local/disp/001` (`paper/sections/local.tex:26-28`), in the proof of Lemma
`art:localization`.

Under the assumptions of the lemma, with $U$ a neighborhood of $x_*$ and $r>0$ chosen with
$\overline B_r(x_*)\subset U$ (Euclidean ball), put
$\delta=\inf_{\|u\|=r}(F(x_*+u)-F(x_*))$. Continuity, compactness of the sphere and uniqueness
give that this infimum is a minimum and
\[ \delta=\min_{\norm{u}=r}\bigl(F(x_*+u)-F(x_*)\bigr)>0. \]
The sphere $\{\|u\|=r\}$ is nonempty only for $n\ge1$; `hn : 1 ≤ n` is the article's standing
convention $n\ge1$ (Definition `art:admissible`). -/
theorem localization_sphere_min {n : ℕ} (hn : 1 ≤ n) (F : Vec n → ℝ) (hF : ConvexOn ℝ univ F)
    (xstar : Vec n) (hmin : ∀ x, F xstar ≤ F x) (huniq : ∀ x, F x = F xstar → x = xstar)
    (U : Set (Vec n)) (_hU : U ∈ 𝓝 xstar) (r : ℝ) (hr : 0 < r)
    (_hrU : {x | ‖euclideanVector (x - xstar)‖ ≤ r} ⊆ U) (δ : ℝ)
    (hδ : δ = sInf ((fun u => F (xstar + u) - F xstar) '' {u | ‖euclideanVector u‖ = r})) :
    IsLeast ((fun u => F (xstar + u) - F xstar) '' {u | ‖euclideanVector u‖ = r}) δ ∧
      0 < δ := by
  set S := {u : Vec n | ‖euclideanVector u‖ = r} with hSdef
  have hS : IsCompact S := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact isClosed_eq continuous_euclid_norm continuous_const
    · refine (Metric.isBounded_closedBall (x := (0 : Vec n)) (r := r)).subset ?_
      intro u hu
      rw [Metric.mem_closedBall, dist_zero_right]
      apply ConvexSubdifferential.norm_le_of_sqNorm_le hr.le
      rw [← euclid_norm_sq, show ‖euclideanVector u‖ = r from hu]
  have hne : S.Nonempty := by
    refine ⟨Pi.single (⟨0, hn⟩ : Fin n) r, ?_⟩
    have h := euclid_norm_sq (Pi.single (⟨0, hn⟩ : Fin n) r)
    have hs : sqNorm (Pi.single (⟨0, hn⟩ : Fin n) r) = r ^ 2 := by
      simp [sqNorm, Pi.single_apply]
    rw [hs] at h
    exact (pow_left_inj₀ (norm_nonneg _) hr.le two_ne_zero).mp h
  have hcont : ContinuousOn (fun u => F (xstar + u) - F xstar) S :=
    ((convex_continuous hF).comp (continuous_const.add continuous_id)).sub
      continuous_const |>.continuousOn
  obtain ⟨u0, hu0, hmin0⟩ := hS.exists_isMinOn hne hcont
  have hleast : IsLeast ((fun u => F (xstar + u) - F xstar) '' S) (F (xstar + u0) - F xstar) :=
    ⟨⟨u0, hu0, rfl⟩, by rintro _ ⟨u, hu, rfl⟩; exact hmin0 hu⟩
  have hδeq : δ = F (xstar + u0) - F xstar := by rw [hδ]; exact hleast.csInf_eq
  refine ⟨hδeq ▸ hleast, ?_⟩
  rw [hδeq]
  have hu0ne : u0 ≠ 0 := by
    rintro rfl
    have h0 : ‖euclideanVector (0 : Vec n)‖ = r := hu0
    rw [show euclideanVector (0 : Vec n) = 0 from rfl, norm_zero] at h0
    exact hr.ne h0
  have hne' : F (xstar + u0) ≠ F xstar := fun h => hu0ne (by
    have := huniq _ h
    simpa using this)
  exact sub_pos.mpr (lt_of_le_of_ne (hmin _) (Ne.symm hne'))

/-- Item `A/local/disp/002` (`paper/sections/local.tex:31-33`), in the proof of Lemma
`art:localization`.

Under the assumptions of display `disp/001` (with $\delta$ the minimum over the Euclidean sphere
of radius $r$), for $\|x-x_*\|\ge r$, convexity at the point at distance $r$ on the segment from
$x_*$ to $x$ gives
\[ F(x)-F(x_*)\ge\frac{\norm{x-x_*}}r\delta. \] -/
theorem localization_radial_lower {n : ℕ} (hn : 1 ≤ n) (F : Vec n → ℝ) (hF : ConvexOn ℝ univ F)
    (xstar : Vec n) (hmin : ∀ x, F xstar ≤ F x) (huniq : ∀ x, F x = F xstar → x = xstar)
    (U : Set (Vec n)) (hU : U ∈ 𝓝 xstar) (r : ℝ) (hr : 0 < r)
    (hrU : {x | ‖euclideanVector (x - xstar)‖ ≤ r} ⊆ U) (δ : ℝ)
    (hδ : δ = sInf ((fun u => F (xstar + u) - F xstar) '' {u | ‖euclideanVector u‖ = r}))
    (x : Vec n) (hx : r ≤ ‖euclideanVector (x - xstar)‖) :
    ‖euclideanVector (x - xstar)‖ / r * δ ≤ F x - F xstar := by
  obtain ⟨hleast, _⟩ := localization_sphere_min hn F hF xstar hmin huniq U hU r hr hrU δ hδ
  set R := ‖euclideanVector (x - xstar)‖ with hRdef
  have hR : 0 < R := lt_of_lt_of_le hr hx
  set t := r / R with htdef
  have ht0 : 0 ≤ t := div_nonneg hr.le hR.le
  have ht1 : t ≤ 1 := (div_le_one hR).mpr hx
  have hz : ‖euclideanVector (t • (x - xstar))‖ = r := by
    rw [euclideanVector_smul, norm_smul, Real.norm_of_nonneg ht0, ← hRdef, htdef]
    field_simp
  have hδz : δ ≤ F (xstar + t • (x - xstar)) - F xstar := hleast.2 ⟨_, hz, rfl⟩
  have hconv := hF.2 (mem_univ xstar) (mem_univ x) (sub_nonneg.mpr ht1) ht0
    (by ring : (1 - t) + t = 1)
  have heq : (1 - t) • xstar + t • x = xstar + t • (x - xstar) := by module
  rw [heq, smul_eq_mul, smul_eq_mul] at hconv
  have h1 : δ ≤ t * (F x - F xstar) := by nlinarith
  calc R / r * δ ≤ R / r * (t * (F x - F xstar)) :=
        mul_le_mul_of_nonneg_left h1 (div_nonneg hR.le hr.le)
    _ = F x - F xstar := by rw [htdef]; field_simp; ring

/-! ### The proof of Theorem `art:polyhedral` (`local.tex:48-77`) -/

/-- Sharp Taylor bound for a gradient that is `L`-Lipschitz in the Euclidean norm on an open
convex set: $f(y)-f(x)-\nabla f(x)^T(y-x)\le\frac L2\|y-x\|^2$. -/
theorem taylor_upper_of_lipschitz {n : ℕ} {f : Vec n → ℝ} {B : Set (Vec n)}
    (hBc : Convex ℝ B) (hd : ∀ y ∈ B, DifferentiableAt ℝ f y) {L : ℝ}
    (hLip : ∀ y ∈ B, ∀ y' ∈ B, ‖euclideanVector (coordinateGradient f y -
      coordinateGradient f y')‖ ≤ L * ‖euclideanVector (y - y')‖)
    {x y : Vec n} (hx : x ∈ B) (hy : y ∈ B) :
    f y - f x - dot (coordinateGradient f x) (y - x) ≤ L / 2 * sqNorm (y - x) := by
  set h := y - x with hhdef
  set φ : ℝ → ℝ := fun s => f (x + s • h) - s * dot (coordinateGradient f x) h -
    L / 2 * s ^ 2 * sqNorm h with hφ
  have hseg : ∀ s ∈ Icc (0 : ℝ) 1, x + s • h ∈ B := by
    intro s hs
    have hm := hBc hx hy (sub_nonneg.mpr hs.2) hs.1 (by ring : (1 - s) + s = 1)
    have he : (1 - s) • x + s • y = x + s • h := by rw [hhdef]; module
    rwa [he] at hm
  have hderiv : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt φ
      (dot (coordinateGradient f (x + s • h)) h - dot (coordinateGradient f x) h -
        L * s * sqNorm h) s := by
    intro s hs
    have hfd := hasFDerivAt_coordinateGradient (hd _ (hseg s hs))
    have hline : HasDerivAt (fun s : ℝ => x + s • h) h s := by
      simpa using ((hasDerivAt_id s).smul_const h).const_add x
    have h1 := hfd.comp_hasDerivAt s hline
    have h2 := ((hasDerivAt_id s).mul_const (dot (coordinateGradient f x) h))
    have h3 := ((hasDerivAt_pow 2 s).const_mul (L / 2)).mul_const (sqNorm h)
    convert (h1.sub h2).sub h3 using 1
    · simp only [gradientFunctional_apply, id]
      push_cast
      ring
  have hcont : ContinuousOn φ (Icc 0 1) := fun s hs =>
    (hderiv s hs).continuousAt.continuousWithinAt
  have hanti : AntitoneOn φ (Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1) hcont
    · intro s hs
      rw [interior_Icc] at hs
      exact (hderiv s (Ioo_subset_Icc_self hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hsI := Ioo_subset_Icc_self hs
      rw [(hderiv s hsI).deriv]
      have hcs := dot_le_euclid (coordinateGradient f (x + s • h) - coordinateGradient f x) h
      have hl := hLip _ (hseg s hsI) x hx
      have hsh : x + s • h - x = s • h := by abel
      rw [hsh, euclideanVector_smul, norm_smul, Real.norm_of_nonneg hs.1.le] at hl
      have hsq := euclid_norm_sq h
      rw [dot_sub_left] at hcs
      have key : ‖euclideanVector (coordinateGradient f (x + s • h) - coordinateGradient f x)‖ *
          ‖euclideanVector h‖ ≤ L * s * sqNorm h := by
        calc _ ≤ L * (s * ‖euclideanVector h‖) * ‖euclideanVector h‖ :=
              mul_le_mul_of_nonneg_right hl (norm_nonneg _)
          _ = L * s * sqNorm h := by rw [← hsq]; ring
      linarith
  have h01 := hanti (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one) zero_le_one
  simp only [hφ, zero_smul, add_zero, zero_mul, sub_zero, one_smul, one_mul, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, one_pow] at h01
  have hxy : x + h = y := by rw [hhdef]; abel
  rw [hxy] at h01
  linarith

/-- Item `A/local/disp/003` (`paper/sections/local.tex:61-63`), in the proof of Theorem
`art:polyhedral`.

Under the assumptions of Theorem `art:polyhedral` (`positive_partition.tex:1-18`, written out as
in `PositivePartition.polyhedral`), the proof first discards the cells not containing $x_*$ and
shrinks to a common Euclidean ball $B=B_\rho(x_*)\subset U\cap\bigcap_{i:x_*\in P_i}V_i$ that meets
only cells containing $x_*$ (`hdisc`), on which the gradients of the remaining extensions have
one Lipschitz bound $L$ (`hLip`). Let $x\in B$ be a differentiability point of $F$, with
gradient $g=\nabla F(x)$, and $P_i$ a cell containing it. Comparing right derivatives at $\tau=0$
along the inward segment gives
\[ \nabla F(x)^T(x-x_*)=\nabla f_i(x)^T(x-x_*). \]
Here $\nabla f_i(x)$ is `coordinateGradient (f i) x`, the coordinates of the Fréchet
derivative. -/
theorem polyhedral_radial_derivative {n : ℕ} (_hn : 1 ≤ n) (F : Vec n → ℝ)
    (_hF : ConvexOn ℝ univ F) (xstar : Vec n) (_hmin : ∀ x, F xstar ≤ F x)
    (_huniq : ∀ x, F x = F xstar → x = xstar) (U : Set (Vec n)) (_hU : IsOpen U)
    (_hxU : xstar ∈ U) {ι : Type*} [Fintype ι] (m : ι → ℕ) (a : ∀ i, Fin (m i) → Vec n)
    (b : ∀ i, Fin (m i) → ℝ) (P : ι → Set (Vec n))
    (hP : ∀ i, P i = {x | ∀ j, dot (a i j) x ≤ b i j})
    (_hfull : ∀ i, (interior (P i)).Nonempty) (_hcover : U ⊆ ⋃ i, P i)
    (V : ι → Set (Vec n)) (hV : ∀ i, IsOpen (V i)) (_hUV : ∀ i, U ∩ P i ⊆ V i)
    (f : ι → Vec n → ℝ) (hf : ∀ i, CenteredSmoothSublinear.LocallyC11On (V i) (f i))
    (hrep : ∀ i, ∀ x ∈ U ∩ P i, F x = f i x)
    (r : ℝ) (hr : 0 < r) (B : Set (Vec n)) (hB : B = {x | ‖euclideanVector (x - xstar)‖ < r})
    (hBU : B ⊆ U) (hBV : ∀ i, xstar ∈ P i → B ⊆ V i)
    (hdisc : ∀ i, (B ∩ P i).Nonempty → xstar ∈ P i) (L : ℝ) (_hL : 0 ≤ L)
    (_hLip : ∀ i, xstar ∈ P i → ∀ y ∈ B, ∀ y' ∈ B,
      ‖euclideanVector (coordinateGradient (f i) y - coordinateGradient (f i) y')‖ ≤
        L * ‖euclideanVector (y - y')‖)
    (x g : Vec n) (hxB : x ∈ B) (hg : HasFDerivAt F (gradientFunctional g) x) (i : ι)
    (hxi : x ∈ P i) :
    dot g (x - xstar) = dot (coordinateGradient (f i) x) (x - xstar) := by
  have hsP : xstar ∈ P i := hdisc i ⟨x, hxB, hxi⟩
  have hxV : x ∈ V i := hBV i hsP hxB
  have hdiff : DifferentiableAt ℝ (f i) x :=
    ((hf i).1 x hxV).differentiableAt ((hV i).mem_nhds hxV)
  have hBc : Convex ℝ B := hB ▸ (euclid_ball_open_convex xstar r).2
  have hsB : xstar ∈ B := by
    rw [hB, mem_setOf_eq, sub_self]
    simpa [show euclideanVector (0 : Vec n) = 0 from rfl] using hr
  have hPc : Convex ℝ (P i) := by
    rw [hP i]; exact ConvexCellRadial.polyhedron_convex (a i) (b i)
  have h := ConvexCellRadial.radial_derivative_eq hPc hBc hsP hxi hsB hxB
    (fun z hz hzP => hrep i z ⟨hBU hz, hzP⟩) hg hdiff
  rw [h, (hasFDerivAt_coordinateGradient hdiff).fderiv, gradientFunctional_apply]

/-- Item `A/local/disp/004` (`paper/sections/local.tex:66-70`), in the proof of Theorem
`art:polyhedral`.

Under the assumptions of display `disp/003` (the theorem's hypotheses, the ball $B=B_\rho(x_*)$, the
common Lipschitz bound $L$ of the remaining extension gradients, a differentiability point
$x\in B$ of $F$ with gradient $g$, and a cell $P_i\ni x$), with $r_x=x-x_*$, the smooth Taylor
estimate along the same segment gives, for $0\le\tau\le1$,
\[ 0\le F(x-\tau r_x)-F(x)+\tau\nabla F(x)^Tr_x\le\tfrac12L\tau^2\norm{r_x}^2
   \le\tfrac12L\rho^2\tau^2. \]
The first inequality uses convexity of $F$, not convexity of the extension. -/
theorem polyhedral_inward_taylor {n : ℕ} (_hn : 1 ≤ n) (F : Vec n → ℝ)
    (hF : ConvexOn ℝ univ F) (xstar : Vec n) (_hmin : ∀ x, F xstar ≤ F x)
    (_huniq : ∀ x, F x = F xstar → x = xstar) (U : Set (Vec n)) (_hU : IsOpen U)
    (_hxU : xstar ∈ U) {ι : Type*} [Fintype ι] (m : ι → ℕ) (a : ∀ i, Fin (m i) → Vec n)
    (b : ∀ i, Fin (m i) → ℝ) (P : ι → Set (Vec n))
    (hP : ∀ i, P i = {x | ∀ j, dot (a i j) x ≤ b i j})
    (_hfull : ∀ i, (interior (P i)).Nonempty) (_hcover : U ⊆ ⋃ i, P i)
    (V : ι → Set (Vec n)) (hV : ∀ i, IsOpen (V i)) (_hUV : ∀ i, U ∩ P i ⊆ V i)
    (f : ι → Vec n → ℝ) (hf : ∀ i, CenteredSmoothSublinear.LocallyC11On (V i) (f i))
    (hrep : ∀ i, ∀ x ∈ U ∩ P i, F x = f i x)
    (r : ℝ) (hr : 0 < r) (B : Set (Vec n)) (hB : B = {x | ‖euclideanVector (x - xstar)‖ < r})
    (hBU : B ⊆ U) (hBV : ∀ i, xstar ∈ P i → B ⊆ V i)
    (hdisc : ∀ i, (B ∩ P i).Nonempty → xstar ∈ P i) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ i, xstar ∈ P i → ∀ y ∈ B, ∀ y' ∈ B,
      ‖euclideanVector (coordinateGradient (f i) y - coordinateGradient (f i) y')‖ ≤
        L * ‖euclideanVector (y - y')‖)
    (x g : Vec n) (hxB : x ∈ B) (hg : HasFDerivAt F (gradientFunctional g) x) (i : ι)
    (hxi : x ∈ P i) (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    0 ≤ F (x - τ • (x - xstar)) - F x + τ * dot g (x - xstar) ∧
      F (x - τ • (x - xstar)) - F x + τ * dot g (x - xstar) ≤
        1 / 2 * L * τ ^ 2 * sqNorm (x - xstar) ∧
      1 / 2 * L * τ ^ 2 * sqNorm (x - xstar) ≤ 1 / 2 * L * r ^ 2 * τ ^ 2 := by
  have hsP : xstar ∈ P i := hdisc i ⟨x, hxB, hxi⟩
  have hBc : Convex ℝ B := hB ▸ (euclid_ball_open_convex xstar r).2
  have hsB : xstar ∈ B := by
    rw [hB, mem_setOf_eq, sub_self]
    simpa [show euclideanVector (0 : Vec n) = 0 from rfl] using hr
  have hPc : Convex ℝ (P i) := by
    rw [hP i]; exact ConvexCellRadial.polyhedron_convex (a i) (b i)
  set y := x - τ • (x - xstar) with hydef
  have hyconv : y = (1 - τ) • x + τ • xstar := by rw [hydef]; module
  have hyB : y ∈ B := by
    rw [hyconv]; exact hBc hxB hsB (sub_nonneg.mpr hτ1) hτ0 (by ring)
  have hyP : y ∈ P i := by
    rw [hyconv]; exact hPc hxi hsP (sub_nonneg.mpr hτ1) hτ0 (by ring)
  have hrad := polyhedral_radial_derivative _hn F hF xstar _hmin _huniq U _hU _hxU m a b P hP
    _hfull _hcover V hV _hUV f hf hrep r hr B hB hBU hBV hdisc L hL hLip x g hxB hg i hxi
  have hyx : y - x = -τ • (x - xstar) := by rw [hydef]; module
  refine ⟨?_, ?_, ?_⟩
  · have hs := convex_supporting_inequality hF hg y
    rw [hyx, dot_smul_right] at hs
    linarith
  · have hd : ∀ z ∈ B, DifferentiableAt ℝ (f i) z := fun z hz =>
      ((hf i).1 z (hBV i hsP hz)).differentiableAt ((hV i).mem_nhds (hBV i hsP hz))
    have ht := taylor_upper_of_lipschitz hBc hd (hLip i hsP) hxB hyB
    rw [hyx, dot_smul_right, CertificateGeometry.sqNorm_smul] at ht
    rw [hrep i y ⟨hBU hyB, hyP⟩, hrep i x ⟨hBU hxB, hxi⟩, hrad]
    nlinarith
  · have hxr : sqNorm (x - xstar) ≤ r ^ 2 := by
      rw [← euclid_norm_sq]
      have h0 : ‖euclideanVector (x - xstar)‖ < r := by rw [hB] at hxB; exact hxB
      nlinarith [norm_nonneg (euclideanVector (x - xstar))]
    have hc : 0 ≤ 1 / 2 * L * τ ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hxr hc]

/-- Item `A/local/prose/005` (`paper/sections/local.tex:38-42`), anchor "A finite local
partition controls which formulas", stated under the assumptions of Theorem `art:polyhedral`.

"Near $x_*$ only cells containing $x_*$ occur: the finitely many closed cells that miss $x_*$
avoid a ball around it. Convexity of a cell then keeps the entire inward segment in that same cell. Its smooth extension
yields quadratic model accuracy even if the full gradient jumps across cell boundaries."
Stated as: there is a ball $B_\rho(x_*)\subset U$ meeting only cells that contain $x_*$; for a
cell containing $x$ and $x_*$ the whole inward segment $x-\tau(x-x_*)$, $0\le\tau\le1$, stays in
it; and the inward model condition \eqref{art:inward-condition}
(`RadialCertificate.HasInwardTaylorBounds F K xstar`) holds on every compact $K$ in that ball. -/
theorem polyhedral_local_partition {n : ℕ} (_hn : 1 ≤ n) (F : Vec n → ℝ)
    (hF : ConvexOn ℝ univ F) (xstar : Vec n) (_hmin : ∀ x, F xstar ≤ F x)
    (_huniq : ∀ x, F x = F xstar → x = xstar) (U : Set (Vec n)) (hU : IsOpen U)
    (hxU : xstar ∈ U) {ι : Type*} [Fintype ι] (m : ι → ℕ) (a : ∀ i, Fin (m i) → Vec n)
    (b : ∀ i, Fin (m i) → ℝ) (P : ι → Set (Vec n))
    (hP : ∀ i, P i = {x | ∀ j, dot (a i j) x ≤ b i j})
    (_hfull : ∀ i, (interior (P i)).Nonempty) (hcover : U ⊆ ⋃ i, P i)
    (V : ι → Set (Vec n)) (hV : ∀ i, IsOpen (V i)) (hUV : ∀ i, U ∩ P i ⊆ V i)
    (f : ι → Vec n → ℝ) (hf : ∀ i, CenteredSmoothSublinear.LocallyC11On (V i) (f i))
    (hrep : ∀ i, ∀ x ∈ U ∩ P i, F x = f i x) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball xstar ρ ⊆ U ∧
      (∀ i, (Metric.ball xstar ρ ∩ P i).Nonempty → xstar ∈ P i) ∧
      (∀ i, ∀ x ∈ P i, xstar ∈ P i → ∀ τ ∈ Icc (0 : ℝ) 1, x - τ • (x - xstar) ∈ P i) ∧
      ∀ K : Set (Vec n), IsCompact K → K ⊆ Metric.ball xstar ρ →
        RadialCertificate.HasInwardTaylorBounds F K xstar := by
  have hPc : ∀ i, IsClosed (P i) := fun i => by
    rw [hP i]; exact ConvexCellRadial.polyhedron_closed (a i) (b i)
  have hPv : ∀ i, Convex ℝ (P i) := fun i => by
    rw [hP i]; exact ConvexCellRadial.polyhedron_convex (a i) (b i)
  obtain ⟨ε₁, hε₁, hBU, hinc, _⟩ :=
    ConvexCellRadial.incident_neighborhood P V hPc hV hU hxU hUV
  obtain ⟨ε₂, hε₂, hIR⟩ := ConvexCellRadial.local_cells_inward hF P V f hPc hPv hV hf hU hxU hUV
    (fun x hx => mem_iUnion.mp (hcover hx)) (fun i x hx hxi => hrep i x ⟨hx, hxi⟩)
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂,
    (Metric.ball_subset_ball (min_le_left _ _)).trans hBU, ?_, ?_, ?_⟩
  · rintro i ⟨x, hx, hxi⟩
    exact hinc i x (Metric.ball_subset_ball (min_le_left _ _) hx) hxi
  · intro i x hx hs τ hτ
    have he : x - τ • (x - xstar) = (1 - τ) • x + τ • xstar := by module
    rw [he]
    exact hPv i hx hs (sub_nonneg.mpr hτ.2) hτ.1 (by ring)
  · intro K hK hKB
    exact hIR K hK (hKB.trans (Metric.ball_subset_ball (min_le_right _ _)))

/-! ### Corollary `art:plq` -/

/-- A quadratic polynomial in the library's form `ConvexCellRadial.quadratic Q c d` is
$x^TQx+c^Tx+d$. -/
theorem quadratic_eq {n : ℕ} (Q : Mat n) (c : Vec n) (d : ℝ) (x : Vec n) :
    ConvexCellRadial.quadratic Q c d x = dot x (Q *ᵥ x) + dot c x + d := by
  simp only [ConvexCellRadial.quadratic, dot, Matrix.mulVec, dotProduct, Finset.mul_sum]
  congr 2
  · apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring

/-- Item `A/local/corollary/art:plq` (`paper/sections/local.tex:79-84`), Corollary `art:plq`,
first sentence.

"A finite convex piecewise linear-quadratic objective with a unique minimizer has the local
convergence property of Theorem `art:polyhedral`." Piecewise linear-quadratic is the meaning fixed
in the proof (`local.tex:86-87`): a representation $F=x^TQ_ix+c_i^Tx+d_i$ on each cell of a
finite cover of $\R^n$ by closed full-dimensional polyhedral cells $P_i$. Since the
representation is global, the property holds for every open neighborhood $U$ of $x_*$: some
$\varepsilon>0$, chosen before the run, gives $x_k\in U$, $F(x_k)\to F(x_*)$, $x_k\to x_*$ for
every admissible run with $F(x_0)\le F(x_*)+\varepsilon$. -/
theorem plq {n : ℕ} (F : Vec n → ℝ) (hF : ConvexOn ℝ univ F) (xstar : Vec n)
    (hmin : ∀ x, F xstar ≤ F x) (huniq : ∀ x, F x = F xstar → x = xstar)
    {ι : Type*} [Fintype ι] (m : ι → ℕ) (a : ∀ i, Fin (m i) → Vec n) (b : ∀ i, Fin (m i) → ℝ)
    (P : ι → Set (Vec n)) (hP : ∀ i, P i = {x | ∀ j, dot (a i j) x ≤ b i j})
    (_hfull : ∀ i, (interior (P i)).Nonempty) (hcover : ∀ x, ∃ i, x ∈ P i)
    (Q : ι → Mat n) (c : ι → Vec n) (d : ι → ℝ)
    (hrep : ∀ i, ∀ x ∈ P i, F x = dot x (Q i *ᵥ x) + dot (c i) x + d i) :
    ∀ U : Set (Vec n), IsOpen U → xstar ∈ U →
      ∃ ε : ℝ, 0 < ε ∧ ∀ R : AdmissibleBFGSRun n F, F (R.x 0) ≤ F xstar + ε →
        (∀ k, R.x k ∈ U) ∧ Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) ∧
          Tendsto R.x atTop (𝓝 xstar) := by
  intro U hU hxU
  have hPe : ∀ i, P i = ConvexCellRadial.polyhedron (a i) (b i) := hP
  exact ConvexCellRadial.piecewise_quadratic_basin hF a b Q c d hU hxU
    (fun x _ => by obtain ⟨i, hi⟩ := hcover x; exact ⟨i, by rw [← hPe i]; exact hi⟩)
    (fun i x _ hx => by rw [quadratic_eq]; exact hrep i x (by rw [hPe i]; exact hx)) hmin huniq

/-- Item `A/local/corollary/art:plq` (`paper/sections/local.tex:79-84`), Corollary `art:plq`,
second sentence.

"The same holds for a convex locally $C^{1,1}$ loss plus a finite convex piecewise
linear-quadratic regularizer, provided the sum has a unique minimizer." Here
`loss` is convex and locally $C^{1,1}$ on $\R^n$, `reg` is convex with a quadratic formula on each
cell of a finite cover of $\R^n$ by closed full-dimensional polyhedra, and $F$ = `loss + reg`
has the unique minimizer $x_*$. -/
theorem plq_loss_regularizer {n : ℕ} (loss reg F : Vec n → ℝ) (hloss : ConvexOn ℝ univ loss)
    (hloss_s : CenteredSmoothSublinear.LocallyC11On univ loss) (hreg : ConvexOn ℝ univ reg)
    {ι : Type*} [Fintype ι] (m : ι → ℕ) (a : ∀ i, Fin (m i) → Vec n) (b : ∀ i, Fin (m i) → ℝ)
    (P : ι → Set (Vec n)) (hP : ∀ i, P i = {x | ∀ j, dot (a i j) x ≤ b i j})
    (_hfull : ∀ i, (interior (P i)).Nonempty) (hcover : ∀ x, ∃ i, x ∈ P i)
    (Q : ι → Mat n) (c : ι → Vec n) (d : ι → ℝ)
    (hrep : ∀ i, ∀ x ∈ P i, reg x = dot x (Q i *ᵥ x) + dot (c i) x + d i)
    (hFdef : ∀ x, F x = loss x + reg x) (xstar : Vec n) (hmin : ∀ x, F xstar ≤ F x)
    (huniq : ∀ x, F x = F xstar → x = xstar) :
    ∀ U : Set (Vec n), IsOpen U → xstar ∈ U →
      ∃ ε : ℝ, 0 < ε ∧ ∀ R : AdmissibleBFGSRun n F, F (R.x 0) ≤ F xstar + ε →
        (∀ k, R.x k ∈ U) ∧ Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) ∧
          Tendsto R.x atTop (𝓝 xstar) := by
  intro U hU hxU
  have hPe : ∀ i, P i = ConvexCellRadial.polyhedron (a i) (b i) := hP
  have hF : ConvexOn ℝ univ F := (hloss.add hreg).congr (fun x _ => (hFdef x).symm)
  exact ConvexCellRadial.smooth_plus_piecewise_quadratic_basin hF a b Q c d hU hxU
    ⟨hloss_s.1.mono (subset_univ _), hloss_s.2.mono (subset_univ _)⟩
    (fun x _ => by obtain ⟨i, hi⟩ := hcover x; exact ⟨i, by rw [← hPe i]; exact hi⟩)
    (fun i x _ hx => by
      rw [hFdef, quadratic_eq]; exact congrArg _ (hrep i x (by rw [hPe i]; exact hx)))
    hmin huniq


/-! ### The deductions after Corollary `art:plq` (`local.tex:92-100`) -/

/-- The interior of a finite union of closed sets with empty interiors is empty. -/
theorem interior_biUnion_closed_empty {X : Type*} [TopologicalSpace X] {ι : Type*}
    (s : Finset ι) (C : ι → Set X) (hc : ∀ i ∈ s, IsClosed (C i))
    (he : ∀ i ∈ s, interior (C i) = ∅) : interior (⋃ i ∈ s, C i) = ∅ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.set_biUnion_insert, union_comm,
      interior_union_isClosed_of_interior_empty
        (isClosed_biUnion_finset fun i hi => hc i (Finset.mem_insert_of_mem hi))
        (he j (Finset.mem_insert_self j s))]
    exact ih (fun i hi => hc i (Finset.mem_insert_of_mem hi))
      (fun i hi => he i (Finset.mem_insert_of_mem hi))

/-- An affine function vanishing on a nonempty open set is zero. -/
theorem affine_eq_zero_of_open {n : ℕ} (v : Vec n) (c : ℝ) {O : Set (Vec n)} (hO : IsOpen O)
    {z : Vec n} (hz : z ∈ O) (h : ∀ x ∈ O, dot v x + c = 0) : v = 0 ∧ c = 0 := by
  classical
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hO z hz
  have hv : v = 0 := by
    ext i
    have hmem : z + Pi.single i (ε / 2) ∈ O := hball (by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Pi.norm_single,
        Real.norm_of_nonneg (by positivity)]
      linarith)
    have h1 := h _ hmem
    have h0 := h z hz
    have hd : dot v (z + Pi.single i (ε / 2)) = dot v z + v i * (ε / 2) := by
      simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_eq_single i (fun k _ hk => by simp [Pi.single_apply, hk])
        (fun h => absurd (Finset.mem_univ i) h)]
      simp
    rw [hd] at h1
    have h2 : v i * (ε / 2) = 0 := by linarith
    simpa [hε.ne'] using h2
  refine ⟨hv, ?_⟩
  have h0 := h z hz
  simpa [hv, dot] using h0

/-- Item `A/local/prose/007` (`paper/sections/local.tex:92-94`), anchor "In particular, a finite
convex polyhedral penalty,": a finite convex polyhedral penalty is piecewise affine on a finite
polyhedral partition.

A finite convex polyhedral penalty is a finite maximum of affine functions,
$\varphi(x)=\max_j(p_j^Tx+q_j)$. With the closed polyhedral cells
$C_j=\{x:p_{j'}^Tx+q_{j'}\le p_j^Tx+q_j\ \forall j'\}$, written as affine inequalities, $\varphi$ is
convex and affine on each cell ($\varphi=p_j^Tx+q_j$ on $C_j$), and some subfamily
$\{C_j\}_{j\in S}$ is a partition of $\R^n$ into full-dimensional cells: they cover $\R^n$ and have
pairwise disjoint interiors. -/
theorem polyhedral_penalty_partition {n k : ℕ} (p : Fin k → Vec n) (q : Fin k → ℝ)
    (φ : Vec n → ℝ) (hφ : ∀ x, IsGreatest (Set.range fun j => dot (p j) x + q j) (φ x))
    (C : Fin k → Set (Vec n)) (hC : ∀ j, C j = {x | ∀ j', dot (p j' - p j) x ≤ q j - q j'}) :
    ConvexOn ℝ univ φ ∧ (∀ j, ∀ x ∈ C j, φ x = dot (p j) x + q j) ∧
      ∃ S : Finset (Fin k), (∀ j ∈ S, (interior (C j)).Nonempty) ∧ (∀ x, ∃ j ∈ S, x ∈ C j) ∧
        ∀ j ∈ S, ∀ j' ∈ S, j ≠ j' → Disjoint (interior (C j)) (interior (C j')) := by
  classical
  have hmemC : ∀ j x, x ∈ C j ↔ ∀ j', dot (p j') x + q j' ≤ dot (p j) x + q j := by
    intro j x
    rw [hC j, mem_setOf_eq]
    constructor
    · intro h j'
      have := h j'
      rw [dot_sub_left] at this
      linarith
    · intro h j'
      have := h j'
      rw [dot_sub_left]
      linarith
  have hpiece : ∀ j, ∀ x ∈ C j, φ x = dot (p j) x + q j := by
    intro j x hx
    refine (hφ x).unique ⟨⟨j, rfl⟩, ?_⟩
    rintro _ ⟨j', rfl⟩
    exact (hmemC j x).mp hx j'
  have hcov : ∀ x, ∃ j, x ∈ C j := by
    intro x
    obtain ⟨j, hj⟩ := (hφ x).1
    refine ⟨j, (hmemC j x).mpr fun j' => ?_⟩
    have hj' : dot (p j) x + q j = φ x := hj
    rw [hj']
    exact (hφ x).2 ⟨j', rfl⟩
  have hclosed : ∀ j, IsClosed (C j) := fun j => by
    rw [hC j]
    exact ConvexCellRadial.polyhedron_closed (fun j' => p j' - p j) (fun j' => q j - q j')
  have hconv : ConvexOn ℝ univ φ := by
    refine ⟨convex_univ, fun x _ y _ s t hs ht hst => ?_⟩
    obtain ⟨j, hj⟩ := (hφ (s • x + t • y)).1
    have hj' : dot (p j) (s • x + t • y) + q j = φ (s • x + t • y) := hj
    rw [← hj']
    have hx : dot (p j) x + q j ≤ φ x := (hφ x).2 ⟨j, rfl⟩
    have hy : dot (p j) y + q j ≤ φ y := (hφ y).2 ⟨j, rfl⟩
    have hlin : dot (p j) (s • x + t • y) = s * dot (p j) x + t * dot (p j) y := by
      show (p j) ⬝ᵥ (s • x + t • y) = s * ((p j) ⬝ᵥ x) + t * ((p j) ⬝ᵥ y)
      rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    rw [hlin, smul_eq_mul, smul_eq_mul]
    have hq : q j = s * q j + t * q j := by rw [← add_mul, hst, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left hx hs, mul_le_mul_of_nonneg_left hy ht]
  -- the full-dimensional cells still cover
  set T := Finset.univ.filter (fun j => (interior (C j)).Nonempty) with hT
  have hcovT : ∀ x, ∃ j ∈ T, x ∈ C j := by
    intro x
    by_contra hno
    push_neg at hno
    have hAc : IsClosed (⋃ j ∈ T, C j) := isClosed_biUnion_finset fun j _ => hclosed j
    have hxA : x ∉ ⋃ j ∈ T, C j := by
      simp only [mem_iUnion]
      rintro ⟨j, hj, hx⟩
      exact hno j hj hx
    have hsub : (⋃ j ∈ T, C j)ᶜ ⊆
        ⋃ j ∈ Finset.univ.filter (fun j => ¬ (interior (C j)).Nonempty), C j := by
      intro y hy
      obtain ⟨j, hj⟩ := hcov y
      by_cases hjT : (interior (C j)).Nonempty
      · exact absurd (mem_iUnion₂.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjT⟩, hj⟩) hy
      · exact mem_iUnion₂.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjT⟩, hj⟩
    have hint := interior_biUnion_closed_empty (Finset.univ.filter
      (fun j => ¬ (interior (C j)).Nonempty)) C (fun j _ => hclosed j)
      (fun j hj => Set.not_nonempty_iff_eq_empty.mp (Finset.mem_filter.mp hj).2)
    have hxi := interior_mono hsub (mem_interior_iff_mem_nhds.mpr (hAc.isOpen_compl.mem_nhds hxA))
    rw [hint] at hxi
    exact hxi
  -- one representative per distinct affine piece
  have hkeyC : ∀ j j', p j = p j' → q j = q j' → C j = C j' := by
    intro j j' hp hq
    rw [hC j, hC j', hp, hq]
  set S := T.filter (fun j => ∀ j' ∈ T, p j' = p j → q j' = q j → j ≤ j') with hS
  have hrepr : ∀ j ∈ T, ∃ j₀ ∈ S, C j₀ = C j := by
    intro j hj
    set E := T.filter (fun j' => p j' = p j ∧ q j' = q j) with hE
    have hEne : E.Nonempty := ⟨j, Finset.mem_filter.mpr ⟨hj, rfl, rfl⟩⟩
    have hj₀E : E.min' hEne ∈ E := E.min'_mem hEne
    obtain ⟨hj₀T, hp₀, hq₀⟩ := Finset.mem_filter.mp hj₀E
    refine ⟨E.min' hEne, Finset.mem_filter.mpr ⟨hj₀T, fun j' hj'T hp' hq' =>
      E.min'_le j' (Finset.mem_filter.mpr ⟨hj'T, hp'.trans hp₀, hq'.trans hq₀⟩)⟩,
      hkeyC _ _ hp₀ hq₀⟩
  refine ⟨hconv, hpiece, S, ?_, ?_, ?_⟩
  · intro j hj
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2
  · intro x
    obtain ⟨j, hjT, hx⟩ := hcovT x
    obtain ⟨j₀, hj₀, hC₀⟩ := hrepr j hjT
    exact ⟨j₀, hj₀, hC₀ ▸ hx⟩
  · intro j hj j' hj' hne
    rw [Set.disjoint_left]
    intro z hz hz'
    have hO : IsOpen (interior (C j) ∩ interior (C j')) := isOpen_interior.inter isOpen_interior
    have hzero := affine_eq_zero_of_open (p j - p j') (q j - q j') hO ⟨hz, hz'⟩ (by
      intro x hx
      have h1 := hpiece j x (interior_subset hx.1)
      have h2 := hpiece j' x (interior_subset hx.2)
      rw [dot_sub_left]
      linarith)
    have hpj : p j = p j' := sub_eq_zero.mp hzero.1
    have hqj : q j = q j' := sub_eq_zero.mp hzero.2
    have hjT := (Finset.mem_filter.mp hj).1
    have hj'T := (Finset.mem_filter.mp hj').1
    have h1 := (Finset.mem_filter.mp hj).2 j' hj'T hpj.symm hqj.symm
    have h2 := (Finset.mem_filter.mp hj').2 j hjT hpj hqj
    exact hne (le_antisymm h1 h2)

/-- `dot` is linear in its first argument over a finite sum. -/
theorem dot_sum_smul {n : ℕ} {ι : Type*} [Fintype ι] (s : ι → ℝ) (u : ι → Vec n) (x : Vec n) :
    dot (∑ i, s i • u i) x = ∑ i, s i * dot (u i) x := by
  simp only [dot, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Item `A/local/prose/007` (`paper/sections/local.tex:92-94`), anchor "In particular, a finite
convex polyhedral penalty,": "such as a finite sum of absolute-value or hinge terms".

A finite sum $\sum_j|a_j^Tx-b_j|+\sum_k\max\{0,c_k^Tx-e_k\}$ of absolute-value and hinge terms is
a finite convex polyhedral penalty: it is the maximum of finitely many affine functions (one for
each choice of slopes), so `polyhedral_penalty_partition` applies to it. -/
theorem abs_hinge_sum_polyhedral {n : ℕ} {J K : Type*} [Fintype J] [Fintype K]
    (a : J → Vec n) (b : J → ℝ) (c : K → Vec n) (e : K → ℝ) (φ : Vec n → ℝ)
    (hφ : ∀ x, φ x = ∑ j, |dot (a j) x - b j| + ∑ k, max 0 (dot (c k) x - e k)) :
    ∃ (N : ℕ) (p : Fin N → Vec n) (q : Fin N → ℝ),
      ∀ x, IsGreatest (Set.range fun j => dot (p j) x + q j) (φ x) := by
  classical
  let P : J ⊕ K → AffineKinks.Kink n := fun i =>
    Sum.elim (fun j => AffineKinks.Kink.absolute (a j) (b j))
      (fun k => AffineKinks.Kink.hinge (c k) (e k)) i
  have hpen : ∀ x, φ x = AffineKinks.penalty P x := by
    intro x
    rw [hφ, AffineKinks.penalty, Fintype.sum_sum_type]
    simp [P, AffineKinks.Kink.absolute_value, AffineKinks.Kink.hinge_value]
  let slope : (J ⊕ K → Bool) → J ⊕ K → ℝ := fun σ i => if σ i then (P i).hi else (P i).lo
  let eq := Fintype.equivFin (J ⊕ K → Bool)
  have hval : ∀ (σ : J ⊕ K → Bool) (x : Vec n),
      dot (∑ i, slope σ i • (P i).a) x + -∑ i, slope σ i * (P i).b = AffineKinks.piece P σ x := by
    intro σ x
    rw [dot_sum_smul, AffineKinks.piece]
    simp only [AffineKinks.Kink.residual, mul_sub, Finset.sum_sub_distrib, slope]
    ring
  refine ⟨Fintype.card (J ⊕ K → Bool), fun j => ∑ i, slope (eq.symm j) i • (P i).a,
    fun j => -∑ i, slope (eq.symm j) i * (P i).b, fun x => ⟨?_, ?_⟩⟩
  · obtain ⟨σ, hσ⟩ := AffineKinks.cells_cover P x
    refine ⟨eq σ, ?_⟩
    simp only [Equiv.symm_apply_apply]
    rw [hval, hpen, AffineKinks.penalty_eq_piece P σ hσ]
  · rintro _ ⟨j, rfl⟩
    simp only
    rw [hval, hpen]
    apply Finset.sum_le_sum
    intro i _
    simp only [AffineKinks.Kink.value]
    split_ifs
    · exact le_max_right _ _
    · exact le_max_left _ _

/-- Item `A/local/prose/008` (`paper/sections/local.tex:94-96`), anchor "It therefore falls under
this corollary".

A finite convex polyhedral penalty $\varphi=\max_j(p_j^Tx+q_j)$ added to a convex, locally
$C^{1,1}$ loss falls under Corollary `art:plq` (second sentence), under the stated uniqueness
assumption: the conclusion of `plq_loss_regularizer`, derived by applying that theorem to the
full-dimensional cells of `polyhedral_penalty_partition` (affine pieces, $Q_i=0$). -/
theorem loss_plus_polyhedral_penalty {n k : ℕ} (loss φ F : Vec n → ℝ)
    (hloss : ConvexOn ℝ univ loss) (hloss_s : CenteredSmoothSublinear.LocallyC11On univ loss)
    (p : Fin k → Vec n) (q : Fin k → ℝ)
    (hφ : ∀ x, IsGreatest (Set.range fun j => dot (p j) x + q j) (φ x))
    (hFdef : ∀ x, F x = loss x + φ x) (xstar : Vec n) (hmin : ∀ x, F xstar ≤ F x)
    (huniq : ∀ x, F x = F xstar → x = xstar) :
    ∀ U : Set (Vec n), IsOpen U → xstar ∈ U →
      ∃ ε : ℝ, 0 < ε ∧ ∀ R : AdmissibleBFGSRun n F, F (R.x 0) ≤ F xstar + ε →
        (∀ k, R.x k ∈ U) ∧ Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) ∧
          Tendsto R.x atTop (𝓝 xstar) := by
  classical
  set C : Fin k → Set (Vec n) := fun j => {x | ∀ j', dot (p j' - p j) x ≤ q j - q j'} with hCdef
  obtain ⟨hφc, hpiece, S, hfull, hcov, _⟩ := polyhedral_penalty_partition p q φ hφ C (fun _ => rfl)
  exact plq_loss_regularizer loss φ F hloss hloss_s hφc (ι := S) (fun _ => k)
    (fun j j' => p j' - p j) (fun j j' => q j - q j') (fun j => C j) (fun _ => rfl)
    (fun j => hfull j j.2) (fun x => by obtain ⟨j, hj, hx⟩ := hcov x; exact ⟨⟨j, hj⟩, hx⟩)
    (fun _ => 0) (fun j => p j) (fun j => q j)
    (fun j x hx => by rw [hpiece j x hx]; simp [dot]) hFdef xstar hmin huniq

/-- Item `A/local/prose/010` (`paper/sections/local.tex:97-98`), anchor "A finite maximum of
arbitrary quadratic formulas"; and Item `A/local/prose/044` (`paper/sections/local.tex:441-442`),
anchor "a replacement by polyhedral cells".

The finite maximum of the three quadratic formulas of Theorem `art:nonradial-example` admits no
representation as in Theorem `art:polyhedral` on any open neighborhood $U$ of its minimizer $0$:
there are no finitely many polyhedra $P_i$ covering $U$, open $V_i\supset U\cap P_i$ and
$f_i\in C^{1,1}_{\rm loc}(V_i)$ with $F=f_i$ on $U\cap P_i$ (not even if lower-dimensional
cells are allowed). Hence this finite maximum of quadratics is not covered by Theorem
`art:polyhedral` or Corollary `art:plq`. Proof: such a representation gives the inward condition
on a compact ball around $0$ (`ConvexCellRadial.local_cells_inward`), hence the radial secant
condition there (`RadialCertificate.radial_of_inward_on_compact`), which fails on every
neighborhood of $0$ (`PlanarQuadraticExample.not_radial_secant_on_neighborhood`). -/
theorem quadratic_max_no_polyhedral_cells (F : Vec 2 → ℝ)
    (hF : ∀ x : Vec 2, F x = max (x 0 + x 0 ^ 2 + x 1 ^ 2 / 2)
      (max (x 1 + x 0 ^ 2 / 2 + 3 * x 1 ^ 2 / 2) (-x 0 - x 1 + 3 * x 0 ^ 2 / 2 + x 1 ^ 2))) :
    ¬ ∃ (U : Set (Vec 2)) (N : ℕ) (m : Fin N → ℕ) (a : ∀ i, Fin (m i) → Vec 2)
        (b : ∀ i, Fin (m i) → ℝ) (V : Fin N → Set (Vec 2)) (f : Fin N → Vec 2 → ℝ),
      IsOpen U ∧ (0 : Vec 2) ∈ U ∧ U ⊆ ⋃ i, {x | ∀ j, dot (a i j) x ≤ b i j} ∧
        (∀ i, IsOpen (V i)) ∧ (∀ i, U ∩ {x | ∀ j, dot (a i j) x ≤ b i j} ⊆ V i) ∧
        (∀ i, CenteredSmoothSublinear.LocallyC11On (V i) (f i)) ∧
        ∀ i, ∀ x ∈ U ∩ {x | ∀ j, dot (a i j) x ≤ b i j}, F x = f i x := by
  have hFe : F = PlanarQuadraticExample.objective := by
    funext x
    rw [hF x]
    simp [PlanarQuadraticExample.objective, PlanarQuadraticExample.branch]
  subst hFe
  rintro ⟨U, N, m, a, b, V, f, hU, h0, hcov, hV, hUV, hf, hrep⟩
  obtain ⟨ε, hε, hIR⟩ := ConvexCellRadial.local_cells_inward
    PlanarQuadraticExample.objective_convex (fun i => ConvexCellRadial.polyhedron (a i) (b i)) V f
    (fun i => ConvexCellRadial.polyhedron_closed (a i) (b i))
    (fun i => ConvexCellRadial.polyhedron_convex (a i) (b i)) hV hf hU h0 hUV
    (fun x hx => mem_iUnion.mp (hcov hx)) (fun i x hx hxi => hrep i x ⟨hx, hxi⟩)
  have hK : IsCompact (Metric.closedBall (0 : Vec 2) (ε / 2)) := isCompact_closedBall _ _
  have hKB : Metric.closedBall (0 : Vec 2) (ε / 2) ⊆ Metric.ball 0 ε :=
    Metric.closedBall_subset_ball (by linarith)
  exact PlanarQuadraticExample.not_radial_secant_on_neighborhood
    (Metric.closedBall_mem_nhds 0 (by linarith : (0 : ℝ) < ε / 2))
    (RadialCertificate.radial_of_inward_on_compact PlanarQuadraticExample.objective_convex hK 0
      (hIR _ hK hKB))

/-! ### Corollary `art:local-centered` and its two examples -/

/-- Item `A/local/corollary/art:local-centered` (`paper/sections/local.tex:102-109`), Corollary
`art:local-centered`.

If the representation and smoothness assumptions of Theorem `art:centered` hold on a neighborhood
of a unique minimizer $x_*$ -- an open convex set $U\ni x_*$, $\psi$ convex and locally
$C^{1,1}$ on $U$, $\gamma:\R^n\to\R$ finite, convex and positively homogeneous of degree one, and
$F(x)=\psi(x)+\gamma(x-x_*)$ on $U$ -- then some $\varepsilon>0$, chosen from the objective alone,
has the following property: every admissible run starting with $F(x_0)\le F(x_*)+\varepsilon$
stays in that neighborhood and converges to $x_*$ in value and iterates.
(`Homogeneous.PositiveDegreeOne γ` is `∀ t ≥ 0, ∀ x, γ (t • x) = t * γ x`.) -/
theorem local_centered {n : ℕ} (F ψ γ : Vec n → ℝ) (hF : ConvexOn ℝ univ F) (xstar : Vec n)
    (hmin : ∀ x, F xstar ≤ F x) (huniq : ∀ x, F x = F xstar → x = xstar)
    (U : Set (Vec n)) (hU : IsOpen U) (_hUc : Convex ℝ U) (hxU : xstar ∈ U)
    (hψ : ConvexOn ℝ U ψ) (hψs : CenteredSmoothSublinear.LocallyC11On U ψ)
    (hγ : ConvexOn ℝ univ γ) (hγh : Homogeneous.PositiveDegreeOne γ)
    (hrep : ∀ x ∈ U, F x = ψ x + γ (x - xstar)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ R : AdmissibleBFGSRun n F, F (R.x 0) ≤ F xstar + ε →
      (∀ k, R.x k ∈ U) ∧ Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) ∧
        Tendsto R.x atTop (𝓝 xstar) :=
  CenteredSmoothSublinear.local_centered_basin hF xstar hmin huniq hU hxU hψ hψs hγ hγh hrep

/-- A finite sum of convex functions is convex. -/
theorem convexOn_finset_sum {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Vec n → ℝ)
    (hf : ∀ i ∈ s, ConvexOn ℝ univ (f i)) : ConvexOn ℝ univ (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (convexOn_const (0 : ℝ) convex_univ : ConvexOn ℝ univ fun _ : Vec n => (0 : ℝ))
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact (hf j (Finset.mem_insert_self j s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- $x\mapsto\|Ax-b\|^2$ is convex. -/
theorem sqNorm_affine_convex {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Vec m) :
    ConvexOn ℝ univ (fun x : Vec n => sqNorm (A *ᵥ x - b)) := by
  refine ⟨convex_univ, fun x _ y _ s t hs ht hst => ?_⟩
  have he : A *ᵥ (s • x + t • y) - b = s • (A *ᵥ x - b) + t • (A *ᵥ y - b) := by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
    calc s • A *ᵥ x + t • A *ᵥ y - b = s • A *ᵥ x + t • A *ᵥ y - (s + t) • b := by
          rw [hst, one_smul]
      _ = _ := by module
  simp only [he, smul_eq_mul]
  unfold sqNorm
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have ht' : t = 1 - s := by linarith
  subst ht'
  nlinarith [mul_nonneg (mul_nonneg hs ht) (sq_nonneg ((A *ᵥ x - b) i - (A *ᵥ y - b) i))]

/-- $r\mapsto\lambda\sum_{i\in I}|r_i|$ is convex for $\lambda\ge0$. -/
theorem weighted_abs_sum_convex {n : ℕ} (lam : ℝ) (hlam : 0 ≤ lam) (I : Finset (Fin n)) :
    ConvexOn ℝ univ (fun r : Vec n => lam * ∑ i ∈ I, |r i|) := by
  refine ⟨convex_univ, fun x _ y _ s t hs ht hst => ?_⟩
  simp only [smul_eq_mul, Pi.add_apply, Pi.smul_apply]
  have h : ∑ i ∈ I, |s * x i + t * y i| ≤ s * ∑ i ∈ I, |x i| + t * ∑ i ∈ I, |y i| := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    calc |s * x i + t * y i| ≤ |s * x i| + |t * y i| := abs_add_le _ _
      _ = s * |x i| + t * |y i| := by rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg ht]
  calc lam * ∑ i ∈ I, |s * x i + t * y i| ≤ lam * (s * ∑ i ∈ I, |x i| + t * ∑ i ∈ I, |y i|) :=
        mul_le_mul_of_nonneg_left h hlam
    _ = s * (lam * ∑ i ∈ I, |x i|) + t * (lam * ∑ i ∈ I, |y i|) := by ring


/-- Membership in the sign neighborhood: $|x_i|=\sigma_ix_i$ when $\sigma_ix_i>0$ and
$\sigma_i=\operatorname{sign}(x_{*,i})$ with $x_{*,i}\ne0$. -/
theorem abs_eq_sign_mul {a x : ℝ} (ha : a ≠ 0) (hx : 0 < Real.sign a * x) :
    |x| = Real.sign a * x := by
  rcases lt_or_gt_of_ne ha with h | h
  · rw [Real.sign_of_neg h] at hx ⊢
    rw [abs_of_neg (by linarith)]
    ring
  · rw [Real.sign_of_pos h] at hx ⊢
    rw [abs_of_pos (by linarith)]
    ring

/-- Item `A/local/prose/012` (`paper/sections/local.tex:116-122`), anchor "For a concrete
reduction, let": the set where the lasso decomposition is claimed.

For $F(x)=\frac12\|Ax-b\|^2+\lambda\|x\|_1$ with $A\in\R^{m\times n}$, $b\in\R^m$, $\lambda>0$
and a unique minimizer $x_*$, put $I_0=\{i:x_{*,i}=0\}$ and
$\sigma_i=\operatorname{sign}(x_{*,i})$ for $i\notin I_0$. The set
$N=\{x:\sigma_ix_i>0\ \forall i\notin I_0\}$ is an open convex neighborhood of $x_*$. -/
theorem lasso_neighborhood {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Vec m) (lam : ℝ)
    (_hlam : 0 < lam) (F : Vec n → ℝ)
    (_hFdef : ∀ x, F x = 1 / 2 * sqNorm (A *ᵥ x - b) + lam * ∑ i, |x i|)
    (xstar : Vec n) (_hmin : ∀ x, F xstar ≤ F x) (_huniq : ∀ x, F x = F xstar → x = xstar)
    (I0 : Finset (Fin n)) (hI0 : I0 = Finset.univ.filter fun i => xstar i = 0)
    (σ : Fin n → ℝ) (hσ : ∀ i ∉ I0, σ i = Real.sign (xstar i))
    (N : Set (Vec n)) (hN : N = {x | ∀ i ∉ I0, 0 < σ i * x i}) :
    IsOpen N ∧ Convex ℝ N ∧ xstar ∈ N := by
  have hne : ∀ i ∉ I0, xstar i ≠ 0 := by
    intro i hi h0
    exact hi (by rw [hI0]; simp [h0])
  refine ⟨?_, ?_, ?_⟩
  · have he : N = ⋂ i ∈ I0ᶜ, {x : Vec n | 0 < σ i * x i} := by
      rw [hN]
      ext x
      simp
    rw [he]
    exact isOpen_biInter_finset fun i _ =>
      isOpen_lt continuous_const (continuous_const.mul (continuous_apply i))
  · rw [hN]
    intro x hx y hy s t hs ht hst i hi
    have hxi := hx i hi
    have hyi := hy i hi
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 : s * min (σ i * x i) (σ i * y i) ≤ s * (σ i * x i) :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) hs
    have h2 : t * min (σ i * x i) (σ i * y i) ≤ t * (σ i * y i) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) ht
    have h3 : 0 < min (σ i * x i) (σ i * y i) := lt_min hxi hyi
    nlinarith
  · rw [hN]
    intro i hi
    rw [hσ i hi]
    rcases lt_or_gt_of_ne (hne i hi) with h | h
    · rw [Real.sign_of_neg h]; linarith
    · rw [Real.sign_of_pos h]; linarith

/-- Item `A/local/disp/005`, equation `art:local-l1-decomposition`
(`paper/sections/local.tex:123-130`).

With $F$, $x_*$, $I_0$, $\sigma$ and the neighborhood $N$ of `lasso_neighborhood`, and
\[ \psi(x)=\tfrac12\norm{Ax-b}^2+\lambda\sum_{i\notin I_0}\sigma_ix_i,\qquad
   \gamma(r)=\lambda\sum_{i\in I_0}|r_i|, \]
the exact decomposition on $N$ is $F(x)=\psi(x)+\gamma(x-x_*)$. ($\sum_{i\notin I_0}$ is the sum
over the complement `I0ᶜ`.) -/
theorem lasso_decomposition {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Vec m) (lam : ℝ)
    (_hlam : 0 < lam) (F : Vec n → ℝ)
    (hFdef : ∀ x, F x = 1 / 2 * sqNorm (A *ᵥ x - b) + lam * ∑ i, |x i|)
    (xstar : Vec n) (_hmin : ∀ x, F xstar ≤ F x) (_huniq : ∀ x, F x = F xstar → x = xstar)
    (I0 : Finset (Fin n)) (hI0 : I0 = Finset.univ.filter fun i => xstar i = 0)
    (σ : Fin n → ℝ) (hσ : ∀ i ∉ I0, σ i = Real.sign (xstar i))
    (N : Set (Vec n)) (hN : N = {x | ∀ i ∉ I0, 0 < σ i * x i})
    (ψ γ : Vec n → ℝ) (hψ : ∀ x, ψ x = 1 / 2 * sqNorm (A *ᵥ x - b) + lam * ∑ i ∈ I0ᶜ, σ i * x i)
    (hγ : ∀ r, γ r = lam * ∑ i ∈ I0, |r i|) :
    ∀ x ∈ N, F x = ψ x + γ (x - xstar) := by
  intro x hx
  rw [hN] at hx
  have hzero : ∀ i ∈ I0, xstar i = 0 := by
    intro i hi
    rw [hI0] at hi
    simpa using hi
  have hne : ∀ i ∉ I0, xstar i ≠ 0 := by
    intro i hi h0
    exact hi (by rw [hI0]; simp [h0])
  have h1 : ∑ i ∈ I0, |x i| = ∑ i ∈ I0, |(x - xstar) i| := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [hzero i hi]
  have h2 : ∑ i ∈ I0ᶜ, |x i| = ∑ i ∈ I0ᶜ, σ i * x i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ∉ I0 := Finset.mem_compl.mp hi
    have hpos := hx i hi'
    rw [hσ i hi'] at hpos ⊢
    exact abs_eq_sign_mul (hne i hi') hpos
  rw [hFdef, hψ, hγ, ← Finset.sum_add_sum_compl I0, h1, h2]
  ring

/-- Item `A/local/prose/013` (`paper/sections/local.tex:131-133`), anchor "The nonzero optimal
coordinates contribute affine terms".

With $\psi,\gamma$ as in display `disp/005`: $\psi$ ($=\frac12\|Ax-b\|^2$ plus the affine terms of
the nonzero optimal coordinates) is smooth ($C^\infty$) and convex, and $\gamma$ is a finite,
convex, positively homogeneous (centered sublinear) function. -/
theorem lasso_parts {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Vec m) (lam : ℝ)
    (hlam : 0 < lam) (I0 : Finset (Fin n)) (σ : Fin n → ℝ) (ψ γ : Vec n → ℝ)
    (hψ : ∀ x, ψ x = 1 / 2 * sqNorm (A *ᵥ x - b) + lam * ∑ i ∈ I0ᶜ, σ i * x i)
    (hγ : ∀ r, γ r = lam * ∑ i ∈ I0, |r i|) :
    ConvexOn ℝ univ ψ ∧ ContDiff ℝ ∞ ψ ∧ ConvexOn ℝ univ γ ∧
      Homogeneous.PositiveDegreeOne γ := by
  have hψe : ψ = fun x => 1 / 2 * sqNorm (A *ᵥ x - b) + lam * ∑ i ∈ I0ᶜ, σ i * x i := funext hψ
  have hγe : γ = fun r => lam * ∑ i ∈ I0, |r i| := funext hγ
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hq : ConvexOn ℝ univ (fun x : Vec n => 1 / 2 * sqNorm (A *ᵥ x - b)) :=
      (sqNorm_affine_convex A b).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have hl : ConvexOn ℝ univ (fun x : Vec n => lam * ∑ i ∈ I0ᶜ, σ i * x i) := by
      refine ⟨convex_univ, fun x _ y _ s t _ _ _ => le_of_eq ?_⟩
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
        Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
    rw [hψe]
    exact hq.add hl
  · rw [hψe]
    have hA : ContDiff ℝ ∞ (fun x : Vec n => A *ᵥ x - b) :=
      (AffineProjection.matrixCLM A).contDiff.sub contDiff_const
    unfold sqNorm
    apply ContDiff.add
    · apply ContDiff.mul contDiff_const
      apply ContDiff.sum
      intro i _
      exact ((contDiff_apply ℝ ℝ i).comp hA).pow 2
    · apply ContDiff.mul contDiff_const
      apply ContDiff.sum
      intro i _
      exact contDiff_const.mul (contDiff_apply ℝ ℝ i)
  · rw [hγe]
    exact weighted_abs_sum_convex lam hlam.le I0
  · intro t ht r
    rw [hγ, hγ, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg ht]
    ring

/-- The lasso objective is convex. -/
theorem lasso_convex {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Vec m) (lam : ℝ)
    (hlam : 0 ≤ lam) (F : Vec n → ℝ)
    (hFdef : ∀ x, F x = 1 / 2 * sqNorm (A *ᵥ x - b) + lam * ∑ i, |x i|) :
    ConvexOn ℝ univ F :=
  (((sqNorm_affine_convex A b).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)).add
    (weighted_abs_sum_convex lam hlam Finset.univ)).congr (fun x _ => (hFdef x).symm)

/-- Item `A/local/prose/014` (`paper/sections/local.tex:133-135`), anchor
"Corollary~\ref{art:local-centered} therefore gives a".

For the lasso objective with a unique minimizer, Corollary `art:local-centered` (applied with the
neighborhood $N$ and the decomposition `disp/005`) gives a positive sublevel basin, chosen
independently of the initial SPD matrix, in which every admissible run stays in $N$ and converges
in value and iterates to $x_*$. -/
theorem lasso_local_basin {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Vec m) (lam : ℝ)
    (hlam : 0 < lam) (F : Vec n → ℝ)
    (hFdef : ∀ x, F x = 1 / 2 * sqNorm (A *ᵥ x - b) + lam * ∑ i, |x i|)
    (xstar : Vec n) (hmin : ∀ x, F xstar ≤ F x) (huniq : ∀ x, F x = F xstar → x = xstar)
    (I0 : Finset (Fin n)) (hI0 : I0 = Finset.univ.filter fun i => xstar i = 0)
    (σ : Fin n → ℝ) (hσ : ∀ i ∉ I0, σ i = Real.sign (xstar i))
    (N : Set (Vec n)) (hN : N = {x | ∀ i ∉ I0, 0 < σ i * x i}) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ R : AdmissibleBFGSRun n F, F (R.x 0) ≤ F xstar + ε →
      (∀ k, R.x k ∈ N) ∧ Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) ∧
        Tendsto R.x atTop (𝓝 xstar) := by
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Vec n → ℝ, ψ = fun x =>
      1 / 2 * sqNorm (A *ᵥ x - b) + lam * ∑ i ∈ I0ᶜ, σ i * x i := ⟨_, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : Vec n → ℝ, γ = fun r => lam * ∑ i ∈ I0, |r i| := ⟨_, rfl⟩
  have hψ' : ∀ x, ψ x = 1 / 2 * sqNorm (A *ᵥ x - b) + lam * ∑ i ∈ I0ᶜ, σ i * x i :=
    fun x => by rw [hψ]
  have hγ' : ∀ r, γ r = lam * ∑ i ∈ I0, |r i| := fun r => by rw [hγ]
  obtain ⟨hNo, hNc, hxN⟩ := lasso_neighborhood A b lam hlam F hFdef xstar hmin huniq I0 hI0 σ hσ N hN
  obtain ⟨hψc, hψs, hγc, hγh⟩ := lasso_parts A b lam hlam I0 σ ψ γ hψ' hγ'
  exact local_centered F ψ γ (lasso_convex A b lam hlam.le F hFdef) xstar hmin huniq N hNo hNc hxN
    (hψc.subset (subset_univ _) hNc)
    (ConvexCellRadial.contDiffOn_two_locallyC11 hNo (hψs.of_le (by norm_cast)).contDiffOn)
    hγc hγh
    (lasso_decomposition A b lam hlam F hFdef xstar hmin huniq I0 hI0 σ hσ N hN ψ γ hψ' hγ')

/-- Item `A/local/prose/015` (`paper/sections/local.tex:136`), anchor "Uniqueness is a hypothesis
here".

$\lambda>0$ alone does not supply a unique minimizer: for $A=(1\ 1)\in\R^{1\times2}$, $b=2$,
$\lambda=1$, the lasso objective $F(x)=\frac12(x_1+x_2-2)^2+|x_1|+|x_2|$ has the two distinct
minimizers $(1,0)$ and $(0,1)$. -/
theorem lasso_uniqueness_not_automatic :
    ∃ (A : Matrix (Fin 1) (Fin 2) ℝ) (b : Vec 1) (lam : ℝ), 0 < lam ∧
      ∃ x y : Vec 2, x ≠ y ∧
        (∀ z, 1 / 2 * sqNorm (A *ᵥ x - b) + lam * ∑ i, |x i| ≤
          1 / 2 * sqNorm (A *ᵥ z - b) + lam * ∑ i, |z i|) ∧
        (∀ z, 1 / 2 * sqNorm (A *ᵥ y - b) + lam * ∑ i, |y i| ≤
          1 / 2 * sqNorm (A *ᵥ z - b) + lam * ∑ i, |z i|) := by
  have hval : ∀ z : Vec 2, 1 / 2 * sqNorm (!![(1 : ℝ), 1] *ᵥ z - ![2]) + 1 * ∑ i, |z i| =
      1 / 2 * (z 0 + z 1 - 2) ^ 2 + (|z 0| + |z 1|) := by
    intro z
    simp [sqNorm, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hlow : ∀ z : Vec 2, 3 / 2 ≤ 1 / 2 * (z 0 + z 1 - 2) ^ 2 + (|z 0| + |z 1|) := by
    intro z
    nlinarith [le_abs_self (z 0), le_abs_self (z 1), sq_nonneg (z 0 + z 1 - 1)]
  refine ⟨!![1, 1], ![2], 1, one_pos, ![1, 0], ![0, 1], ?_, ?_, ?_⟩
  · intro h
    have := congrFun h 0
    norm_num at this
  · intro z
    rw [hval, hval]
    refine le_trans (le_of_eq ?_) (hlow z)
    norm_num
  · intro z
    rw [hval, hval]
    refine le_trans (le_of_eq ?_) (hlow z)
    norm_num

/-- $x\mapsto\|Ax-b\|$ (Euclidean) is convex. -/
theorem norm_affine_convex {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Vec m) :
    ConvexOn ℝ univ (fun x : Vec n => ‖euclideanVector (A *ᵥ x - b)‖) :=
  EuclideanResidual.norm_residual_convex (EuclideanResidual.matrixEuclideanCLM A)
    (euclideanVector b)

/-- Item `A/local/prose/016` (`paper/sections/local.tex:138-142`), anchor "A locally $C^{1,1}$
convex loss plus finitely many Euclidean".

For $F(x)=\ell(x)+\sum_j\|A_jx-b_j\|$ with $\ell$ convex and locally $C^{1,1}$ and finitely
many Euclidean residual norms, and any point $x_*$: with
$\psi(x)=\ell(x)+\sum_{j:A_jx_*\ne b_j}\|A_jx-b_j\|$ and
$\gamma(r)=\sum_{j:A_jx_*=b_j}\|A_jr\|$, the decomposition $F(x)=\psi(x)+\gamma(x-x_*)$ holds
(a zero residual gives the centered sublinear function $\|A_j(x-x_*)\|$), $\psi$ is convex,
$\gamma$ is convex and positively homogeneous, and on an open convex neighborhood of $x_*$ (where
the residuals nonzero at $x_*$ stay nonzero, so that their norms are smooth) $\psi$ is locally
$C^{1,1}$: the representation and smoothness assumptions of Theorem `art:centered` hold near
$x_*$. -/
theorem euclidean_residuals_local_form {n : ℕ} {J : Type*} [Fintype J] {m : J → ℕ}
    (loss : Vec n → ℝ) (hloss : ConvexOn ℝ univ loss)
    (hloss_s : CenteredSmoothSublinear.LocallyC11On univ loss)
    (A : ∀ j, Matrix (Fin (m j)) (Fin n) ℝ) (b : ∀ j, Vec (m j)) (F : Vec n → ℝ)
    (hFdef : ∀ x, F x = loss x + ∑ j, ‖euclideanVector (A j *ᵥ x - b j)‖) (xstar : Vec n)
    (ψ γ : Vec n → ℝ)
    (hψ : ∀ x, ψ x = loss x + ∑ j ∈ Finset.univ.filter (fun j => A j *ᵥ xstar - b j ≠ 0),
      ‖euclideanVector (A j *ᵥ x - b j)‖)
    (hγ : ∀ r, γ r = ∑ j ∈ Finset.univ.filter (fun j => A j *ᵥ xstar - b j = 0),
      ‖euclideanVector (A j *ᵥ r)‖) :
    (∀ x, F x = ψ x + γ (x - xstar)) ∧ ConvexOn ℝ univ ψ ∧ ConvexOn ℝ univ γ ∧
      Homogeneous.PositiveDegreeOne γ ∧
      ∃ U : Set (Vec n), IsOpen U ∧ Convex ℝ U ∧ xstar ∈ U ∧
        CenteredSmoothSublinear.LocallyC11On U ψ := by
  classical
  have hψe : ψ = fun x => loss x + ∑ j ∈ Finset.univ.filter (fun j => A j *ᵥ xstar - b j ≠ 0),
      ‖euclideanVector (A j *ᵥ x - b j)‖ := funext hψ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [hFdef, hψ, hγ, ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun j => A j *ᵥ xstar - b j ≠ 0)]
    have h0 : ∑ j ∈ Finset.univ.filter (fun j => ¬ (A j *ᵥ xstar - b j ≠ 0)),
        ‖euclideanVector (A j *ᵥ x - b j)‖ =
        ∑ j ∈ Finset.univ.filter (fun j => A j *ᵥ xstar - b j = 0),
          ‖euclideanVector (A j *ᵥ (x - xstar))‖ := by
      simp only [not_not]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : A j *ᵥ xstar = b j := sub_eq_zero.mp (Finset.mem_filter.mp hj).2
      rw [Matrix.mulVec_sub, hj']
    rw [h0]
    ring
  · rw [hψe]
    exact hloss.add (convexOn_finset_sum _ _ fun j _ => norm_affine_convex (A j) (b j))
  · have he : γ = fun r => ∑ j ∈ Finset.univ.filter (fun j => A j *ᵥ xstar - b j = 0),
        ‖euclideanVector (A j *ᵥ r - 0)‖ := by
      funext r
      simp [hγ]
    rw [he]
    exact convexOn_finset_sum _ _ fun j _ => norm_affine_convex (A j) 0
  · intro t ht r
    rw [hγ, hγ, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.mulVec_smul, euclideanVector_smul, norm_smul, Real.norm_of_nonneg ht]
  · obtain ⟨ε, hε, hsm⟩ := EuclideanResidual.smooth_neighborhood
      (fun j => EuclideanResidual.matrixEuclideanCLM (A j)) (fun j => euclideanVector (b j)) xstar
    refine ⟨Metric.ball xstar ε, Metric.isOpen_ball, convex_ball xstar ε,
      Metric.mem_ball_self hε, ?_⟩
    have hsp : ∀ x, ψ x = loss x + EuclideanResidual.smoothPart
        (fun j => EuclideanResidual.matrixEuclideanCLM (A j)) (fun j => euclideanVector (b j))
        xstar x := by
      intro x
      rw [hψ, EuclideanResidual.smoothPart, Finset.sum_filter]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      simp only [EuclideanResidual.matrix_residual]
      by_cases h : A j *ᵥ xstar - b j = 0
      · simp [h, show euclideanVector (0 : Vec (m j)) = 0 from rfl]
      · have h' : euclideanVector (A j *ᵥ xstar - b j) ≠ 0 := fun h'' => h (by
          simpa using congrArg (WithLp.equiv 2 (Vec (m j))) h'')
        simp [h, h']
    have hψe' : ψ = fun x => loss x + EuclideanResidual.smoothPart
        (fun j => EuclideanResidual.matrixEuclideanCLM (A j)) (fun j => euclideanVector (b j))
        xstar x := funext hsp
    rw [hψe']
    exact ConvexCellRadial.locallyC11_add Metric.isOpen_ball
      ⟨hloss_s.1.mono (subset_univ _), hloss_s.2.mono (subset_univ _)⟩
      (ConvexCellRadial.contDiffOn_two_locallyC11 Metric.isOpen_ball hsm)

/-- Item `A/local/prose/017` (`paper/sections/local.tex:142-143`), anchor "Under uniqueness,".

If, in addition, $F=\ell+\sum_j\|A_jx-b_j\|$ has a unique minimizer $x_*$, Corollary
`art:local-centered` applies (with the neighborhood and decomposition of
`euclidean_residuals_local_form`): some $\varepsilon>0$ gives, for every admissible run with
$F(x_0)\le F(x_*)+\varepsilon$, iterates in that neighborhood and convergence in value and
iterates to $x_*$. -/
theorem euclidean_residuals_basin {n : ℕ} {J : Type*} [Fintype J] {m : J → ℕ}
    (loss : Vec n → ℝ) (hloss : ConvexOn ℝ univ loss)
    (hloss_s : CenteredSmoothSublinear.LocallyC11On univ loss)
    (A : ∀ j, Matrix (Fin (m j)) (Fin n) ℝ) (b : ∀ j, Vec (m j)) (F : Vec n → ℝ)
    (hFdef : ∀ x, F x = loss x + ∑ j, ‖euclideanVector (A j *ᵥ x - b j)‖) (xstar : Vec n)
    (hmin : ∀ x, F xstar ≤ F x) (huniq : ∀ x, F x = F xstar → x = xstar) :
    ∃ U : Set (Vec n), IsOpen U ∧ xstar ∈ U ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ R : AdmissibleBFGSRun n F, F (R.x 0) ≤ F xstar + ε →
        (∀ k, R.x k ∈ U) ∧ Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) ∧
          Tendsto R.x atTop (𝓝 xstar) := by
  classical
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Vec n → ℝ, ψ = fun x => loss x + ∑ j ∈ Finset.univ.filter
      (fun j => A j *ᵥ xstar - b j ≠ 0), ‖euclideanVector (A j *ᵥ x - b j)‖ := ⟨_, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : Vec n → ℝ, γ = fun r => ∑ j ∈ Finset.univ.filter
      (fun j => A j *ᵥ xstar - b j = 0), ‖euclideanVector (A j *ᵥ r)‖ := ⟨_, rfl⟩
  obtain ⟨hdec, hψc, hγc, hγh, U, hU, hUc, hxU, hψs⟩ := euclidean_residuals_local_form loss hloss
    hloss_s A b F hFdef xstar ψ γ (fun x => by rw [hψ]) (fun r => by rw [hγ])
  have hF : ConvexOn ℝ univ F :=
    (hloss.add (convexOn_finset_sum _ _ fun j _ => norm_affine_convex (A j) (b j))).congr
      (fun x _ => (hFdef x).symm)
  obtain ⟨ε, hε, hbasin⟩ := local_centered F ψ γ hF xstar hmin huniq U hU hUc hxU
    (hψc.subset (subset_univ _) hUc) hψs hγc hγh (fun x _ => hdec x)
  exact ⟨U, hU, hxU, ε, hε, hbasin⟩


/-! ### Affine criticality in the plane (`local.tex:157-168`) -/

open AffineCriticalObjective ConvexSubdifferential in
/-- Item `A/local/disp/006` (`paper/sections/local.tex:158-161`): the definition
\[ \mathcal C_{\rm aff}=\{p:0\in\aff\partial F(p)\} \]
for $F:\R^2\to\R$. The library predicate `AffineCriticalObjective.IsAffineCritical F p` (stated
with the Euclidean copy of $\partial F(p)$) unfolds to $0\in\aff\partial F(p)$, where
`subdifferential F p = {g | ∀ z, dot g (z - p) ≤ F z - F p}` is the convex subdifferential
(`ConvexSubdifferential.mem_subdifferential`) and `affineSpan ℝ` is the affine hull. -/
theorem affineCritical_set_eq (F : Vec 2 → ℝ) :
    {p | IsAffineCritical F p} = {p | (0 : Vec 2) ∈ affineSpan ℝ (subdifferential F p)} := by
  ext p
  exact isAffineCritical_iff_coordinate_affineSpan F p

/-- $a^Tb=b^Ta$. -/
theorem dot_comm' {n : ℕ} (a b : Vec n) : dot a b = dot b a := by
  simp only [dot, mul_comm]

/-- $a^Ta=\|a\|^2$. -/
theorem dot_self_eq_sqNorm {n : ℕ} (a : Vec n) : dot a a = sqNorm a := by
  simp only [dot, sqNorm, pow_two]

/-- $\|a+tv\|^2=\|a\|^2+2t\,a^Tv+t^2\|v\|^2$. -/
theorem sqNorm_add_smul {n : ℕ} (a v : Vec n) (t : ℝ) :
    sqNorm (a + t • v) = sqNorm a + 2 * t * dot a v + t ^ 2 * sqNorm v := by
  simp only [sqNorm, dot, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- First-order condition for a least-(Euclidean)-norm point of an affine subspace. -/
theorem least_norm_orthogonal {n : ℕ} (S : AffineSubspace ℝ (Vec n)) {a : Vec n} (ha : a ∈ S)
    (hmin : ∀ c ∈ S, sqNorm a ≤ sqNorm c) {c : Vec n} (hc : c ∈ S) : dot a (c - a) = 0 := by
  have hline : ∀ t : ℝ, a + t • (c - a) ∈ S := by
    intro t
    have h := AffineMap.lineMap_mem (Q := S) t ha hc
    rwa [AffineMap.lineMap_apply_module', add_comm] at h
  have hq : ∀ t : ℝ, 0 ≤ 2 * t * dot a (c - a) + t ^ 2 * sqNorm (c - a) := by
    intro t
    have h := hmin _ (hline t)
    rw [sqNorm_add_smul] at h
    linarith
  set u := dot a (c - a)
  set d := sqNorm (c - a)
  have hd : 0 ≤ d := sqNorm_nonneg _
  by_contra hu
  have h := hq (-u / (d + 1))
  have hpos : 0 < d + 1 := by linarith
  have h2 : 2 * (-u / (d + 1)) * u + (-u / (d + 1)) ^ 2 * d =
      -(u ^ 2 * (d + 2)) / (d + 1) ^ 2 := by
    field_simp
    ring
  rw [h2] at h
  have h3 : 0 < u ^ 2 * (d + 2) / (d + 1) ^ 2 := by
    apply div_pos _ (by positivity)
    exact mul_pos (by positivity) (by linarith)
  rw [neg_div] at h
  linarith

open AffineCriticalObjective ConvexSubdifferential in
/-- Item `A/local/prose/021` (`paper/sections/local.tex:162-165`), anchor "At a point outside this
set, let $a$".

Let $F:\R^2\to\R$ be finite and convex and $p\notin\mathcal C_{\rm aff}$. The affine hull
$\aff\partial F(p)$ has a unique least-norm point $a$; it satisfies $a\ne0$ and
$g^Ta=\|a\|^2$ for every $g\in\partial F(p)$ ("orthogonality to its direction space"), and thus
$g^T(-a/\|a\|^2)=-1$: $-a/\|a\|^2$ decreases all supporting models at the same unit rate.
Norms are Euclidean (`sqNorm a` $=\|a\|^2$). -/
theorem least_norm_point (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (p : Vec 2)
    (hp : ¬ IsAffineCritical F p) :
    (∃! a : Vec 2, a ∈ affineSpan ℝ (subdifferential F p) ∧
      ∀ c ∈ affineSpan ℝ (subdifferential F p), sqNorm a ≤ sqNorm c) ∧
    ∀ a : Vec 2, a ∈ affineSpan ℝ (subdifferential F p) →
      (∀ c ∈ affineSpan ℝ (subdifferential F p), sqNorm a ≤ sqNorm c) →
      a ≠ 0 ∧ (∀ g ∈ subdifferential F p, dot g a = sqNorm a) ∧
        ∀ g ∈ subdifferential F p, dot g (-(sqNorm a)⁻¹ • a) = -1 := by
  set S := affineSpan ℝ (subdifferential F p) with hS
  have hpairing : ∀ a ∈ S, (∀ c ∈ S, sqNorm a ≤ sqNorm c) →
      ∀ g ∈ subdifferential F p, dot g a = sqNorm a := by
    intro a ha hmin g hg
    have h := least_norm_orthogonal S ha hmin (subset_affineSpan ℝ _ hg)
    rw [dot_comm' g a, ← dot_self_eq_sqNorm]
    have h' : dot a (g - a) = dot a g - dot a a := by
      simp only [dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    linarith
  refine ⟨?_, ?_⟩
  · -- existence and uniqueness
    obtain ⟨g0, hg0⟩ := subdifferential_nonempty hF p
    have hS0 : g0 ∈ S := subset_affineSpan ℝ _ hg0
    set K := (S : Set (Vec 2)) ∩ {c | sqNorm c ≤ sqNorm g0} with hK
    have hsq_cont : Continuous (fun c : Vec 2 => sqNorm c) := by
      unfold sqNorm; fun_prop
    have hKc : IsCompact K := by
      apply Metric.isCompact_of_isClosed_isBounded
      · exact (AffineSubspace.closed_of_finiteDimensional S).inter
          (isClosed_le hsq_cont continuous_const)
      · refine (Metric.isBounded_closedBall (x := (0 : Vec 2))
          (r := Real.sqrt (sqNorm g0))).subset ?_
        intro c hc
        rw [Metric.mem_closedBall, dist_zero_right]
        apply ConvexSubdifferential.norm_le_of_sqNorm_le (Real.sqrt_nonneg _)
        rw [Real.sq_sqrt (sqNorm_nonneg _)]
        exact hc.2
    obtain ⟨a, haK, hamin⟩ := hKc.exists_isMinOn
      ⟨g0, hS0, show sqNorm g0 ≤ sqNorm g0 from le_rfl⟩ hsq_cont.continuousOn
    have hamin' : ∀ c ∈ S, sqNorm a ≤ sqNorm c := by
      intro c hc
      by_cases h : sqNorm c ≤ sqNorm g0
      · exact hamin ⟨hc, h⟩
      · exact (haK.2).trans (le_of_lt (lt_of_not_ge h))
    refine ⟨a, ⟨haK.1, hamin'⟩, ?_⟩
    rintro a' ⟨ha', hmin'⟩
    have h1 := least_norm_orthogonal S haK.1 hamin' ha'
    have h2 := least_norm_orthogonal S ha' hmin' haK.1
    have hz : sqNorm (a' - a) = 0 := by
      rw [← dot_self_eq_sqNorm]
      have e1 : dot (a' - a) (a' - a) = -dot a' (a - a') - dot a (a' - a) := by
        simp only [dot, Pi.sub_apply, Finset.sum_sub_distrib.symm, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [e1, h1, h2]
      ring
    exact sub_eq_zero.mp ((CertificateGeometry.sqNorm_eq_zero_iff _).mp hz)
  · intro a ha hmin
    have hne : a ≠ 0 := by
      rintro rfl
      exact hp ((isAffineCritical_iff_coordinate_affineSpan F p).mpr ha)
    have hpos : sqNorm a ≠ 0 := fun h => hne ((CertificateGeometry.sqNorm_eq_zero_iff a).mp h)
    refine ⟨hne, hpairing a ha hmin, fun g hg => ?_⟩
    rw [dot_smul_right, hpairing a ha hmin g hg]
    field_simp

open AffineCriticalObjective ConvexSubdifferential in
/-- Item `A/local/prose/022` (`paper/sections/local.tex:166-168`), anchor "Affine criticality
concerns failure of this common-rate direction", first part.

Affine criticality is the failure of a common-rate direction:
$p\in\mathcal C_{\rm aff}$ iff there is no $v$ with $g^Tv=-1$ for all $g\in\partial F(p)$; and
ordinary stationarity $0\in\partial F(p)$ is the failure of every strict common descent direction:
iff there is no $v$ with $g^Tv<0$ for all $g\in\partial F(p)$. -/
theorem affineCritical_and_stationarity (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (p : Vec 2) :
    (IsAffineCritical F p ↔ ¬ ∃ v : Vec 2, ∀ g ∈ subdifferential F p, dot g v = -1) ∧
      ((0 : Vec 2) ∈ subdifferential F p ↔
        ¬ ∃ v : Vec 2, ∀ g ∈ subdifferential F p, dot g v < 0) := by
  refine ⟨?_, ?_⟩
  · rw [equal_rate_exists_iff_not_affineCritical hF p, not_not]
  · constructor
    · rintro h0 ⟨v, hv⟩
      have := hv 0 h0
      simp [dot] at this
    · intro hno
      by_contra h0
      apply hno
      -- the least-norm subgradient separates zero
      obtain ⟨g0, hg0, hmin⟩ := (isCompact_subdifferential hF p).exists_isMinOn
        (subdifferential_nonempty hF p)
        (show Continuous (fun c : Vec 2 => sqNorm c) by unfold sqNorm; fun_prop).continuousOn
      have hg0ne : g0 ≠ 0 := fun h => h0 (h ▸ hg0)
      have hpos : 0 < sqNorm g0 := lt_of_le_of_ne (sqNorm_nonneg _)
        (fun h => hg0ne ((CertificateGeometry.sqNorm_eq_zero_iff g0).mp h.symm))
      refine ⟨-g0, fun g hg => ?_⟩
      have hcomb : ∀ t ∈ Icc (0 : ℝ) 1, g0 + t • (g - g0) ∈ subdifferential F p := by
        intro t ht
        have h := convex_subdifferential F p hg0 hg (sub_nonneg.mpr ht.2) ht.1
          (by ring : (1 - t) + t = 1)
        have he : (1 - t) • g0 + t • g = g0 + t • (g - g0) := by module
        rwa [he] at h
      have hq : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ 2 * t * dot g0 (g - g0) + t ^ 2 * sqNorm (g - g0) := by
        intro t ht
        have h := hmin (hcomb t ht)
        simp only [mem_setOf_eq] at h
        rw [sqNorm_add_smul] at h
        linarith
      have hc : 0 ≤ dot g0 (g - g0) := by
        by_contra hneg
        push_neg at hneg
        set u := dot g0 (g - g0)
        set d := sqNorm (g - g0)
        have hd : 0 ≤ d := sqNorm_nonneg _
        set t := -u / (d - u + 1)
        have hden : 0 < d - u + 1 := by linarith
        have ht0 : 0 < t := div_pos (by linarith) hden
        have ht1 : t ≤ 1 := (div_le_one hden).mpr (by linarith)
        have h := hq t ⟨ht0.le, ht1⟩
        have hkey : 2 * t * u + t ^ 2 * d = t * (u * (2 * (d - u + 1) - d) / (d - u + 1)) := by
          simp only [t]
          field_simp
          ring
        rw [hkey] at h
        have hneg' : u * (2 * (d - u + 1) - d) / (d - u + 1) < 0 :=
          div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hneg (by linarith)) hden
        nlinarith
      have h' : dot g0 (g - g0) = dot g g0 - sqNorm g0 := by
        rw [← dot_self_eq_sqNorm, dot_comm' g g0]
        simp only [dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
      have hneg : dot g (-g0) = -dot g g0 := by
        simp only [dot, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
      rw [hneg]
      linarith

open AffineCriticalObjective ConvexSubdifferential in
/-- Item `A/local/prose/022` (`paper/sections/local.tex:166-168`), second part: "They need not
coincide." Item `A/local/prose/035` (`paper/sections/local.tex:289-290`), second part: equal-rate
descent is "stronger than ordinary descent".

For the finite convex $F(u,v)=\max\{u,2u\}$ on $\R^2$ and $p=0$: $p$ is affine critical
($0=2(1,0)-(2,0)$ with $(1,0),(2,0)\in\partial F(0)$) but not stationary
($0\notin\partial F(0)$, $F$ is unbounded below); there is a strict common descent direction
($v=(-1,0)$) but no equal-rate direction. -/
theorem affineCritical_not_stationary_example :
    ∃ F : Vec 2 → ℝ, ConvexOn ℝ univ F ∧ IsAffineCritical F 0 ∧
      (0 : Vec 2) ∉ subdifferential F 0 ∧
      (∃ v : Vec 2, ∀ g ∈ subdifferential F 0, dot g v < 0) ∧
      ¬ ∃ v : Vec 2, ∀ g ∈ subdifferential F 0, dot g v = -1 := by
  set F : Vec 2 → ℝ := fun x => max (x 0) (2 * x 0) with hFdef
  have hconv : ConvexOn ℝ univ F := by
    refine ⟨convex_univ, fun x _ y _ s t hs ht hst => ?_⟩
    simp only [hFdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    apply max_le
    · nlinarith [le_max_left (x 0) (2 * x 0), le_max_left (y 0) (2 * y 0)]
    · nlinarith [le_max_right (x 0) (2 * x 0), le_max_right (y 0) (2 * y 0)]
  have hF0 : F 0 = 0 := by simp [hFdef]
  have hsub : ∀ c : ℝ, 1 ≤ c → c ≤ 2 → (![c, 0] : Vec 2) ∈ subdifferential F 0 := by
    intro c hc1 hc2 z
    simp only [hFdef, sub_zero, dot, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, zero_mul, add_zero, Pi.zero_apply, mul_zero,
      max_self]
    rcases le_total 0 (z 0) with h | h
    · nlinarith [le_max_right (z 0) (2 * z 0), mul_le_mul_of_nonneg_right hc2 h]
    · nlinarith [le_max_left (z 0) (2 * z 0), mul_le_mul_of_nonpos_right hc1 h]
  have hcrit : IsAffineCritical F 0 := by
    rw [isAffineCritical_iff_coordinate_affineSpan]
    have h := AffineMap.lineMap_mem (Q := affineSpan ℝ (subdifferential F 0)) (-1 : ℝ)
      (subset_affineSpan ℝ _ (hsub 1 le_rfl (by norm_num)))
      (subset_affineSpan ℝ _ (hsub 2 (by norm_num) le_rfl))
    have he : AffineMap.lineMap (![1, 0] : Vec 2) ![2, 0] (-1 : ℝ) = 0 := by
      ext i
      fin_cases i <;> norm_num [AffineMap.lineMap_apply_module]
    rwa [he] at h
  refine ⟨F, hconv, hcrit, ?_, ⟨![-1, 0], fun g hg => ?_⟩, ?_⟩
  · intro h0
    have h := h0 ![-1, 0]
    simp [hFdef, dot] at h
    norm_num at h
  · have h := hg ![-1, 0]
    simp only [hFdef, sub_zero, Matrix.cons_val_zero] at h
    norm_num at h
    simp only [dot, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons] at h ⊢
    linarith
  · exact ((affineCritical_and_stationarity F hconv 0).1).mp hcrit

open AffineCriticalObjective ConvexSubdifferential in
/-- Item `A/local/prose/035` (`paper/sections/local.tex:289-290`), anchor "This condition says that
nonoptimal points retain equal-rate descent", first part.

For finite convex $F:\R^2\to\R$ and any set $K$, the condition
$\mathcal C_{\rm aff}\cap K\subseteq\arg\min F$ of Corollary `art:planar-convergence` says exactly
that every nonoptimal point of $K$ has an equal-rate descent direction; and an equal-rate
direction is a strict common descent direction (the converse fails,
`affineCritical_not_stationary_example`). -/
theorem affineCorrect_iff_equal_rate (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (K : Set (Vec 2)) :
    ({p | IsAffineCritical F p} ∩ K ⊆ argmin F ↔
      ∀ p ∈ K, p ∉ argmin F → ∃ v : Vec 2, ∀ g ∈ subdifferential F p, dot g v = -1) ∧
      ∀ p : Vec 2, (∃ v : Vec 2, ∀ g ∈ subdifferential F p, dot g v = -1) →
        ∃ v : Vec 2, ∀ g ∈ subdifferential F p, dot g v < 0 := by
  refine ⟨⟨fun h p hpK hpn => ?_, fun h p hp => ?_⟩, fun p ⟨v, hv⟩ => ⟨v, fun g hg => ?_⟩⟩
  · rw [equal_rate_exists_iff_not_affineCritical hF p]
    exact fun hc => hpn (h ⟨hc, hpK⟩)
  · by_contra hn
    exact (equal_rate_exists_iff_not_affineCritical hF p).mp (h p hp.2 hn) hp.1
  · rw [hv g hg]; norm_num

/-! ### Theorem `art:planar-cluster` and its proof -/

/-- Two vectors of the plane are linearly independent only if their determinant is nonzero. -/
theorem pairDet_ne_zero_of_linearIndependent {a b : Vec 2}
    (h : LinearIndependent ℝ ![a, b]) : HomogeneousPlanar.pairDet a b ≠ 0 := by
  rw [LinearIndependent.pair_iff] at h
  intro hd
  simp only [HomogeneousPlanar.pairDet] at hd
  have h1 := h (b 1) (-a 1) (by
    ext i; fin_cases i <;> simp <;> linarith)
  have h2 := h (b 0) (-a 0) (by
    ext i; fin_cases i <;> simp <;> linarith)
  have ha : a = 0 := by
    ext i; fin_cases i
    · simpa using h2.2
    · simpa using h1.2
  have h3 := h 1 0 (by simp [ha])
  exact one_ne_zero h3.1

/-- The regularity alternative of Theorem `art:planar-cluster`, hypothesis 2, as stated in the
TeX, implies the library's `ContDiffAt ℝ 2 F p ∨ PlanarCornerCharts.ConvexTwoBranchRegularAt F p`. -/
theorem regular_of_paper {F : Vec 2 → ℝ} {p : Vec 2}
    (h : (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p])) :
    ContDiffAt ℝ 2 F p ∨ PlanarCornerCharts.ConvexTwoBranchRegularAt F p := by
  rcases h with ⟨V, hV, hpV, hC⟩ | ⟨V, hV, hpV, f₁, f₂, hc₁, hc₂, hC₁, hC₂, hmax, h₁, h₂, hind⟩
  · exact Or.inl (hC.contDiffAt (hV.mem_nhds hpV))
  · right
    refine ⟨![f₁, f₂], V, hV, hpV, ?_, ?_, ?_, ?_⟩
    · intro i; fin_cases i
      · exact ⟨hc₁, hC₁⟩
      · exact ⟨hc₂, hC₂⟩
    · intro z hz
      rw [hmax z hz]
      refine ⟨?_, ?_⟩
      · rcases max_choice (f₁ z) (f₂ z) with h | h
        · exact ⟨0, by simp [h]⟩
        · exact ⟨1, by simp [h]⟩
      · rintro _ ⟨i, rfl⟩
        fin_cases i
        · exact le_max_left _ _
        · exact le_max_right _ _
    · intro i; fin_cases i
      · exact h₁
      · exact h₂
    · exact pairDet_ne_zero_of_linearIndependent hind

open AffineCriticalObjective in
/-- Item `A/local/theorem/art:planar-cluster` (`paper/sections/local.tex:214-229`), Theorem
`art:planar-cluster` ("An affine-critical cluster point in the plane").

Let $F:\R^2\to\R$ be finite and convex, attain its minimum $F_*$ (`IsLeast (range F) Fstar`),
and have a compact sublevel $K=\{F\le b\}$ with $b>F_*$. Assume:
1. for every $F_*<t\le b$, the boundary of $\{F\le t\}$ contains no nontrivial line segment;
2. at every $p\in K\setminus\mathcal C_{\rm aff}$, either $F$ is $C^2$ in a neighborhood of $p$,
   or it equals $\max\{f_1,f_2\}$ there, where $f_1,f_2$ are convex $C^2$ functions, both active
   at $p$, and $\nabla f_1(p),\nabla f_2(p)$ are linearly independent.
Every infinite admissible full-BFGS run starting in $K$ has an affine-critical cluster point
(`MapClusterPt p atTop R.x`: every neighborhood of $p$ contains $x_k$ for infinitely many $k$).
No local representation is required at affine-critical points (hypothesis 2 is only imposed
off $\mathcal C_{\rm aff}$). -/
theorem planar_cluster (F : Vec 2 → ℝ) (_hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (hFstar : IsLeast (Set.range F) Fstar) (b : ℝ) (_hb : Fstar < b)
    (hK : IsCompact {x | F x ≤ b})
    (hstrict : ∀ t, Fstar < t → t ≤ b →
      ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {z | F z ≤ t} → x = y)
    (hreg : ∀ p, F p ≤ b → ¬ IsAffineCritical F p →
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]))
    (R : AdmissibleBFGSRun 2 F) (hR : R.x 0 ∈ {x | F x ≤ b}) :
    ∃ p, MapClusterPt p atTop R.x ∧ IsAffineCritical F p := by
  obtain ⟨⟨star, hstar⟩, hlow⟩ := hFstar
  have hmin : ∀ z, F star ≤ F z := fun z => hstar ▸ hlow ⟨z, rfl⟩
  obtain ⟨p, hp, _, ha⟩ := R.planar_affineCritical_cluster_on_sublevel star hmin b hK hR
    (fun t ht htb => hstrict t (hstar ▸ ht) htb)
    (fun p hp hn => regular_of_paper (hreg p hp hn))
  exact ⟨p, hp, ha⟩

open AffineCriticalObjective in
/-- Item `A/local/disp/007` (`paper/sections/local.tex:240-244`), in the proof of Theorem
`art:planar-cluster`.

Under the assumptions of the theorem, for an admissible run starting in $K$, every $k$ and
$0\le\theta\le1$, the supporting inequality and convexity give
\[ F(x_k)-\theta d_k\le F((1-\theta)x_k+\theta x_{k+1})\le(1-\theta)F(x_k)+\theta F(x_{k+1}), \]
with $d_k=\alpha_kq_k=-g_k^Ts_k$ (`R.d k`). The proof uses it along a subsequence with
$x_k\to x$, $x_{k+1}\to z\ne x$; it holds for every $k$. -/
theorem planar_cluster_segment_values (F : Vec 2 → ℝ) (_hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (Set.range F) Fstar) (b : ℝ) (_hb : Fstar < b)
    (_hK : IsCompact {x | F x ≤ b})
    (_hstrict : ∀ t, Fstar < t → t ≤ b →
      ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {z | F z ≤ t} → x = y)
    (_hreg : ∀ p, F p ≤ b → ¬ IsAffineCritical F p →
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]))
    (R : AdmissibleBFGSRun 2 F) (_hR : R.x 0 ∈ {x | F x ≤ b}) (k : ℕ) (θ : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    F (R.x k) - θ * R.d k ≤ F ((1 - θ) • R.x k + θ • R.x (k + 1)) ∧
      F ((1 - θ) • R.x k + θ • R.x (k + 1)) ≤ (1 - θ) * F (R.x k) + θ * F (R.x (k + 1)) :=
  ⟨R.segment_value_lower k (1 - θ) θ (by ring),
    R.convex.2 (mem_univ _) (mem_univ _) (sub_nonneg.mpr hθ1) hθ0 (by ring)⟩

open AffineCriticalObjective ConvexSubdifferential TransportedCertificate in
/-- Item `A/local/disp/008` (`paper/sections/local.tex:255-260`), in the proof of Theorem
`art:planar-cluster`.

Under the assumptions of the theorem, for an admissible run starting in $K$ with value limit
$\ell$ (`hℓ`), suppose, as the proof does for a contradiction, that the cluster set $\Gamma$
contains no affine-critical point (`hnoaff`), so that $\ell>F_*$ (`hℓpos`). Lemma
`art:planar-field` constructs a continuous comparison field $w$ on a neighborhood $U$ of the
whole set $\Gamma$, and for each sufficiently close (Euclidean $\|s\|<\delta$) pair in $U$ that
is eligible for the run's constants $c_1,c_2$, with $g=\nabla F(x)$, $h=\nabla F(z)$, $s=z-x$,
$y=h-g$, $t=y^Ts$, $d=-g^Ts$, it gives uniform constants $m>0$, $C,L\ge0$ and scalars
$\lambda>0,\beta$ with
\[ (g^Tw(x))^2\ge m,\qquad (y^Tw(z))^2/t\le C,\qquad w(z)=\lambda w(x)+\beta s,\qquad
   \lambda^2\le1+Ld. \]
(The proof's assumptions cannot all hold -- that is the contradiction the proof derives.) -/
theorem planar_cluster_field (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (hFstar : IsLeast (Set.range F) Fstar) (b : ℝ) (_hb : Fstar < b)
    (hK : IsCompact {x | F x ≤ b})
    (hstrict : ∀ t, Fstar < t → t ≤ b →
      ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {z | F z ≤ t} → x = y)
    (hreg : ∀ p, F p ≤ b → ¬ IsAffineCritical F p →
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]))
    (R : AdmissibleBFGSRun 2 F) (hR : R.x 0 ∈ {x | F x ≤ b}) (ℓ : ℝ)
    (hℓ : Tendsto (fun k => F (R.x k)) atTop (𝓝 ℓ)) (hℓpos : Fstar < ℓ)
    (hnoaff : ∀ p, MapClusterPt p atTop R.x → ¬ IsAffineCritical F p) :
    ∃ (w : Vec 2 → Vec 2) (U : Set (Vec 2)), IsOpen U ∧ {p | MapClusterPt p atTop R.x} ⊆ U ∧
      ContinuousOn w U ∧ ∃ m C L δ : ℝ, 0 < m ∧ 0 ≤ C ∧ 0 ≤ L ∧ 0 < δ ∧
        ∀ x ∈ U, ∀ z ∈ U, ∀ g h : Vec 2, EligiblePair F R.c₁ R.c₂ x z g h →
          ‖euclideanVector (z - x)‖ < δ →
          ∃ lam β : ℝ, 0 < lam ∧ m ≤ (dot g (w x)) ^ 2 ∧
            (dot (h - g) (w z)) ^ 2 / dot (h - g) (z - x) ≤ C ∧
            w z = lam • w x + β • (z - x) ∧ lam ^ 2 ≤ 1 + L * (-dot g (z - x)) := by
  obtain ⟨⟨star, hstar⟩, hlow⟩ := hFstar
  have hx0 : F (R.x 0) ≤ b := hR
  have hclosed : IsClosed R.initialSublevel :=
    isClosed_le (convex_continuous R.convex) continuous_const
  have hinit : IsCompact R.initialSublevel :=
    hK.of_isClosed_subset hclosed (fun x hx => le_trans hx hx0)
  have hΓ := ClusterSetGeometry.isCompact_clusterSet R.x hinit R.iterate_mem_initialSublevel
  have hlevel : ∀ p ∈ ClusterSetGeometry.clusterSet R.x, F p = ℓ :=
    fun p hp => R.value_of_cluster hℓ hp
  have hℓb : ℓ ≤ b :=
    (le_of_tendsto hℓ (Eventually.of_forall R.objective_le_initial)).trans hx0
  obtain ⟨m', χ, v, _, U, Q, hU, hΓU, hUQ, hQ, η, κ, δ, C, C', C₀, hη, _, hδ, _, hC', hC₀,
      hLip, hvis, _, hpairs⟩ :=
    PlanarAllPairs.source_all_endpoint_estimates hF hΓ hlevel (hstrict ℓ hℓpos hℓb)
      (fun p hp => regular_of_paper (hreg p ((hlevel p hp).le.trans hℓb) (hnoaff p hp)))
      (fun p hp => hnoaff p hp) R.c₁_pos R.c₂_lt_one
  have hUQ' : U ⊆ Q := subset_closure.trans hUQ
  obtain ⟨G, hG, hGb⟩ := convex_supporting_bound_on_compact hF hQ
  set w := PlanarObjectiveField.field hF χ v
  refine ⟨w, U, hU, hΓU, ?_, η ^ 2, C₀, C', min δ (1 / G), by positivity, hC₀, hC',
    lt_min hδ (by positivity), ?_⟩
  · intro x hx
    obtain ⟨L, V, hV, hLV⟩ := hLip x (hUQ' hx)
    exact (hLV.continuousOn.continuousAt hV).continuousWithinAt
  · intro x hx z hz g h hp hs
    obtain ⟨_, hsec, lam, β, hlam, hend, _, hsq⟩ :=
      hpairs x hx z hz g h hp (hs.trans_le (min_le_left _ _))
    have hgsub : g ∈ subdifferential F x := convex_supporting_inequality hF hp.gradient_x
    have hvx := hvis x (hUQ' hx) g hgsub
    have hgn : ‖euclideanVector g‖ ≤ G := by
      have h1 := hGb x (hUQ' hx) g hgsub
      rw [← euclid_norm_sq] at h1
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) hG.le two_ne_zero).mp h1
    have hd1 : pairDecrease x z g ≤ 1 := by
      have hcs := dot_le_euclid (-g) (z - x)
      have hneg : dot (-g) (z - x) = pairDecrease x z g := by
        simp only [pairDecrease, pairStep, dot, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
      have hnorm : ‖euclideanVector (-g)‖ = ‖euclideanVector g‖ := by
        rw [show euclideanVector (-g) = -euclideanVector g from rfl, norm_neg]
      rw [hneg, hnorm] at hcs
      have hs' : ‖euclideanVector (z - x)‖ < 1 / G := hs.trans_le (min_le_right _ _)
      calc pairDecrease x z g ≤ ‖euclideanVector g‖ * ‖euclideanVector (z - x)‖ := hcs
        _ ≤ G * (1 / G) := mul_le_mul hgn hs'.le (norm_nonneg _) hG.le
        _ = 1 := by field_simp
    refine ⟨lam, β, hlam, ?_, hsec, hend, ?_⟩
    · exact pow_le_pow_left₀ hη.le hvx 2
    · have h := hsq hd1
      simpa [pairDecrease, pairStep] using h

open AffineCriticalObjective in
/-- Item `A/local/disp/009` (`paper/sections/local.tex:264-269`), in the proof of Theorem
`art:planar-cluster`.

Under the assumptions of the theorem, for an admissible run starting in $K$, a field
$w:\R^2\to\R^2$, $E_k=w(x_k)^TB_kw(x_k)$ with $B_k=H_k^{-1}$, and an index $k$ of the tail at
which display `disp/008` applies to the accepted pair $(x_k,x_{k+1})$ -- scalars $\lambda_k>0$,
$\beta_k$ with $w(x_{k+1})=\lambda_kw(x_k)+\beta_ks_k$, $(g_k^Tw(x_k))^2\ge m$,
$(y_k^Tw(x_{k+1}))^2/t_k\le C$ and $\lambda_k^2\le1+Ld_k$ -- the Hessian update and
$\widehat B_ks_k=0$ yield
\[ E_{k+1}=\lambda_k^2\Bigl(E_k-\frac{(g_k^Tw(x_k))^2}{q_k}\Bigr)
     +\frac{(y_k^Tw(x_{k+1}))^2}{t_k}\le(1+Ld_k)(E_k-m/q_k)+C, \]
with $s_k=x_{k+1}-x_k$, $y_k=g_{k+1}-g_k$, $t_k=y_k^Ts_k$, $q_k=g_k^TH_kg_k$ (`R.q k`),
$d_k$ = `R.d k`. -/
theorem planar_cluster_energy (F : Vec 2 → ℝ) (_hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (Set.range F) Fstar) (b : ℝ) (_hb : Fstar < b)
    (_hK : IsCompact {x | F x ≤ b})
    (_hstrict : ∀ t, Fstar < t → t ≤ b →
      ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {z | F z ≤ t} → x = y)
    (_hreg : ∀ p, F p ≤ b → ¬ IsAffineCritical F p →
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]))
    (R : AdmissibleBFGSRun 2 F) (_hR : R.x 0 ∈ {x | F x ≤ b}) (w : Vec 2 → Vec 2)
    (E : ℕ → ℝ) (hE : ∀ k, E k = dot (w (R.x k)) ((R.H k)⁻¹ *ᵥ w (R.x k))) (m C L : ℝ) (k : ℕ)
    (lam β : ℝ) (_hlam : 0 < lam)
    (hframe : w (R.x (k + 1)) = lam • w (R.x k) + β • (R.x (k + 1) - R.x k))
    (hvis : m ≤ (dot (R.g k) (w (R.x k))) ^ 2)
    (hsec : (dot (R.g (k + 1) - R.g k) (w (R.x (k + 1)))) ^ 2 /
      dot (R.g (k + 1) - R.g k) (R.x (k + 1) - R.x k) ≤ C)
    (htr : lam ^ 2 ≤ 1 + L * R.d k) :
    E (k + 1) = lam ^ 2 * (E k - (dot (R.g k) (w (R.x k))) ^ 2 / R.q k) +
        (dot (R.g (k + 1) - R.g k) (w (R.x (k + 1)))) ^ 2 /
          dot (R.g (k + 1) - R.g k) (R.x (k + 1) - R.x k) ∧
      lam ^ 2 * (E k - (dot (R.g k) (w (R.x k))) ^ 2 / R.q k) +
        (dot (R.g (k + 1) - R.g k) (w (R.x (k + 1)))) ^ 2 /
          dot (R.g (k + 1) - R.g k) (R.x (k + 1) - R.x k) ≤
        (1 + L * R.d k) * (E k - m / R.q k) + C := by
  have hdisp : R.displacement k = R.x (k + 1) - R.x k := by
    rw [R.step]; simp [AdmissibleBFGSRun.displacement]
  have hen := R.scalar_frame_energy k (w (R.x k)) (w (R.x (k + 1))) lam β (by rw [hdisp]; exact hframe)
  have hres := R.scalar_frame_residual_nonneg k (w (R.x k))
  have hEk : ∀ j, E j = metricEnergy (R.hessian j) (w (R.x j)) := fun j => by
    rw [hE j]; rfl
  simp only [AdmissibleBFGSRun.gradientChange, AdmissibleBFGSRun.curvature, hdisp] at hen
  rw [← hEk, ← hEk] at hen
  rw [← hEk] at hres
  refine ⟨hen, ?_⟩
  have hq := R.q_pos k
  have hmq : m / R.q k ≤ (dot (R.g k) (w (R.x k))) ^ 2 / R.q k :=
    div_le_div_of_nonneg_right hvis hq.le
  have hlam2 : 0 ≤ lam ^ 2 := sq_nonneg _
  have h1 : lam ^ 2 * (E k - (dot (R.g k) (w (R.x k))) ^ 2 / R.q k) ≤
      (1 + L * R.d k) * (E k - (dot (R.g k) (w (R.x k))) ^ 2 / R.q k) :=
    mul_le_mul_of_nonneg_right htr hres
  have h2 : (1 + L * R.d k) * (E k - (dot (R.g k) (w (R.x k))) ^ 2 / R.q k) ≤
      (1 + L * R.d k) * (E k - m / R.q k) :=
    mul_le_mul_of_nonneg_left (by linarith) (hlam2.trans htr)
  linarith

open AffineCriticalObjective in
/-- Item `A/local/corollary/art:planar-convergence` (`paper/sections/local.tex:276-281`),
Corollary `art:planar-convergence` ("When affine criticality is correct").

Under the hypotheses of Theorem `art:planar-cluster`, assume in addition that
$\mathcal C_{\rm aff}\cap K\subseteq\arg\min F$. Every admissible run starting in $K$ then
converges in value to $F_*$ and in (Euclidean) distance to $\arg\min F$
(`euclideanSolutionDistance F x` is the Euclidean distance from $x$ to $\arg\min F$). A unique
minimizer ($\arg\min F=\{x_*\}$) gives convergence of the entire sequence. -/
theorem planar_convergence (F : Vec 2 → ℝ) (_hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (hFstar : IsLeast (Set.range F) Fstar) (b : ℝ) (_hb : Fstar < b)
    (hK : IsCompact {x | F x ≤ b})
    (hstrict : ∀ t, Fstar < t → t ≤ b →
      ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {z | F z ≤ t} → x = y)
    (hreg : ∀ p, F p ≤ b → ¬ IsAffineCritical F p →
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]))
    (hcorr : {p | IsAffineCritical F p} ∩ {x | F x ≤ b} ⊆ argmin F)
    (R : AdmissibleBFGSRun 2 F) (hR : R.x 0 ∈ {x | F x ≤ b}) :
    Tendsto (fun k => F (R.x k)) atTop (𝓝 Fstar) ∧
      Tendsto (fun k => euclideanSolutionDistance F (R.x k)) atTop (𝓝 0) ∧
      ∀ xstar : Vec 2, argmin F = {xstar} → Tendsto R.x atTop (𝓝 xstar) := by
  obtain ⟨⟨star, hstar⟩, hlow⟩ := hFstar
  have hmin : ∀ z, F star ≤ F z := fun z => hstar ▸ hlow ⟨z, rfl⟩
  obtain ⟨hv, _, hed, hx⟩ := R.planar_convergence_on_sublevel star hmin b hK hR
    (fun t ht htb => hstrict t (hstar ▸ ht) htb)
    (fun p hp hn => regular_of_paper (hreg p hp hn))
    (fun p hp hc => ConvexSubdifferential.zero_mem_iff_global_minimum.mpr (hcorr ⟨hc, hp⟩))
  refine ⟨hstar ▸ hv, hed, fun xstar hxs => ?_⟩
  have hxsmin : ∀ z, F xstar ≤ F z := by
    have : xstar ∈ argmin F := by rw [hxs]; rfl
    exact this
  have he : F star = F xstar := le_antisymm (hmin xstar) (hxsmin star)
  have hu : ∀ z, F z = F star → z = star := by
    intro z hz
    have hz' : z ∈ argmin F := fun y => hz ▸ hmin y
    have hs' : star ∈ argmin F := hmin
    rw [hxs] at hz' hs'
    rw [hz', hs']
  have hst : star = xstar := by
    have hs' : star ∈ argmin F := hmin
    rw [hxs] at hs'
    exact hs'
  rw [← hst]
  exact hx hu


/-! ### Corollary `art:planar-max` -/

open ConvexSubdifferential in
/-- Translation of the active-set data of Corollary `art:planar-max` (indexed by the active set
$I_*$ itself) to the library's enumeration `activeIndexMap` of $I_*$ by `Fin`. -/
theorem active_family_conversion {F : Vec 2 → ℝ} {m : ℕ} (f : Fin m → Vec 2 → ℝ)
    (xstar : Vec 2)
    (hind : AffineIndependent ℝ fun i : activeIndices F f xstar => coordinateGradient (f i) xstar)
    (lam : activeIndices F f xstar → ℝ) (hpos : ∀ i, 0 < lam i) (hsum : ∑ i, lam i = 1)
    (hzero : ∑ i, lam i • coordinateGradient (f i) xstar = 0) :
    AffineIndependent ℝ (fun j => coordinateGradient (f (activeIndexMap F f xstar j)) xstar) ∧
      ∃ w : Vec (activeIndices F f xstar).card, (∀ j, 0 < w j) ∧ ∑ j, w j = 1 ∧
        ∑ j, w j • coordinateGradient (f (activeIndexMap F f xstar j)) xstar = 0 := by
  set e := (activeIndices F f xstar).orderIsoOfFin rfl
  have he : ∀ j, ((e j : activeIndices F f xstar) : Fin m) = activeIndexMap F f xstar j :=
    fun j => Finset.coe_orderIsoOfFin_apply _ _ j
  refine ⟨?_, fun j => lam (e j), fun j => hpos _, (Equiv.sum_comp e.toEquiv lam).trans hsum, ?_⟩
  · have h := hind.comp_embedding e.toEquiv.toEmbedding
    convert h using 1
  · rw [← hzero, ← Equiv.sum_comp e.toEquiv
      (fun i : activeIndices F f xstar => lam i • coordinateGradient (f i) xstar)]
    apply Finset.sum_congr rfl
    intro j _
    rw [← he j]
    rfl

open ConvexSubdifferential AffineCriticalObjective in
/-- Item `A/local/corollary/art:planar-max` (`paper/sections/local.tex:303-322`), Corollary
`art:planar-max` ("Nondegenerate planar smooth maxima"), including its displays
`A/local/disp/010` (lines 310-313) and `A/local/disp/011` (lines 316-319).

Let $F:\R^2\to\R$ be finite and convex with a unique minimizer $x_*$. Near $x_*$ (on an open
$U\ni x_*$) suppose $F=\max_{1\le i\le m}f_i$ (`IsGreatest`: $F(x)$ is the largest $f_i(x)$),
where the branches are convex and $C^2$. Suppose sufficiently low positive sublevels are strictly
convex in the boundary-segment sense of Theorem `art:planar-cluster` (`hcontour`). For the active
set $I_*=\{i:f_i(x_*)=F(x_*)\}$, suppose the gradients are affinely independent and that there are
weights
\[ \lambda_i^*>0,\qquad \sum_{i\in I_*}\lambda_i^*=1,\qquad
   \sum_{i\in I_*}\lambda_i^*\nabla f_i(x_*)=0. \]
Then some $\varepsilon>0$, chosen independently of $H_0$ and the valid line-search constants,
satisfies $F(x_0)<F_*+\varepsilon\Rightarrow F(x_k)\to F_*,\ x_k\to x_*$ for every infinite
admissible full-BFGS run ($F_*=F(x_*)$). The last sentence of the corollary is
`planar_max_hessian_contours`. -/
theorem planar_max (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (xstar : Vec 2)
    (hmin : ∀ x, F xstar ≤ F x) (huniq : ∀ x, F x = F xstar → x = xstar)
    {m : ℕ} (f : Fin m → Vec 2 → ℝ) (U : Set (Vec 2)) (hU : IsOpen U) (hxU : xstar ∈ U)
    (hf : ∀ i, ConvexOn ℝ U (f i) ∧ ContDiffOn ℝ 2 (f i) U)
    (hmax : ∀ x ∈ U, IsGreatest (Set.range fun i => f i x) (F x))
    (hcontour : ∃ b, F xstar < b ∧ ∀ t, F xstar < t → t ≤ b →
      ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {z | F z ≤ t} → x = y)
    (I : Finset (Fin m)) (hI : I = Finset.univ.filter fun i => f i xstar = F xstar)
    (hind : AffineIndependent ℝ fun i : I => coordinateGradient (f i) xstar)
    (lam : I → ℝ) (hpos : ∀ i, 0 < lam i) (hsum : ∑ i, lam i = 1)
    (hzero : ∑ i, lam i • coordinateGradient (f i) xstar = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ R : AdmissibleBFGSRun 2 F, F (R.x 0) < F xstar + ε →
      Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) ∧ Tendsto R.x atTop (𝓝 xstar) := by
  have hrep : LocalFiniteMax F f xstar := by
    filter_upwards [hU.mem_nhds hxU] with z hz using hmax z hz
  have hIa : I = activeIndices F f xstar := hI
  subst hIa
  obtain ⟨hind', w, hw, hws, hwz⟩ := active_family_conversion f xstar hind lam hpos hsum hzero
  obtain ⟨b, hb, hstrict⟩ := hcontour
  exact PlanarMaxRegular.finite_max_local_basin hF xstar hmin huniq hU hxU hf hrep hind' w hw hws
    hwz hb hstrict

open ConvexSubdifferential AffineCriticalObjective in
/-- Item `A/local/corollary/art:planar-max` (`paper/sections/local.tex:303-322`), last sentence:
"A common positive lower Hessian bound on the locally relevant branches suffices for the contour
hypothesis."

Under the assumptions of `planar_max` without the contour hypothesis, if the active branches have
a common positive lower Hessian bound on $U$ ($\nabla^2f_i(x)-\mu I\succeq0$ for $i\in I_*$,
$x\in U$, $\mu>0$; `RadialHessian.matrix f x` is the matrix of the second Fréchet derivative),
then sufficiently low positive sublevels have no nontrivial boundary segment. -/
theorem planar_max_hessian_contours (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (xstar : Vec 2)
    (hmin : ∀ x, F xstar ≤ F x) (huniq : ∀ x, F x = F xstar → x = xstar)
    {m : ℕ} (f : Fin m → Vec 2 → ℝ) (U : Set (Vec 2)) (hU : IsOpen U) (hxU : xstar ∈ U)
    (hf : ∀ i, ConvexOn ℝ U (f i) ∧ ContDiffOn ℝ 2 (f i) U)
    (hmax : ∀ x ∈ U, IsGreatest (Set.range fun i => f i x) (F x))
    (I : Finset (Fin m)) (hI : I = Finset.univ.filter fun i => f i xstar = F xstar)
    (_hind : AffineIndependent ℝ fun i : I => coordinateGradient (f i) xstar)
    (lam : I → ℝ) (_hpos : ∀ i, 0 < lam i) (_hsum : ∑ i, lam i = 1)
    (_hzero : ∑ i, lam i • coordinateGradient (f i) xstar = 0) (μ : ℝ) (hμ : 0 < μ)
    (hhess : ∀ i ∈ I, ∀ x ∈ U, (RadialHessian.matrix (f i) x - μ • (1 : Mat 2)).PosSemidef) :
    ∃ b, F xstar < b ∧ ∀ t, F xstar < t → t ≤ b →
      ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {z | F z ≤ t} → x = y := by
  have hrep : LocalFiniteMax F f xstar := by
    filter_upwards [hU.mem_nhds hxU] with z hz using hmax z hz
  have hIa : I = activeIndices F f xstar := hI
  subst hIa
  set a := activeIndexMap F f xstar
  have hai : ∀ i, a i ∈ activeIndices F f xstar := by
    intro i
    have hi : a i ∈ Set.range a := mem_range_self i
    rwa [range_activeIndexMap] at hi
  have hr := localFiniteMax_restrict_active (convex_continuous hF).continuousAt
    (fun i => ((hf i).2.contDiffAt (hU.mem_nhds hxU)).continuousAt) hrep
  obtain ⟨r, hrpos, hball⟩ := Metric.mem_nhds_iff.mp (hr.and (hU.mem_nhds hxU))
  have hs : StrictConvexOn ℝ (Metric.ball xstar r) F := by
    apply PlanarMaxRegular.strictConvexOn_finite_max (convex_ball xstar r)
    · intro i
      exact PlanarMaxRegular.strictConvexOn_of_hessian_lower_bound Metric.isOpen_ball
        (convex_ball xstar r) ((hf (a i)).2.mono (fun p hp => (hball hp).2)) hμ
        (fun p hp => hhess (a i) (hai i) p (hball hp).2)
    · exact fun p hp => (hball hp).1
  obtain ⟨η, hη, hsub⟩ := Localization.neighborhood_basin hF xstar hmin huniq
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hrpos))
  refine ⟨F xstar + η, by linarith, fun t _ htb x y hxy => ?_⟩
  exact PlanarMaxRegular.no_segment_frontier_of_local_strictConvex (convex_continuous hF) hs
    (fun p hp => hsub (le_trans hp htb)) x y hxy

/-- For a matrix with nonzero Gram determinant, every solution of $Ml=b$ is
$(M^TM)^{-1}M^Tb$. -/
theorem gram_solution {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix (Fin 3) ι ℝ)
    (h : (Mᵀ * M).det ≠ 0) (l : ι → ℝ) (b : Fin 3 → ℝ) (hl : M *ᵥ l = b) :
    l = (Mᵀ * M)⁻¹ *ᵥ (Mᵀ *ᵥ b) := by
  rw [← hl, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr h), Matrix.one_mulVec]

/-- Full column rank gives a nonzero Gram determinant. -/
theorem gram_det_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix (Fin 3) ι ℝ)
    (h : Function.Injective M.mulVec) : (Mᵀ * M).det ≠ 0 := by
  intro hd
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  have h0 : v ⬝ᵥ ((Mᵀ * M) *ᵥ v) = 0 := by rw [hMv, dotProduct_zero]
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
    dotProduct_self_eq_zero] at h0
  exact hv (h (h0.trans (Matrix.mulVec_zero M).symm))

/-- Components of the augmented gradient matrix applied to a weight vector. -/
theorem augmented_mulVec {m : ℕ} (f : Fin m → Vec 2 → ℝ) (I : Finset (Fin m))
    (A : Vec 2 → Matrix (Fin 3) I ℝ)
    (hA : ∀ p, A p = Matrix.of fun (r : Fin 3) (i : I) =>
      ![coordinateGradient (f i) p 0, coordinateGradient (f i) p 1, 1] r)
    (p : Vec 2) (l : I → ℝ) :
    A p *ᵥ l = ![(∑ i, l i • coordinateGradient (f i) p) 0,
      (∑ i, l i • coordinateGradient (f i) p) 1, ∑ i, l i] := by
  ext r
  fin_cases r <;>
    simp [hA, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

/-- Affine independence of the gradients $\nabla f_i(x)$, $i\in I$, makes the augmented matrix
$A(x)$ with columns $(\nabla f_i(x),1)$ of full column rank. -/
theorem augmented_injective {m : ℕ} (f : Fin m → Vec 2 → ℝ) (I : Finset (Fin m))
    (A : Vec 2 → Matrix (Fin 3) I ℝ)
    (hA : ∀ p, A p = Matrix.of fun (r : Fin 3) (i : I) =>
      ![coordinateGradient (f i) p 0, coordinateGradient (f i) p 1, 1] r)
    (x : Vec 2) (hind : AffineIndependent ℝ fun i : I => coordinateGradient (f i) x) :
    Function.Injective (A x).mulVec := by
  intro u v huv
  have h0 : A x *ᵥ (u - v) = 0 := by rw [Matrix.mulVec_sub, huv, sub_self]
  rw [augmented_mulVec f I A hA] at h0
  have hs : ∑ i, (u - v) i = 0 := by simpa using congrFun h0 2
  have hg : ∑ i, (u - v) i • coordinateGradient (f i) x = 0 := by
    ext j
    fin_cases j
    · simpa using congrFun h0 0
    · simpa using congrFun h0 1
  have hw := (affineIndependent_iff_of_fintype ℝ _).mp hind (u - v) hs
    (by rw [Finset.weightedVSub_eq_linear_combination _ hs]; exact hg)
  funext i
  have := hw i
  simp only [Pi.sub_apply] at this
  linarith

/-- With $C^2$ branches on an open set $U\ni x$, the augmented matrix $A$ is continuous at $x$. -/
theorem augmented_continuousAt {m : ℕ} (f : Fin m → Vec 2 → ℝ) (U : Set (Vec 2)) (hU : IsOpen U)
    {x : Vec 2} (hxU : x ∈ U) (hf : ∀ i, ContDiffOn ℝ 2 (f i) U) (I : Finset (Fin m))
    (A : Vec 2 → Matrix (Fin 3) I ℝ)
    (hA : ∀ p, A p = Matrix.of fun (r : Fin 3) (i : I) =>
      ![coordinateGradient (f i) p 0, coordinateGradient (f i) p 1, 1] r) :
    ContinuousAt A x := by
  have hcg : ∀ i : I, ContinuousAt (coordinateGradient (f i)) x := fun i =>
    (PlanarCrossing.contDiffAt_coordinateGradient
      ((hf i).contDiffAt (hU.mem_nhds hxU))).continuousAt
  have hfun : A = fun p => Matrix.of fun (r : Fin 3) (i : I) =>
      ![coordinateGradient (f i) p 0, coordinateGradient (f i) p 1, 1] r := funext hA
  rw [hfun]
  refine continuousAt_pi.mpr fun r => continuousAt_pi.mpr fun i => ?_
  fin_cases r
  · exact ((continuous_apply 0).continuousAt).comp (hcg i)
  · exact ((continuous_apply 1).continuousAt).comp (hcg i)
  · exact continuousAt_const

open ConvexSubdifferential AffineCriticalObjective in
/-- Item `A/local/disp/012` (`paper/sections/local.tex:328-330`), in the proof of Corollary
`art:planar-max`.

Under the assumptions of the corollary, let $A(x)$ be the $3\times|I_*|$ matrix with columns
$(\nabla f_i(x),1)$, $i\in I_*$. Affine independence makes $A(x_*)$ full column rank, and this
persists nearby; there, if $A(p)\lambda=(0,0,1)^T$ is solvable, its unique solution is
\[ \lambda(p)=(A(p)^TA(p))^{-1}A(p)^T(0,0,1)^T. \] -/
theorem planar_max_barycentric (F : Vec 2 → ℝ) (_hF : ConvexOn ℝ univ F) (xstar : Vec 2)
    (_hmin : ∀ x, F xstar ≤ F x) (_huniq : ∀ x, F x = F xstar → x = xstar)
    {m : ℕ} (f : Fin m → Vec 2 → ℝ) (U : Set (Vec 2)) (hU : IsOpen U) (hxU : xstar ∈ U)
    (hf : ∀ i, ConvexOn ℝ U (f i) ∧ ContDiffOn ℝ 2 (f i) U)
    (_hmax : ∀ x ∈ U, IsGreatest (Set.range fun i => f i x) (F x))
    (_hcontour : ∃ b, F xstar < b ∧ ∀ t, F xstar < t → t ≤ b →
      ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {z | F z ≤ t} → x = y)
    (I : Finset (Fin m)) (_hI : I = Finset.univ.filter fun i => f i xstar = F xstar)
    (hind : AffineIndependent ℝ fun i : I => coordinateGradient (f i) xstar)
    (lam : I → ℝ) (_hpos : ∀ i, 0 < lam i) (_hsum : ∑ i, lam i = 1)
    (_hzero : ∑ i, lam i • coordinateGradient (f i) xstar = 0)
    (A : Vec 2 → Matrix (Fin 3) I ℝ)
    (hA : ∀ p, A p = Matrix.of fun (r : Fin 3) (i : I) =>
      ![coordinateGradient (f i) p 0, coordinateGradient (f i) p 1, 1] r) :
    Function.Injective (A xstar).mulVec ∧
      ∀ᶠ p in 𝓝 xstar, Function.Injective (A p).mulVec ∧
        ∀ l : I → ℝ, A p *ᵥ l = ![0, 0, 1] →
          l = ((A p)ᵀ * A p)⁻¹ *ᵥ ((A p)ᵀ *ᵥ ![0, 0, 1]) := by
  classical
  have hinj := augmented_injective f I A hA xstar hind
  have hAc := augmented_continuousAt f U hU hxU (fun i => (hf i).2) I A hA
  have hdetc : ContinuousAt (fun p => ((A p)ᵀ * A p).det) xstar :=
    ((continuous_id.matrix_transpose.matrix_mul continuous_id).matrix_det.continuousAt).comp
      (f := A) hAc
  have hev : ∀ᶠ p in 𝓝 xstar, ((A p)ᵀ * A p).det ≠ 0 :=
    hdetc.eventually (isOpen_ne.mem_nhds (gram_det_ne_zero _ hinj))
  refine ⟨hinj, ?_⟩
  filter_upwards [hev] with p hp
  refine ⟨fun u v huv => ?_, fun l hl => gram_solution (A p) hp l _ hl⟩
  rw [gram_solution (A p) hp u _ rfl, gram_solution (A p) hp v _ rfl, huv]


open ConvexSubdifferential AffineCriticalObjective in
/-- Item `A/local/prose/037` (`paper/sections/local.tex:296-299`), "affine independence makes that
balance unique and continuous": continuity. It is also the undisplayed claim of
`paper/sections/local.tex:331` in the proof of Corollary `art:planar-max`: "This expression is
continuous and equals $\lambda^*$ at $x_*$."

Under the assumptions of the corollary, with $A(x)$ as in display `disp/012`, the balance
$\lambda(p)=(A(p)^TA(p))^{-1}A(p)^T(0,0,1)^T$ is continuous at $x_*$ and
$\lambda(x_*)=\lambda^*$. -/
theorem planar_max_balance_continuous (F : Vec 2 → ℝ) (_hF : ConvexOn ℝ univ F) (xstar : Vec 2)
    (_hmin : ∀ x, F xstar ≤ F x) (_huniq : ∀ x, F x = F xstar → x = xstar)
    {m : ℕ} (f : Fin m → Vec 2 → ℝ) (U : Set (Vec 2)) (hU : IsOpen U) (hxU : xstar ∈ U)
    (hf : ∀ i, ConvexOn ℝ U (f i) ∧ ContDiffOn ℝ 2 (f i) U)
    (_hmax : ∀ x ∈ U, IsGreatest (Set.range fun i => f i x) (F x))
    (_hcontour : ∃ b, F xstar < b ∧ ∀ t, F xstar < t → t ≤ b →
      ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {z | F z ≤ t} → x = y)
    (I : Finset (Fin m)) (_hI : I = Finset.univ.filter fun i => f i xstar = F xstar)
    (hind : AffineIndependent ℝ fun i : I => coordinateGradient (f i) xstar)
    (lam : I → ℝ) (_hpos : ∀ i, 0 < lam i) (hsum : ∑ i, lam i = 1)
    (hzero : ∑ i, lam i • coordinateGradient (f i) xstar = 0)
    (A : Vec 2 → Matrix (Fin 3) I ℝ)
    (hA : ∀ p, A p = Matrix.of fun (r : Fin 3) (i : I) =>
      ![coordinateGradient (f i) p 0, coordinateGradient (f i) p 1, 1] r) :
    ContinuousAt (fun p => ((A p)ᵀ * A p)⁻¹ *ᵥ ((A p)ᵀ *ᵥ ![0, 0, 1])) xstar ∧
      ((A xstar)ᵀ * A xstar)⁻¹ *ᵥ ((A xstar)ᵀ *ᵥ ![0, 0, 1]) = lam := by
  classical
  have hinj := augmented_injective f I A hA xstar hind
  have hAc := augmented_continuousAt f U hU hxU (fun i => (hf i).2) I A hA
  have hdet := gram_det_ne_zero (A xstar) hinj
  refine ⟨?_, ?_⟩
  · have hG : ContinuousAt (fun p => (A p)ᵀ * A p) xstar :=
      ((continuous_id.matrix_transpose.matrix_mul continuous_id).continuousAt).comp (f := A) hAc
    have hinv : ContinuousAt (fun p => ((A p)ᵀ * A p)⁻¹) xstar :=
      (continuousAt_matrix_inv _
        (by simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hdet)).comp hG
    have hv : ContinuousAt (fun p => (A p)ᵀ *ᵥ ![0, 0, 1]) xstar :=
      ((continuous_id.matrix_transpose.matrix_mulVec continuous_const).continuousAt).comp
        (f := A) hAc
    exact (continuous_fst.matrix_mulVec continuous_snd).continuousAt.comp (hinv.prodMk_nhds hv)
  · have hsol : A xstar *ᵥ lam = ![0, 0, 1] := by
      rw [augmented_mulVec f I A hA, hzero, hsum]
      simp
    exact (gram_solution (A xstar) hdet lam _ hsol).symm

open ConvexSubdifferential AffineCriticalObjective in
/-- Item `A/local/prose/037` (`paper/sections/local.tex:296-299`), anchor "The extra
affine-correctness condition can be verified from the active models".

Under the assumptions of Corollary `art:planar-max` (the contour hypothesis is not used): near
$x_*$, every affine-critical point is a minimizer (affine correctness), and at a nearby
affine-critical point no branch of $I_*$ is lost ("an affine balance cannot lose a branch nearby
without losing stationarity"). Uniqueness of the balance is display `disp/012`
(`planar_max_barycentric`), its continuity `planar_max_balance_continuous`. -/
theorem planar_max_affine_correct_near (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (xstar : Vec 2)
    (_hmin : ∀ x, F xstar ≤ F x) (_huniq : ∀ x, F x = F xstar → x = xstar)
    {m : ℕ} (f : Fin m → Vec 2 → ℝ) (U : Set (Vec 2)) (hU : IsOpen U) (hxU : xstar ∈ U)
    (hf : ∀ i, ConvexOn ℝ U (f i) ∧ ContDiffOn ℝ 2 (f i) U)
    (hmax : ∀ x ∈ U, IsGreatest (Set.range fun i => f i x) (F x))
    (_hcontour : ∃ b, F xstar < b ∧ ∀ t, F xstar < t → t ≤ b →
      ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {z | F z ≤ t} → x = y)
    (I : Finset (Fin m)) (hI : I = Finset.univ.filter fun i => f i xstar = F xstar)
    (hind : AffineIndependent ℝ fun i : I => coordinateGradient (f i) xstar)
    (lam : I → ℝ) (hpos : ∀ i, 0 < lam i) (hsum : ∑ i, lam i = 1)
    (hzero : ∑ i, lam i • coordinateGradient (f i) xstar = 0) :
    ∀ᶠ p in 𝓝 xstar, (IsAffineCritical F p → p ∈ argmin F) ∧
      (IsAffineCritical F p → ∀ i ∈ I, f i p = F p) := by
  have hrep : LocalFiniteMax F f xstar := by
    filter_upwards [hU.mem_nhds hxU] with z hz using hmax z hz
  have hIa : I = activeIndices F f xstar := hI
  subst hIa
  obtain ⟨hind', w, hw, hws, hwz⟩ := active_family_conversion f xstar hind lam hpos hsum hzero
  set a := activeIndexMap F f xstar
  have hd : ∀ p ∈ U, ∀ i, HasFDerivAt (f i) (gradientFunctional (coordinateGradient (f i) p)) p :=
    fun p hp i => hasFDerivAt_coordinateGradient
      (((hf i).2.contDiffAt (hU.mem_nhds hp)).differentiableAt (by norm_num))
  have hr := localFiniteMax_restrict_active (convex_continuous hF).continuousAt
    (fun i => (hd xstar hxU i).continuousAt) hrep
  have hg : ∀ᶠ p in 𝓝 xstar, ∀ i, HasFDerivAt (f (a i))
      (gradientFunctional ((fun p i => coordinateGradient (f (a i)) p) p i)) p := by
    filter_upwards [hU.mem_nhds hxU] with p hp i
    exact hd p hp (a i)
  have hc : ∀ i, ContinuousAt (fun p => (fun p i => coordinateGradient (f (a i)) p) p i) xstar :=
    fun i => (PlanarCrossing.contDiffAt_coordinateGradient
      ((hf (a i)).2.contDiffAt (hU.mem_nhds hxU))).continuousAt
  have hbary := local_affine_critical_correctness hF (fun p i => coordinateGradient (f (a i)) p)
    xstar hr hg hc hind' w hw hws hwz
  filter_upwards [hbary] with p hp
  refine ⟨fun hcrit => hp.2.1.mp ((isAffineCritical_iff_coordinate_affineSpan F p).mp hcrit),
    fun hcrit i hi => ?_⟩
  have hall := hp.2.2 ((isAffineCritical_iff_coordinate_affineSpan F p).mp hcrit)
  have hir : i ∈ Set.range a := by rw [range_activeIndexMap]; exact hi
  obtain ⟨j, rfl⟩ := hir
  have hj : j ∈ activeIndices F (fun j => f (a j)) p := by rw [hall]; exact Finset.mem_univ j
  exact (mem_activeIndices (F := F) (f := fun j => f (a j))).mp hj

open ConvexSubdifferential AffineCriticalObjective in
/-- Item `A/local/prose/038` (`paper/sections/local.tex:299-301`), anchor "same assumptions leave
at most two active branches".

Under the assumptions of Corollary `art:planar-max` (contour hypothesis not used), near $x_*$:
the branches inactive at $x_*$ stay inactive, and at every point that is not affine critical at
most two branches of $I_*$ are active and $F$ has the regular switching structure of Theorem
`art:planar-cluster` (smooth, or a convex two-branch chart with independent gradients). -/
theorem planar_max_regular_near (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (xstar : Vec 2)
    (_hmin : ∀ x, F xstar ≤ F x) (_huniq : ∀ x, F x = F xstar → x = xstar)
    {m : ℕ} (f : Fin m → Vec 2 → ℝ) (U : Set (Vec 2)) (hU : IsOpen U) (hxU : xstar ∈ U)
    (hf : ∀ i, ConvexOn ℝ U (f i) ∧ ContDiffOn ℝ 2 (f i) U)
    (hmax : ∀ x ∈ U, IsGreatest (Set.range fun i => f i x) (F x))
    (_hcontour : ∃ b, F xstar < b ∧ ∀ t, F xstar < t → t ≤ b →
      ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {z | F z ≤ t} → x = y)
    (I : Finset (Fin m)) (hI : I = Finset.univ.filter fun i => f i xstar = F xstar)
    (hind : AffineIndependent ℝ fun i : I => coordinateGradient (f i) xstar)
    (lam : I → ℝ) (hpos : ∀ i, 0 < lam i) (hsum : ∑ i, lam i = 1)
    (hzero : ∑ i, lam i • coordinateGradient (f i) xstar = 0) :
    ∀ᶠ p in 𝓝 xstar, (∀ i ∉ I, f i p < F p) ∧
      (¬ IsAffineCritical F p → (I.filter fun i => f i p = F p).card ≤ 2 ∧
        (ContDiffAt ℝ 2 F p ∨ PlanarCornerCharts.ConvexTwoBranchRegularAt F p)) := by
  classical
  have hrep : LocalFiniteMax F f xstar := by
    filter_upwards [hU.mem_nhds hxU] with z hz using hmax z hz
  have hIa : I = activeIndices F f xstar := hI
  subst hIa
  obtain ⟨hind', w, hw, hws, hwz⟩ := active_family_conversion f xstar hind lam hpos hsum hzero
  set a := activeIndexMap F f xstar
  set e := (activeIndices F f xstar).orderIsoOfFin rfl
  have he : ∀ j, ((e j : activeIndices F f xstar) : Fin m) = a j :=
    fun j => Finset.coe_orderIsoOfFin_apply _ _ j
  have hd : ∀ p ∈ U, ∀ i, HasFDerivAt (f i) (gradientFunctional (coordinateGradient (f i) p)) p :=
    fun p hp i => hasFDerivAt_coordinateGradient
      (((hf i).2.contDiffAt (hU.mem_nhds hp)).differentiableAt (by norm_num))
  have hr := localFiniteMax_restrict_active (convex_continuous hF).continuousAt
    (fun i => (hd xstar hxU i).continuousAt) hrep
  have hg : ∀ᶠ p in 𝓝 xstar, ∀ i, HasFDerivAt (f (a i))
      (gradientFunctional ((fun p i => coordinateGradient (f (a i)) p) p i)) p := by
    filter_upwards [hU.mem_nhds hxU] with p hp i
    exact hd p hp (a i)
  have hc : ∀ i, ContinuousAt (fun p => (fun p i => coordinateGradient (f (a i)) p) p i) xstar :=
    fun i => (PlanarCrossing.contDiffAt_coordinateGradient
      ((hf (a i)).2.contDiffAt (hU.mem_nhds hxU))).continuousAt
  have hbary := local_affine_critical_correctness hF (fun p i => coordinateGradient (f (a i)) p)
    xstar hr hg hc hind' w hw hws hwz
  have hsub := activeIndices_eventually_subset (convex_continuous hF).continuousAt
    (fun i => (hd xstar hxU i).continuousAt) hrep
  filter_upwards [hbary, hU.mem_nhds hxU, hr.eventually, hrep.eventually, hsub]
    with p hp hpU hrp hrepp hsubp
  refine ⟨fun i hi => ?_, fun hn => ⟨?_, ?_⟩⟩
  · have hle : f i p ≤ F p := (hrepp.self_of_nhds).2 ⟨i, rfl⟩
    refine lt_of_le_of_ne hle fun heq => hi (hsubp (mem_activeIndices.mpr heq))
  · -- at most two active branches
    set S := (activeIndices F f xstar).filter fun i => f i p = F p with hSdef
    have hSI : ∀ s ∈ S, s ∈ activeIndices F f xstar := fun s hs => (Finset.mem_filter.mp hs).1
    let φ : S ↪ Fin (activeIndices F f xstar).card :=
      ⟨fun s => e.symm ⟨s.1, hSI s.1 s.2⟩, fun s t hst => by
        have := congrArg (fun j => ((e j : activeIndices F f xstar) : Fin m)) hst
        simp only [OrderIso.apply_symm_apply] at this
        exact Subtype.ext this⟩
    have hφ : ∀ s : S, a (φ s) = s := by
      intro s
      rw [← he]
      simp [φ]
    have hindS : AffineIndependent ℝ fun s : S => coordinateGradient (f s) p := by
      have h := hp.1.comp_embedding φ
      convert h using 1
      funext s
      simp only [Function.comp_apply]
      rw [hφ s]
    have hsupS : ∀ s : S, coordinateGradient (f s) p ∈ subdifferential F p := fun s =>
      active_gradient_supports hF hrepp (hd p hpU) (mem_activeIndices.mpr (Finset.mem_filter.mp s.2).2)
    have h0 : (0 : Vec 2) ∉ affineSpan ℝ (Set.range fun s : S => coordinateGradient (f s) p) := by
      intro hz
      apply hn
      rw [isAffineCritical_iff_coordinate_affineSpan]
      exact affineSpan_mono ℝ (by rintro _ ⟨s, rfl⟩; exact hsupS s) hz
    set q := Fintype.equivFin S
    have hcard := PlanarActiveGeometry.cardinal_le_two_of_affineIndependent_not_critical
      ((fun s : S => coordinateGradient (f s) p) ∘ q.symm)
      (hindS.comp_embedding q.symm.toEmbedding)
      (by rwa [EquivLike.range_comp])
    simpa [Fintype.card_coe] using hcard
  · exact PlanarMaxRegular.regular_of_finite_max_independent hF hU hpU (fun i => hf (a i)) hrp
      hp.1 hn

/-! ### The planar construction sketch (`local.tex:170-212`) -/

/-- Item `A/local/prose/023` (`paper/sections/local.tex:170-171`), anchor "prohibit long accepted
chords with vanishing value decrease".

For an admissible run with compact initial sublevel whose values decrease to a level $\ell$ above
the minimum ($F(y)<\ell$ for some $y$) at which the boundary of $\{F\le\ell\}$ contains no
nontrivial segment: the value decreases $\Delta_k=F(x_k)-F(x_{k+1})$ vanish and so do the accepted
chords $x_{k+1}-x_k$. -/
theorem strict_contours_short_chords {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (hK : IsCompact {x | F x ≤ F (R.x 0)}) (ℓ : ℝ)
    (hℓ : Tendsto (fun k => F (R.x k)) atTop (𝓝 ℓ)) (hpos : ∃ y, F y < ℓ)
    (hstrict : ∀ x z : Vec n, segment ℝ x z ⊆ frontier {w | F w ≤ ℓ} → x = z) :
    Tendsto (fun k => F (R.x k) - F (R.x (k + 1))) atTop (𝓝 0) ∧
      Tendsto (fun k => R.x (k + 1) - R.x k) atTop (𝓝 0) := by
  refine ⟨?_, R.differences_tendsto_zero_of_strict_contour hK ℓ hℓ hpos hstrict⟩
  have h := hℓ.sub (hℓ.comp (tendsto_add_atTop_nat 1))
  simpa using h

/-- Item `A/local/prose/024` (`paper/sections/local.tex:172-173`), anchor "Regular two-branch
switching makes each positive-level corner move"; and Item `A/local/prose/027`
(`paper/sections/local.tex:178-184`), anchor "Here is the construction near a compact
non-affine-critical part" ("noncritical" before 15 October 2026, M38).

At a two-branch corner $p_0$ ($F=\max\{f_1,f_2\}$ near $p_0$ with $C^2$ branches, both active,
linearly independent gradients) the corner moves smoothly with the level: there is a curve $p(t)$,
$C^2$ at $t=F(p_0)$, with $p(F(p_0))=p_0$ and $f_1(p(t))=f_2(p(t))=F(p(t))=t$ for $t$ near
$F(p_0)$; its velocity $v(t)=p'(t)$ satisfies $\nabla f_i(p(t))^Tv(t)=1$ for both branches, so
$-v(t)$ is an equal-rate descent direction ($\nabla f_i(p(t))^T(-v(t))=-1$). -/
theorem corner_moves_with_level {F : Vec 2 → ℝ} {p₀ : Vec 2} (V : Set (Vec 2)) (hV : IsOpen V)
    (hp₀ : p₀ ∈ V) (f₁ f₂ : Vec 2 → ℝ) (hf₁ : ContDiffOn ℝ 2 f₁ V) (hf₂ : ContDiffOn ℝ 2 f₂ V)
    (hmax : ∀ z ∈ V, F z = max (f₁ z) (f₂ z)) (h₁ : f₁ p₀ = F p₀) (h₂ : f₂ p₀ = F p₀)
    (hind : LinearIndependent ℝ ![coordinateGradient f₁ p₀, coordinateGradient f₂ p₀]) :
    ∃ c : ℝ → Vec 2, c (F p₀) = p₀ ∧ ContDiffAt ℝ 2 c (F p₀) ∧
      ∀ᶠ t in 𝓝 (F p₀), f₁ (c t) = t ∧ f₂ (c t) = t ∧ F (c t) = t ∧
        dot (coordinateGradient f₁ (c t)) (deriv c t) = 1 ∧
        dot (coordinateGradient f₂ (c t)) (deriv c t) = 1 ∧
        dot (coordinateGradient f₁ (c t)) (-deriv c t) = -1 ∧
        dot (coordinateGradient f₂ (c t)) (-deriv c t) = -1 := by
  set f : Fin 2 → Vec 2 → ℝ := ![f₁, f₂] with hfdef
  have hC : ∀ i, ContDiffAt ℝ 2 (f i) p₀ := by
    intro i
    fin_cases i
    · exact hf₁.contDiffAt (hV.mem_nhds hp₀)
    · exact hf₂.contDiffAt (hV.mem_nhds hp₀)
  have hg₁ : HasFDerivAt (f 0) (gradientFunctional (coordinateGradient f₁ p₀)) p₀ :=
    hasFDerivAt_coordinateGradient ((hC 0).differentiableAt (by norm_num))
  have hg₂ : HasFDerivAt (f 1) (gradientFunctional (coordinateGradient f₂ p₀)) p₀ :=
    hasFDerivAt_coordinateGradient ((hC 1).differentiableAt (by norm_num))
  obtain ⟨c, hc, hcC, hlevel, _⟩ := PlanarCornerCharts.exists_corner_chart hC hg₁ hg₂
    (pairDet_ne_zero_of_linearIndependent hind) h₁ h₂
  refine ⟨c, hc, hcC, ?_⟩
  have hcdiff : ∀ᶠ t in 𝓝 (F p₀), DifferentiableAt ℝ c t :=
    (hcC.eventually (by norm_num)).mono fun t ht => ht.differentiableAt (by norm_num)
  have hcV : ∀ᶠ t in 𝓝 (F p₀), c t ∈ V :=
    hcC.continuousAt.eventually_mem (by rw [hc]; exact hV.mem_nhds hp₀)
  filter_upwards [hcdiff, hcV, hlevel.eventually_nhds, hlevel] with t hdt htV hlt hlev
  have hgrad : ∀ i, HasFDerivAt (f i) (gradientFunctional (coordinateGradient (f i) (c t))) (c t) := by
    intro i
    fin_cases i
    · exact hasFDerivAt_coordinateGradient
        ((hf₁.contDiffAt (hV.mem_nhds htV)).differentiableAt (by norm_num))
    · exact hasFDerivAt_coordinateGradient
        ((hf₂.contDiffAt (hV.mem_nhds htV)).differentiableAt (by norm_num))
  have hpair := PlanarCornerCharts.curve_velocity_pairing hdt.hasDerivAt hgrad hlt
  have e1 : dot (coordinateGradient f₁ (c t)) (deriv c t) = 1 := hpair 0
  have e2 : dot (coordinateGradient f₂ (c t)) (deriv c t) = 1 := hpair 1
  have l1 : f₁ (c t) = t := hlev 0
  have l2 : f₂ (c t) = t := hlev 1
  have hneg : ∀ u : Vec 2, dot u (-deriv c t) = -dot u (deriv c t) := fun u => by
    simp only [dot, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
  refine ⟨l1, l2, by rw [hmax _ htV, l1, l2, max_self], e1, e2, ?_, ?_⟩
  · rw [hneg, e1]
  · rw [hneg, e2]

open AffineCriticalObjective in
/-- Item `A/local/prose/028` (`paper/sections/local.tex:184-187`), anchor "There are finitely many
such corners", first claim.

On a compact set $C$ contained in one level $\{F=\ell\}$, at each point of which $F$ is $C^2$
nearby or has the convex two-branch structure of Theorem `art:planar-cluster`, there are only
finitely many corners (points where $F$ is not differentiable). -/
theorem finitely_many_corners {F : Vec 2 → ℝ} (C : Set (Vec 2)) (ℓ : ℝ) (hC : IsCompact C)
    (hlevel : ∀ p ∈ C, F p = ℓ)
    (hreg : ∀ p ∈ C,
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p])) :
    {p ∈ C | ¬ DifferentiableAt ℝ F p}.Finite :=
  PlanarCornerCharts.finite_nonsmooth_on_compact_level hC hlevel
    (fun p hp => (regular_of_paper (hreg p hp)).imp id (fun h => h.to_regular))

/-- Item `A/local/prose/028` (`paper/sections/local.tex:184-187`), second claim: "Their
supporting-normal arcs are disjoint: a common normal at two corners would expose the whole
segment between them, contrary to the strict-contour assumption."

For finite convex $F$ and two points $p,z$ of the level $\{F=\ell\}$, a common nonzero supporting
normal $a$ of $\{F\le\ell\}$ at $p$ and at $z$ exposes the whole segment $[p,z]$ in the boundary
of $\{F\le\ell\}$; under the strict-contour assumption at $\ell$ this forces $p=z$. -/
theorem common_normal_exposes_segment {F : Vec 2 → ℝ} (hF : ConvexOn ℝ univ F) (ℓ : ℝ)
    (p z a : Vec 2) (hp : F p = ℓ) (hz : F z = ℓ) (ha : a ≠ 0)
    (hap : ∀ y, F y ≤ ℓ → dot a (y - p) ≤ 0) (haz : ∀ y, F y ≤ ℓ → dot a (y - z) ≤ 0) :
    segment ℝ p z ⊆ frontier {y | F y ≤ ℓ} ∧
      ((∀ x y : Vec 2, segment ℝ x y ⊆ frontier {w | F w ≤ ℓ} → x = y) → p = z) := by
  have hKc : Convex ℝ {y | F y ≤ ℓ} := by
    simpa only [mem_univ, true_and] using hF.convex_le ℓ
  have hKcl : IsClosed {y | F y ≤ ℓ} := isClosed_le (convex_continuous hF) continuous_const
  have hsp : PlanarNormalGeometry.SupportsSetAt {y | F y ≤ ℓ} p a :=
    ⟨show F p ≤ ℓ from hp.le, ha, fun y hy => hap y hy⟩
  have hsz : PlanarNormalGeometry.SupportsSetAt {y | F y ≤ ℓ} z a :=
    ⟨show F z ≤ ℓ from hz.le, ha, fun y hy => haz y hy⟩
  have hseg : segment ℝ p z ⊆ frontier {y | F y ≤ ℓ} := fun w hw =>
    PlanarNormalGeometry.mem_frontier_of_support hKcl
      (PlanarNormalGeometry.segment_support_of_common_normal hKc hsp hsz w hw)
  exact ⟨hseg, fun hstrict => hstrict p z hseg⟩

/-- Item `A/local/prose/031` (`paper/sections/local.tex:199-200`), anchor "The one-dimensional
tangent is essential here".

If a linear map $Dw$ maps the tangent vector $T$ into its own line ($Dw\,T=cT$), then for a
tangent step $s=rT$, $Dw\,s$ is parallel to $s$, so $\det(s,Dw\,s)=0$
(`HomogeneousPlanar.pairDet a b` $=a_1b_2-a_2b_1=\det(a,b)$). -/
theorem tangent_step_det_zero (M : Mat 2) (T : Vec 2) (c : ℝ) (hT : M *ᵥ T = c • T) (s : Vec 2)
    (r : ℝ) (hs : s = r • T) :
    M *ᵥ s = c • s ∧ HomogeneousPlanar.pairDet s (M *ᵥ s) = 0 := by
  have hMs : M *ᵥ s = c • s := by
    rw [hs, Matrix.mulVec_smul, hT, smul_comm]
  refine ⟨hMs, ?_⟩
  rw [hMs]
  simp only [HomogeneousPlanar.pairDet, Pi.smul_apply, smul_eq_mul]
  ring

/-- Item `A/local/prose/033` (`paper/sections/local.tex:208-209`), anchor "Since Armijo gives
$d\le(F(x)-F(z))/c_1$", first part: for an eligible pair (constants $c_1>0$, $c_2$),
$d=-g^Ts\le(F(x)-F(z))/c_1$. -/
theorem armijo_charges_transport {n : ℕ} (F : Vec n → ℝ) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁)
    (x z g h : Vec n) (hp : TransportedCertificate.EligiblePair F c₁ c₂ x z g h) :
    -dot g (z - x) ≤ (F x - F z) / c₁ := by
  rw [le_div_iff₀ hc₁]
  have h := hp.armijo
  simp only [TransportedCertificate.pairDecrease, TransportedCertificate.pairStep] at h
  linarith

/-- Item `A/local/prose/033` (`paper/sections/local.tex:208-209`), second part: "transport is
charged to summable objective decreases". For an admissible run whose values converge to $\ell$,
the predicted decreases $d_k$ are summable with $\sum_kd_k\le(F(x_0)-\ell)/c_1$, so a transport
budget $|\log\lambda_k|\le Cd_k$ has finite total. -/
theorem run_transport_budget {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (ℓ : ℝ)
    (hℓ : Tendsto (fun k => F (R.x k)) atTop (𝓝 ℓ)) :
    Summable R.d ∧ ∑' k, R.d k ≤ (F (R.x 0) - ℓ) / R.c₁ := by
  have hs := R.summable_predicted_decreases_of_value_limit ℓ hℓ
  refine ⟨hs, hs.tsum_le_of_sum_range_le fun N => ?_⟩
  have hL : ∀ k, ℓ ≤ F (R.x k) := R.objective_antitone.le_of_tendsto hℓ
  simpa using R.finite_budget_le ℓ hL 0 N


/-! ### Theorem `art:nonradial-example` and its proof

The example takes the branches and the objective of display `disp/013` as variables with their
defining equations: `hf` gives $f_0,f_1,f_2$ in the coordinates $u=x_0$, $v=x_1$ and `hF` gives
$F=\max_if_i$. They are the library's `PlanarQuadraticExample.branch` and `objective`
(`example_eq`). -/

/-- The branches and objective of display `disp/013` are the library's
`PlanarQuadraticExample.branch` and `PlanarQuadraticExample.objective`. -/
theorem example_eq (f : Fin 3 → Vec 2 → ℝ)
    (hf : ∀ x : Vec 2, f 0 x = x 0 + x 0 ^ 2 + x 1 ^ 2 / 2 ∧
      f 1 x = x 1 + x 0 ^ 2 / 2 + 3 * x 1 ^ 2 / 2 ∧ f 2 x = -x 0 - x 1 + 3 * x 0 ^ 2 / 2 + x 1 ^ 2)
    (F : Vec 2 → ℝ) (hF : ∀ x, F x = max (f 0 x) (max (f 1 x) (f 2 x))) :
    f = PlanarQuadraticExample.branch ∧ F = PlanarQuadraticExample.objective := by
  have hfe : f = PlanarQuadraticExample.branch := by
    funext i x
    fin_cases i
    · simp [PlanarQuadraticExample.branch, (hf x).1]
    · simp [PlanarQuadraticExample.branch, (hf x).2.1]
    · simp [PlanarQuadraticExample.branch, (hf x).2.2]
  refine ⟨hfe, ?_⟩
  funext x
  rw [hF x, hfe]
  rfl

/-- Item `A/local/theorem/art:nonradial-example` (`paper/sections/local.tex:369-384`), Theorem
`art:nonradial-example` ("Convergence with curved, nonradial switching"), including its display
`A/local/disp/013` (lines 371-377).

For $f_0=u+u^2+\frac12v^2$, $f_1=v+\frac12u^2+\frac32v^2$, $f_2=-u-v+\frac32u^2+v^2$ and
$F=\max_if_i$: every infinite admissible full-BFGS run with $F(x_0)<1/100$ converges in value and
iterates to zero, for arbitrary $H_0\succ0$ and fixed valid Armijo--weak-Wolfe constants.
Nevertheless, the radial secant condition \eqref{art:radial-condition} (with $x_*=0$,
$F_*=F(0)=0$, $N=(h-g)^Tr_z$, $r_z=z$, $T=(h-g)^T(z-x)$) fails on a positive band in every
neighborhood of zero: for every neighborhood $N_0$ of $0$ there is $\eta>0$ such that for every
$C$ some differentiable pair $x,z\in N_0$ with $F_*+\eta\le F(z)\le F(x)$ and $T>0$ has
$N^2>CT$. The obstructing endpoint pairs can themselves be chosen eligible for $c_1=1/4$,
$c_2=1/2$ (`TransportedCertificate.EligiblePair F c₁ c₂ x z g h`: $g=\nabla F(x)$,
$h=\nabla F(z)$, $d=-g^T(z-x)>0$, $c_1d\le F(x)-F(z)\le d$, $(1-c_2)d\le T$). -/
theorem nonradial_example (f : Fin 3 → Vec 2 → ℝ)
    (hf : ∀ x : Vec 2, f 0 x = x 0 + x 0 ^ 2 + x 1 ^ 2 / 2 ∧
      f 1 x = x 1 + x 0 ^ 2 / 2 + 3 * x 1 ^ 2 / 2 ∧ f 2 x = -x 0 - x 1 + 3 * x 0 ^ 2 / 2 + x 1 ^ 2)
    (F : Vec 2 → ℝ) (hF : ∀ x, F x = max (f 0 x) (max (f 1 x) (f 2 x))) :
    (∀ R : AdmissibleBFGSRun 2 F, F (R.x 0) < 1 / 100 →
      Tendsto (fun k => F (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0)) ∧
    ∀ N₀ ∈ 𝓝 (0 : Vec 2), ∃ η : ℝ, 0 < η ∧ ∀ C : ℝ, ∃ x z g h : Vec 2,
      x ∈ N₀ ∧ z ∈ N₀ ∧ F 0 + η ≤ F z ∧ F z ≤ F x ∧
      HasFDerivAt F (gradientFunctional g) x ∧ HasFDerivAt F (gradientFunctional h) z ∧
      0 < dot (h - g) (z - x) ∧ C * dot (h - g) (z - x) < (dot (h - g) z) ^ 2 ∧
      TransportedCertificate.EligiblePair F (1 / 4) (1 / 2) x z g h := by
  obtain ⟨hfe, hFe⟩ := example_eq f hf F hF
  subst hfe hFe
  refine ⟨fun R h0 => PlanarQuadraticExample.fullBFGS_explicit_basin R h0, fun N₀ hN => ?_⟩
  obtain ⟨η, hη, hex⟩ := PlanarQuadraticExample.eligible_radial_unbounded_on_neighborhood hN
  refine ⟨η, hη, fun C => ?_⟩
  obtain ⟨x, z, g, h, H, hx, hz, hband, horder, hpair, _, _, _, hexc⟩ := hex 1 one_pos C
  have ht : 0 < dot (h - g) (z - x) := by
    have hc := hpair.curvature
    have hd := hpair.decrease_pos
    simp only [TransportedCertificate.pairCurvature, TransportedCertificate.pairStep] at hc
    nlinarith
  refine ⟨x, z, g, h, hx, hz, ?_, horder, hpair.gradient_x, hpair.gradient_z, ht, ?_, hpair⟩
  · rw [PlanarQuadraticExample.objective_zero]
    linarith
  · simpa [TransportedCertificate.pairCurvature, TransportedCertificate.pairStep,
      RadialCertificate.radialNumerator] using hexc

/-- Proof of Theorem `art:nonradial-example`, undisplayed claims of
`paper/sections/local.tex:386-389` (not a register item): "The branch Hessians lie between $I$
and $3I$, and $(f_0+f_1+f_2)/3=u^2+v^2$. Thus $F\ge u^2+v^2$, zero is the unique minimizer, and
all positive contours are strict. The active gradients at zero are $(1,0),(0,1),(-1,-1)$, with
positive weights $1/3$." -/
theorem example_model_facts (f : Fin 3 → Vec 2 → ℝ)
    (hf : ∀ x : Vec 2, f 0 x = x 0 + x 0 ^ 2 + x 1 ^ 2 / 2 ∧
      f 1 x = x 1 + x 0 ^ 2 / 2 + 3 * x 1 ^ 2 / 2 ∧ f 2 x = -x 0 - x 1 + 3 * x 0 ^ 2 / 2 + x 1 ^ 2)
    (F : Vec 2 → ℝ) (hF : ∀ x, F x = max (f 0 x) (max (f 1 x) (f 2 x))) :
    (∀ i x, (RadialHessian.matrix (f i) x - 1).PosSemidef ∧
      ((3 : ℝ) • (1 : Mat 2) - RadialHessian.matrix (f i) x).PosSemidef) ∧
    (∀ x : Vec 2, (f 0 x + f 1 x + f 2 x) / 3 = x 0 ^ 2 + x 1 ^ 2) ∧
    (∀ x : Vec 2, x 0 ^ 2 + x 1 ^ 2 ≤ F x) ∧ F 0 = 0 ∧ (∀ x, F 0 ≤ F x) ∧
    (∀ x, F x = F 0 → x = 0) ∧
    (∀ t, 0 < t → ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {z | F z ≤ t} → x = y) ∧
    (∀ i, f i 0 = F 0) ∧
    coordinateGradient (f 0) 0 = ![1, 0] ∧ coordinateGradient (f 1) 0 = ![0, 1] ∧
    coordinateGradient (f 2) 0 = ![-1, -1] ∧
    ∑ i : Fin 3, (1 / 3 : ℝ) • coordinateGradient (f i) 0 = 0 := by
  obtain ⟨hfe, hFe⟩ := example_eq f hf F hF
  subst hfe hFe
  have hsq : ∀ x : Vec 2, sqNorm x = x 0 ^ 2 + x 1 ^ 2 := fun x => by
    simp [sqNorm, Fin.sum_univ_two]
  have hg := fun i => PlanarQuadraticExample.coordinateGradient_eq i (0 : Vec 2)
  obtain ⟨g0, g1, g2⟩ := PlanarQuadraticExample.initial_gradients
  refine ⟨fun i x => PlanarQuadraticExample.branch_actual_hessian_bounds i x, fun x => ?_,
    fun x => (hsq x) ▸ PlanarQuadraticExample.objective_lower x,
    PlanarQuadraticExample.objective_zero, PlanarQuadraticExample.objective_minimum,
    fun x hx => PlanarQuadraticExample.objective_unique_zero x
      (by rwa [PlanarQuadraticExample.objective_zero] at hx),
    fun t _ => PlanarQuadraticExample.strict_contours t, PlanarQuadraticExample.initial_active,
    by rw [hg, g0], by rw [hg, g1], by rw [hg, g2], ?_⟩
  · have h := PlanarQuadraticExample.branch_average x
    rw [Fin.sum_univ_three, hsq] at h
    exact h
  · rw [Fin.sum_univ_three, hg, hg, hg, g0, g1, g2]
    ext j
    fin_cases j <;> norm_num

/-- Proof of Theorem `art:nonradial-example`, undisplayed claims of
`paper/sections/local.tex:390-406` (not a register item): $D=3(1+v-uv)$ is the determinant of
the augmented gradient matrix (rows $\partial_u$, $\partial_v$, $1$); on $|u|,|v|\le1/10$,
$D\ge267/100$ and the three numerators are at least $23/100$, $49/100$, $45/100$; the
coefficients $\lambda_i=$ numerator$_i/D$ sum to one and their weighted gradient is zero;
affine independence, affine correctness and the planar regularity alternative hold throughout
the box; and $\{F\le1/100\}$ lies in the box. -/
theorem example_box_facts (f : Fin 3 → Vec 2 → ℝ)
    (hf : ∀ x : Vec 2, f 0 x = x 0 + x 0 ^ 2 + x 1 ^ 2 / 2 ∧
      f 1 x = x 1 + x 0 ^ 2 / 2 + 3 * x 1 ^ 2 / 2 ∧ f 2 x = -x 0 - x 1 + 3 * x 0 ^ 2 / 2 + x 1 ^ 2)
    (F : Vec 2 → ℝ) (hF : ∀ x, F x = max (f 0 x) (max (f 1 x) (f 2 x))) :
    (∀ x : Vec 2, 3 * (1 + x 1 - x 0 * x 1) = Matrix.det !![
      coordinateGradient (f 0) x 0, coordinateGradient (f 1) x 0, coordinateGradient (f 2) x 0;
      coordinateGradient (f 0) x 1, coordinateGradient (f 1) x 1, coordinateGradient (f 2) x 1;
      1, 1, 1]) ∧
    (∀ x : Vec 2, |x 0| ≤ 1 / 10 → |x 1| ≤ 1 / 10 →
      267 / 100 ≤ 3 * (1 + x 1 - x 0 * x 1) ∧ 23 / 100 ≤ 1 - 4 * x 0 + 3 * x 1 - 7 * x 0 * x 1 ∧
      49 / 100 ≤ 1 + 2 * x 0 - 3 * x 1 - x 0 * x 1 ∧
      45 / 100 ≤ 1 + 2 * x 0 + 3 * x 1 + 5 * x 0 * x 1 ∧
      (∑ i, PlanarQuadraticExample.coefficients x i = 1 ∧
        ∑ i, PlanarQuadraticExample.coefficients x i • coordinateGradient (f i) x = 0) ∧
      AffineIndependent ℝ (fun i => coordinateGradient (f i) x) ∧
      AffineCriticalObjective.AffineCorrectAt F x ∧
      (¬ AffineCriticalObjective.IsAffineCritical F x →
        ContDiffAt ℝ 2 F x ∨ PlanarCornerCharts.ConvexTwoBranchRegularAt F x)) ∧
    ∀ x : Vec 2, F x ≤ 1 / 100 → |x 0| ≤ 1 / 10 ∧ |x 1| ≤ 1 / 10 := by
  obtain ⟨hfe, hFe⟩ := example_eq f hf F hF
  subst hfe hFe
  have hg := fun i x => PlanarQuadraticExample.coordinateGradient_eq i x
  refine ⟨fun x => ?_, fun x hx0 hx1 => ?_, fun x hx => PlanarQuadraticExample.small_sublevel_mem_box hx⟩
  · obtain ⟨g0, g1, g2⟩ := PlanarQuadraticExample.gradient_coordinates x
    rw [hg, hg, hg, g0, g1, g2, Matrix.det_fin_three]
    simp
    ring
  · have hb : x ∈ PlanarQuadraticExample.box := ⟨hx0, hx1⟩
    have hD := (PlanarQuadraticExample.denominator_pos_on_box hb).ne'
    obtain ⟨h1, h2, h3, h4⟩ := PlanarQuadraticExample.coefficient_box_bounds hb
    simp only [PlanarQuadraticExample.denominator, PlanarQuadraticExample.numerator,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons] at h1 h2 h3 h4
    refine ⟨h1, h2, h3, h4, ⟨PlanarQuadraticExample.coefficients_sum hD, ?_⟩, ?_,
      PlanarQuadraticExample.affineCorrect_on_box hb,
      PlanarQuadraticExample.regular_on_box hb⟩
    · simp only [hg]
      exact PlanarQuadraticExample.coefficients_zero hD
    · simp only [hg]
      exact PlanarQuadraticExample.gradient_affineIndependent hD

/-- Item `A/local/disp/014` (`paper/sections/local.tex:393-399`), in the proof of Theorem
`art:nonradial-example`.

With $D=3(1+v-uv)$ ($u=x_0$, $v=x_1$), direct solution of the augmented system
$\sum_i\lambda_i=1$, $\sum_i\lambda_i\nabla f_i(x)=0$ gives, for every solution $\lambda$,
\[ D\lambda_0=1-4u+3v-7uv,\qquad D\lambda_1=1+2u-3v-uv,\qquad D\lambda_2=1+2u+3v+5uv. \] -/
theorem example_coefficients (f : Fin 3 → Vec 2 → ℝ)
    (hf : ∀ x : Vec 2, f 0 x = x 0 + x 0 ^ 2 + x 1 ^ 2 / 2 ∧
      f 1 x = x 1 + x 0 ^ 2 / 2 + 3 * x 1 ^ 2 / 2 ∧ f 2 x = -x 0 - x 1 + 3 * x 0 ^ 2 / 2 + x 1 ^ 2)
    (F : Vec 2 → ℝ) (hF : ∀ x, F x = max (f 0 x) (max (f 1 x) (f 2 x))) (x : Vec 2) (D : ℝ)
    (hD : D = 3 * (1 + x 1 - x 0 * x 1)) (l : Fin 3 → ℝ) (hl1 : ∑ i, l i = 1)
    (hl0 : ∑ i, l i • coordinateGradient (f i) x = 0) :
    D * l 0 = 1 - 4 * x 0 + 3 * x 1 - 7 * x 0 * x 1 ∧
      D * l 1 = 1 + 2 * x 0 - 3 * x 1 - x 0 * x 1 ∧
      D * l 2 = 1 + 2 * x 0 + 3 * x 1 + 5 * x 0 * x 1 := by
  obtain ⟨hfe, -⟩ := example_eq f hf F hF
  subst hfe hD
  have hg := fun i => PlanarQuadraticExample.coordinateGradient_eq i x
  obtain ⟨g0, g1, g2⟩ := PlanarQuadraticExample.gradient_coordinates x
  rw [Fin.sum_univ_three, hg, hg, hg, g0, g1, g2] at hl0
  have e0 := congrFun hl0 0
  have e1 := congrFun hl0 1
  simp at e0 e1
  rw [Fin.sum_univ_three] at hl1
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (2 + x 1) * e0 + (2 * x 0 - 1) * e1 +
      (1 - 4 * x 0 + 3 * x 1 - 7 * x 0 * x 1) * hl1
  · linear_combination (x 1 - 1) * e0 + (2 - x 0) * e1 +
      (1 + 2 * x 0 - 3 * x 1 - x 0 * x 1) * hl1
  · linear_combination (-1 - 2 * x 1) * e0 + (-(1 + x 0)) * e1 +
      (1 + 2 * x 0 + 3 * x 1 + 5 * x 0 * x 1) * hl1

/-- Item `A/local/disp/015` (`paper/sections/local.tex:409-412`), in the proof of Theorem
`art:nonradial-example`.

For $v(u)=\bigl(-1+\sqrt{1+4u+2u^2}\bigr)/2$ (the object defined by the display, `hv`),
\[ v(u)=u-\tfrac12u^2+O(u^3)\qquad(u\to0^+). \] -/
theorem example_tie_expansion (v : ℝ → ℝ)
    (hv : ∀ u, v u = (-1 + Real.sqrt (1 + 4 * u + 2 * u ^ 2)) / 2) :
    (fun u => v u - (u - u ^ 2 / 2)) =O[𝓝[>] 0] (fun u => u ^ 3) := by
  have hve : v = PlanarQuadraticExample.tieHeight := funext fun u => by
    rw [hv u, PlanarQuadraticExample.tieHeight]
  subst hve
  have h := PlanarQuadraticExample.tieHeight_expansion
  convert h using 2 with u
  ring

/-- Proof of Theorem `art:nonradial-example`, undisplayed claim of `paper/sections/local.tex:413`
(not a register item): "This is the positive active tie $f_0=f_1$, with $f_2$ inactive", for
$0<u<1/10$. -/
theorem example_tie (f : Fin 3 → Vec 2 → ℝ)
    (hf : ∀ x : Vec 2, f 0 x = x 0 + x 0 ^ 2 + x 1 ^ 2 / 2 ∧
      f 1 x = x 1 + x 0 ^ 2 / 2 + 3 * x 1 ^ 2 / 2 ∧ f 2 x = -x 0 - x 1 + 3 * x 0 ^ 2 / 2 + x 1 ^ 2)
    (F : Vec 2 → ℝ) (hF : ∀ x, F x = max (f 0 x) (max (f 1 x) (f 2 x))) (v : ℝ → ℝ)
    (hv : ∀ u, v u = (-1 + Real.sqrt (1 + 4 * u + 2 * u ^ 2)) / 2) (u : ℝ) (hu : 0 < u)
    (hu' : u < 1 / 10) :
    0 < v u ∧ f 0 ![u, v u] = F ![u, v u] ∧ f 1 ![u, v u] = F ![u, v u] ∧
      f 2 ![u, v u] < F ![u, v u] := by
  obtain ⟨hfe, hFe⟩ := example_eq f hf F hF
  subst hfe hFe
  have hve : v = PlanarQuadraticExample.tieHeight := funext fun u => by
    rw [hv u, PlanarQuadraticExample.tieHeight]
  subst hve
  exact ⟨PlanarQuadraticExample.tieHeight_pos hu, PlanarQuadraticExample.tie_active hu hu'⟩

/-- Item `A/local/disp/016` (`paper/sections/local.tex:414-417`), in the proof of Theorem
`art:nonradial-example`.

At the tie point $(u,v)$, $v=v(u)$, for small $u$ ($0<u<1/10$):
\[ (\nabla f_0-\nabla f_1)^T(u,v)=(1+u)u-(1+2v)v=\tfrac12u^2-v^2\ne0. \] -/
theorem example_radial_jump (f : Fin 3 → Vec 2 → ℝ)
    (hf : ∀ x : Vec 2, f 0 x = x 0 + x 0 ^ 2 + x 1 ^ 2 / 2 ∧
      f 1 x = x 1 + x 0 ^ 2 / 2 + 3 * x 1 ^ 2 / 2 ∧ f 2 x = -x 0 - x 1 + 3 * x 0 ^ 2 / 2 + x 1 ^ 2)
    (F : Vec 2 → ℝ) (hF : ∀ x, F x = max (f 0 x) (max (f 1 x) (f 2 x))) (v : ℝ → ℝ)
    (hv : ∀ u, v u = (-1 + Real.sqrt (1 + 4 * u + 2 * u ^ 2)) / 2) (u : ℝ) (hu : 0 < u)
    (hu' : u < 1 / 10) :
    dot (coordinateGradient (f 0) ![u, v u] - coordinateGradient (f 1) ![u, v u]) ![u, v u] =
        (1 + u) * u - (1 + 2 * v u) * v u ∧
      (1 + u) * u - (1 + 2 * v u) * v u = u ^ 2 / 2 - v u ^ 2 ∧ u ^ 2 / 2 - v u ^ 2 ≠ 0 := by
  obtain ⟨hfe, -⟩ := example_eq f hf F hF
  subst hfe
  have hve : v = PlanarQuadraticExample.tieHeight := funext fun u => by
    rw [hv u, PlanarQuadraticExample.tieHeight]
  subst hve
  have hg := fun i => PlanarQuadraticExample.coordinateGradient_eq i ![u, PlanarQuadraticExample.tieHeight u]
  have hj := (PlanarQuadraticExample.tie_radial_jump hu.le).1
  have he := PlanarQuadraticExample.tieHeight_equation hu.le
  refine ⟨?_, by nlinarith, (PlanarQuadraticExample.tie_radial_jump_neg hu hu').ne⟩
  rw [hg, hg]
  change dot (PlanarQuadraticExample.gradient 0 (PlanarQuadraticExample.base u) -
    PlanarQuadraticExample.gradient 1 (PlanarQuadraticExample.base u))
      (PlanarQuadraticExample.base u) = _
  rw [hj]
  simp [dot, Fin.sum_univ_two, PlanarQuadraticExample.base]
  ring

/-- Item `A/local/disp/017` (`paper/sections/local.tex:421-426`), in the proof of Theorem
`art:nonradial-example`.

For fixed $0<u<1/10$ and $v=v(u)$, take $x=(u,v+e)$ and $z=(u,v-e)$ with $e>0$ tending to zero.
For all sufficiently small $e>0$: branches 1 and 0, respectively, are uniquely active, so
$g=\nabla F(x)=\nabla f_1(x)$ and $h=\nabla F(z)=\nabla f_0(z)$, and with $s=z-x$,
$d=-g^Ts$, $t=(h-g)^Ts$, $\Delta=F(x)-F(z)$ a direct calculation gives
\[ d=2e(1+3v+3e),\qquad t=2e(1+2v+4e),\qquad \Delta=e(1+4v)+e^2. \] -/
theorem example_pair_values (f : Fin 3 → Vec 2 → ℝ)
    (hf : ∀ x : Vec 2, f 0 x = x 0 + x 0 ^ 2 + x 1 ^ 2 / 2 ∧
      f 1 x = x 1 + x 0 ^ 2 / 2 + 3 * x 1 ^ 2 / 2 ∧ f 2 x = -x 0 - x 1 + 3 * x 0 ^ 2 / 2 + x 1 ^ 2)
    (F : Vec 2 → ℝ) (hF : ∀ x, F x = max (f 0 x) (max (f 1 x) (f 2 x))) (v : ℝ → ℝ)
    (hv : ∀ u, v u = (-1 + Real.sqrt (1 + 4 * u + 2 * u ^ 2)) / 2) (u : ℝ) (hu : 0 < u)
    (hu' : u < 1 / 10) :
    ∀ᶠ e in 𝓝[>] (0 : ℝ), ∀ x z g h : Vec 2, x = ![u, v u + e] → z = ![u, v u - e] →
      g = coordinateGradient (f 1) x → h = coordinateGradient (f 0) z →
      (f 0 x < f 1 x ∧ f 2 x < f 1 x ∧ f 1 z < f 0 z ∧ f 2 z < f 0 z) ∧
      HasFDerivAt F (gradientFunctional g) x ∧ HasFDerivAt F (gradientFunctional h) z ∧
      -dot g (z - x) = 2 * e * (1 + 3 * v u + 3 * e) ∧
      dot (h - g) (z - x) = 2 * e * (1 + 2 * v u + 4 * e) ∧
      F x - F z = e * (1 + 4 * v u) + e ^ 2 := by
  obtain ⟨hfe, hFe⟩ := example_eq f hf F hF
  subst hfe hFe
  have hve : v = PlanarQuadraticExample.tieHeight := funext fun u => by
    rw [hv u, PlanarQuadraticExample.tieHeight]
  subst hve
  filter_upwards [PlanarQuadraticExample.eventually_crossing_active hu hu'] with e ha
  rintro x z g h rfl rfl rfl rfl
  have hg1 := PlanarQuadraticExample.coordinateGradient_eq 1
    (PlanarQuadraticExample.oldPoint u e)
  have hg0 := PlanarQuadraticExample.coordinateGradient_eq 0
    (PlanarQuadraticExample.newPoint u e)
  change (_ ∧ _ ∧ _ ∧ _) ∧ HasFDerivAt PlanarQuadraticExample.objective
    (gradientFunctional (coordinateGradient (PlanarQuadraticExample.branch 1)
      (PlanarQuadraticExample.oldPoint u e))) (PlanarQuadraticExample.oldPoint u e) ∧
    HasFDerivAt PlanarQuadraticExample.objective
    (gradientFunctional (coordinateGradient (PlanarQuadraticExample.branch 0)
      (PlanarQuadraticExample.newPoint u e))) (PlanarQuadraticExample.newPoint u e) ∧
    -dot (coordinateGradient (PlanarQuadraticExample.branch 1) (PlanarQuadraticExample.oldPoint u e))
      (PlanarQuadraticExample.newPoint u e - PlanarQuadraticExample.oldPoint u e) = _ ∧
    dot (coordinateGradient (PlanarQuadraticExample.branch 0) (PlanarQuadraticExample.newPoint u e) -
      coordinateGradient (PlanarQuadraticExample.branch 1) (PlanarQuadraticExample.oldPoint u e))
      (PlanarQuadraticExample.newPoint u e - PlanarQuadraticExample.oldPoint u e) = _ ∧
    PlanarQuadraticExample.objective (PlanarQuadraticExample.oldPoint u e) -
      PlanarQuadraticExample.objective (PlanarQuadraticExample.newPoint u e) = _
  rw [hg1, hg0]
  have hd := PlanarQuadraticExample.pair_decrease u e
  have ht := PlanarQuadraticExample.pair_curvature u e
  simp only [TransportedCertificate.pairDecrease, TransportedCertificate.pairCurvature,
    TransportedCertificate.pairStep, PlanarQuadraticExample.oldGradient,
    PlanarQuadraticExample.newGradient] at hd ht
  refine ⟨ha, PlanarQuadraticExample.winner_one_hasGradient ha.1 ha.2.1,
    PlanarQuadraticExample.winner_zero_hasGradient ha.2.2.1 ha.2.2.2, hd, ht, ?_⟩
  rw [PlanarQuadraticExample.winner_one_value ha.1.le ha.2.1.le,
    PlanarQuadraticExample.winner_zero_value ha.2.2.1.le ha.2.2.2.le]
  exact PlanarQuadraticExample.crossing_value_difference hu.le e


/-! ### Examples behind three remarks -/

/-- The square of a nonnegative convex function is convex. -/
theorem convexOn_sq_of_nonneg {n : ℕ} {g : Vec n → ℝ} (hg : ConvexOn ℝ univ g)
    (h0 : ∀ x, 0 ≤ g x) : ConvexOn ℝ univ (fun x => g x ^ 2) := by
  refine ⟨convex_univ, fun x _ y _ s t hs ht hst => ?_⟩
  have h1 := hg.2 (mem_univ x) (mem_univ y) hs ht hst
  simp only [smul_eq_mul] at h1 ⊢
  have h3 : g (s • x + t • y) ^ 2 ≤ (s * g x + t * g y) ^ 2 := pow_le_pow_left₀ (h0 _) h1 2
  have h4 : (s * g x + t * g y) ^ 2 ≤ s * g x ^ 2 + t * g y ^ 2 := by
    have ht' : t = 1 - s := by linarith
    subst ht'
    nlinarith [mul_nonneg (mul_nonneg hs ht) (sq_nonneg (g x - g y))]
  linarith

/-- The Euclidean squared norm is convex. -/
theorem sqNorm_convex {n : ℕ} : ConvexOn ℝ univ (fun x : Vec n => sqNorm x) :=
  (sqNorm_affine_convex (1 : Matrix (Fin n) (Fin n) ℝ) 0).congr (fun x _ => by simp)

/-- Item `A/local/prose/026` (`paper/sections/local.tex:175-176`), anchor "A common positive lower
Hessian bound is one sufficient way", first part (sufficiency).

Let $F:\R^2\to\R$ be finite and convex, attain its minimum $F_*$, and let $b\in\R$. Suppose that on
an open convex set $V\supseteq\{F\le b\}$, $F=\max_if_i$ (`IsGreatest`) for finitely many $C^2$
branches with a common positive lower Hessian bound, $\nabla^2f_i(x)-\mu I\succeq0$ for $x\in V$,
$\mu>0$ (`RadialHessian.matrix f x` is the matrix of the second Fréchet derivative; one branch,
$m=1$, is the case of a $C^2$ objective). Then hypothesis 1 of Theorem `art:planar-cluster` holds:
for every $F_*<t\le b$, the boundary of $\{F\le t\}$ contains no nontrivial line segment. -/
theorem hessian_bound_strict_contours (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (Set.range F) Fstar) (b : ℝ) {m : ℕ} (f : Fin m → Vec 2 → ℝ)
    (V : Set (Vec 2)) (hV : IsOpen V) (hVc : Convex ℝ V) (hbV : {x | F x ≤ b} ⊆ V)
    (hfC : ∀ i, ContDiffOn ℝ 2 (f i) V)
    (hmax : ∀ x ∈ V, IsGreatest (Set.range fun i => f i x) (F x)) (μ : ℝ) (hμ : 0 < μ)
    (hhess : ∀ i, ∀ x ∈ V, (RadialHessian.matrix (f i) x - μ • (1 : Mat 2)).PosSemidef) :
    ∀ t, Fstar < t → t ≤ b →
      ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {z | F z ≤ t} → x = y := by
  have hs : StrictConvexOn ℝ V F :=
    PlanarMaxRegular.strictConvexOn_finite_max hVc
      (fun i => PlanarMaxRegular.strictConvexOn_of_hessian_lower_bound hV hVc (hfC i) hμ
        (hhess i)) hmax
  intro t _ htb x y hxy
  exact PlanarMaxRegular.no_segment_frontier_of_local_strictConvex (convex_continuous hF) hs
    (fun p hp => hbV (le_trans hp htb)) x y hxy

/-- Item `A/local/prose/026` (`paper/sections/local.tex:175-176`), anchor "A common positive lower
Hessian bound is one sufficient way", second part: "but is not required".

$F(x)=\|x\|^4$ on $\R^2$ is convex and $C^2$ with minimizer $0$, all its positive contours are
strict (no boundary of $\{F\le t\}$, $t>0$, contains a nontrivial segment), yet its Hessian at the
minimizer is not bounded below by any $\mu I$, $\mu>0$; so it has no common positive lower Hessian
bound on any neighborhood of the minimizer. (The sufficiency part is
`hessian_bound_strict_contours`.) -/
theorem strict_contours_without_hessian_bound :
    ∃ F : Vec 2 → ℝ, ConvexOn ℝ univ F ∧ ContDiff ℝ 2 F ∧ (∀ x, F 0 ≤ F x) ∧
      (∀ t, F 0 < t → ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {z | F z ≤ t} → x = y) ∧
      ∀ μ : ℝ, 0 < μ → ¬ (RadialHessian.matrix F 0 - μ • (1 : Mat 2)).PosSemidef := by
  set F : Vec 2 → ℝ := fun x => sqNorm x ^ 2 with hFdef
  have hF0 : F 0 = 0 := by simp [hFdef, sqNorm]
  have hcont : Continuous F := by
    simp only [hFdef, sqNorm]; fun_prop
  have hC : ContDiff ℝ 2 F := by
    simp only [hFdef, sqNorm]
    apply ContDiff.pow
    apply ContDiff.sum
    intro i _
    exact (contDiff_apply ℝ ℝ i).pow 2
  refine ⟨F, convexOn_sq_of_nonneg sqNorm_convex sqNorm_nonneg, hC,
    fun x => by rw [hF0]; exact sq_nonneg _, fun t ht x y hxy => ?_, fun μ hμ hpsd => ?_⟩
  · have hlev : ∀ w ∈ segment ℝ x y, F w = t := fun w hw =>
      frontier_le_subset_eq hcont continuous_const (hxy hw)
    set m := (1 - (1 / 2 : ℝ)) • x + (1 / 2 : ℝ) • y with hm
    have hmseg : m ∈ segment ℝ x y :=
      ⟨1 - 1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
    have hx := hlev x (left_mem_segment ℝ x y)
    have hy := hlev y (right_mem_segment ℝ x y)
    have hmv := hlev m hmseg
    simp only [hFdef] at hx hy hmv
    have hxm : sqNorm x = sqNorm m := (pow_left_inj₀ (sqNorm_nonneg _) (sqNorm_nonneg _)
      two_ne_zero).mp (hx.trans hmv.symm)
    have hym : sqNorm y = sqNorm m := (pow_left_inj₀ (sqNorm_nonneg _) (sqNorm_nonneg _)
      two_ne_zero).mp (hy.trans hmv.symm)
    have hcomb := FixedNormal.sqNorm_convex_combination x y (1 / 2)
    rw [← hm] at hcomb
    have hz : sqNorm (y - x) = 0 := by
      have := sqNorm_nonneg (y - x)
      nlinarith
    exact (sub_eq_zero.mp ((CertificateGeometry.sqNorm_eq_zero_iff _).mp hz)).symm
  · set e : Vec 2 := ![1, 0] with he
    have hray : (fun s : ℝ => F (RadialHessian.ray 0 e s)) = fun s => s ^ 4 := by
      funext s
      simp [hFdef, RadialHessian.ray, he, sqNorm, Fin.sum_univ_two]
      ring
    have h2 := RadialHessian.ray_second_derivative_matrix (hC.contDiffAt (x := 0)) e
    rw [hray] at h2
    have hd : deriv (fun s : ℝ => s ^ 4) = fun s => 4 * s ^ 3 := by
      funext s; simp
    rw [hd] at h2
    have h0 : deriv (fun s : ℝ => 4 * s ^ 3) 0 = 0 := by simp
    rw [h0] at h2
    have hq := hpsd.2 e
    simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec_assoc, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul, smul_eq_mul] at hq
    have hdot : e ⬝ᵥ (RadialHessian.matrix F 0 *ᵥ e) = 0 := h2.symm
    have hee : e ⬝ᵥ e = 1 := by simp [he, dotProduct, Fin.sum_univ_two]
    rw [hdot, hee] at hq
    linarith

/-- Item `A/local/prose/009` (`paper/sections/local.tex:96-97`), anchor "Different cells may have
different".

The hypotheses of Corollary `art:plq` allow different quadratic Hessians on different cells: for
$F(x)=x^2+\max\{x,0\}^2$ on $\R$ (Hessian $2$ on $\{x\le0\}$ and $4$ on $\{x\ge0\}$), with the two
closed full-dimensional half-lines as cells and $Q_0=1\ne Q_1=2$, all hypotheses of `plq` hold
(convexity, unique minimizer $0$, cover, quadratic formula on each cell); hence its conclusion. -/
theorem plq_different_hessians :
    ∃ (F : Vec 1 → ℝ) (a : Fin 2 → Fin 1 → Vec 1) (b : Fin 2 → Fin 1 → ℝ)
      (P : Fin 2 → Set (Vec 1)) (Q : Fin 2 → Mat 1) (c : Fin 2 → Vec 1) (d : Fin 2 → ℝ),
      ConvexOn ℝ univ F ∧ (∀ x, F 0 ≤ F x) ∧ (∀ x, F x = F 0 → x = 0) ∧
      (∀ i, P i = {x | ∀ j, dot (a i j) x ≤ b i j}) ∧ (∀ i, (interior (P i)).Nonempty) ∧
      (∀ x, ∃ i, x ∈ P i) ∧ (∀ i, ∀ x ∈ P i, F x = dot x (Q i *ᵥ x) + dot (c i) x + d i) ∧
      Q 0 ≠ Q 1 := by
  set sg : Fin 2 → ℝ := ![1, -1] with hsg
  set F : Vec 1 → ℝ := fun x => x 0 ^ 2 + max (x 0) 0 ^ 2 with hFdef
  have hdot : ∀ (u : ℝ) (x : Vec 1), dot (fun _ : Fin 1 => u) x = u * x 0 := by
    intro u x; simp [dot]
  have hl : ConvexOn ℝ univ (fun x : Vec 1 => x 0) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).toLinearMap.convexOn
      convex_univ
  have hmax : ConvexOn ℝ univ (fun x : Vec 1 => max (x 0) 0) :=
    hl.sup (convexOn_const 0 convex_univ)
  refine ⟨F, fun i _ => fun _ => sg i, fun _ _ => 0,
    fun i => {x | ∀ j : Fin 1, dot ((fun i _ => fun _ => sg i : Fin 2 → Fin 1 → Vec 1) i j) x ≤ 0},
    ![!![1], !![2]], fun _ => 0, fun _ => 0, ?_, ?_, ?_, fun _ => rfl, ?_, ?_, ?_, ?_⟩
  · have h1 : ConvexOn ℝ univ (fun x : Vec 1 => x 0 ^ 2) :=
      sqNorm_convex.congr (fun x _ => by simp [sqNorm])
    have h2 : ConvexOn ℝ univ (fun x : Vec 1 => max (x 0) 0 ^ 2) :=
      convexOn_sq_of_nonneg hmax (fun x => le_max_right _ _)
    exact h1.add h2
  · intro x
    simp only [hFdef]
    norm_num
    positivity
  · intro x hx
    simp only [hFdef] at hx
    norm_num at hx
    have h0 : x 0 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (max (x 0) 0)]
    ext i
    fin_cases i
    simpa using h0
  · intro i
    have hopen : IsOpen {x : Vec 1 | sg i * x 0 < 0} :=
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
  · intro x
    rcases le_or_lt (x 0) 0 with h | h
    · refine ⟨0, fun j => ?_⟩
      show dot (fun _ => sg 0) x ≤ 0
      rw [hdot]
      simp [hsg, h]
    · refine ⟨1, fun j => ?_⟩
      show dot (fun _ => sg 1) x ≤ 0
      rw [hdot]
      simp [hsg]
      linarith
  · intro i x hx
    have h : dot (fun _ => sg i) x ≤ 0 := hx 0
    rw [hdot] at h
    fin_cases i
    · have h' : x 0 ≤ 0 := by simpa [hsg] using h
      simp [hFdef, dot, Matrix.mulVec, dotProduct, max_eq_right h']
      ring
    · have h' : 0 ≤ x 0 := by simp [hsg] at h; linarith
      simp [hFdef, dot, Matrix.mulVec, dotProduct, max_eq_left h']
      ring
  · intro h
    have := congrFun (congrFun h 0) 0
    norm_num at this

/-- Item `A/local/prose/018` (`paper/sections/local.tex:143-144`), anchor "This example allows
nonpolyhedral penalties".

The Euclidean residual norms of `euclidean_residuals_local_form` include nonpolyhedral penalties:
already $x\mapsto\|x\|$ on $\R^2$ ($A=I$, $b=0$) is not a finite convex polyhedral penalty, i.e.
not the maximum of finitely many affine functions. (Proof: each unit vector $u$ would be the
gradient of an affine piece active at $u$, and there are infinitely many unit vectors.) -/
theorem euclidean_norm_not_polyhedral :
    ¬ ∃ (k : ℕ) (p : Fin k → Vec 2) (q : Fin k → ℝ), ∀ x : Vec 2,
      IsGreatest (Set.range fun j => dot (p j) x + q j) ‖euclideanVector x‖ := by
  rintro ⟨k, p, q, hpq⟩
  have hnorm : ∀ y : Vec 2, ‖euclideanVector y‖ = Real.sqrt (sqNorm y) := fun y => by
    rw [← euclid_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  -- every unit vector is the gradient of one of the affine pieces
  have hkey : ∀ u : Vec 2, sqNorm u = 1 → ∃ j, p j = u := by
    intro u hu
    obtain ⟨j, hj⟩ := (hpq u).1
    have hj' : dot (p j) u + q j = 1 := by
      have : dot (p j) u + q j = ‖euclideanVector u‖ := hj
      rw [this, hnorm, hu, Real.sqrt_one]
    have hle : ∀ y, dot (p j) y + q j ≤ ‖euclideanVector y‖ := fun y => (hpq y).2 ⟨j, rfl⟩
    have h0 := hle 0
    have h2 := hle ((2 : ℝ) • u)
    rw [dot_smul_right, euclideanVector_smul, norm_smul, hnorm u, hu, Real.sqrt_one] at h2
    have hz0 : ‖euclideanVector (0 : Vec 2)‖ = 0 := by
      rw [show euclideanVector (0 : Vec 2) = 0 from rfl, norm_zero]
    simp only [dot, Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add, hz0] at h0
    norm_num at h2
    have hq0 : q j = 0 := by linarith
    have hpu : dot (p j) u = 1 := by linarith
    have hp := hle (p j)
    rw [hq0, add_zero, dot_self_eq_sqNorm, hnorm] at hp
    have hs : sqNorm (p j) ≤ 1 := by
      have h0' := Real.sqrt_nonneg (sqNorm (p j))
      have hsq := Real.sq_sqrt (sqNorm_nonneg (p j))
      nlinarith
    have hzero : sqNorm (p j - u) = 0 := by
      have h := sqNorm_add_smul (p j) u (-1)
      have he : p j + (-1 : ℝ) • u = p j - u := by module
      rw [he] at h
      have hn := sqNorm_nonneg (p j - u)
      nlinarith
    exact ⟨j, sub_eq_zero.mp ((CertificateGeometry.sqNorm_eq_zero_iff _).mp hzero)⟩
  -- infinitely many unit vectors
  let u : ℕ → Vec 2 := fun m => ![Real.cos (1 / (m + 1)), Real.sin (1 / (m + 1))]
  have hu : ∀ m, sqNorm (u m) = 1 := fun m => by
    simp [u, sqNorm, Fin.sum_univ_two, Real.cos_sq_add_sin_sq]
  choose J hJ using fun m => hkey (u m) (hu m)
  apply not_injective_infinite_finite J
  intro m₁ m₂ h
  have hc : Real.cos (1 / ((m₁ : ℝ) + 1)) = Real.cos (1 / ((m₂ : ℝ) + 1)) := by
    have := congrFun ((hJ m₁).symm.trans ((congrArg p h).trans (hJ m₂))) 0
    simpa [u] using this
  have hmem : ∀ m : ℕ, 1 / ((m : ℝ) + 1) ∈ Icc 0 Real.pi := fun m => by
    refine ⟨by positivity, ?_⟩
    have h1 : 1 / ((m : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    linarith [Real.pi_gt_three]
  have heq := Real.injOn_cos (hmem m₁) (hmem m₂) hc
  have h' : ((m₁ : ℝ) + 1)⁻¹ = ((m₂ : ℝ) + 1)⁻¹ := by simpa [one_div] using heq
  have h'' : (m₁ : ℝ) + 1 = (m₂ : ℝ) + 1 := inv_inj.mp h'
  exact_mod_cast add_right_cancel h''

/-- Proof of Theorem `art:nonradial-example`, undisplayed claim of `paper/sections/local.tex:427`
(not a register item): "As $u,e\to0^+$, $\Delta/d\to1/2$ and $t/d\to1$", with
$d=2e(1+3v+3e)$, $t=2e(1+2v+4e)$, $\Delta=e(1+4v)+e^2$ (display `disp/017`) and $v=v(u)$. -/
theorem example_ratio_limits (v : ℝ → ℝ)
    (hv : ∀ u, v u = (-1 + Real.sqrt (1 + 4 * u + 2 * u ^ 2)) / 2) :
    Tendsto (fun q : ℝ × ℝ => (q.2 * (1 + 4 * v q.1) + q.2 ^ 2) /
        (2 * q.2 * (1 + 3 * v q.1 + 3 * q.2))) (𝓝[>] 0 ×ˢ 𝓝[>] 0) (𝓝 (1 / 2)) ∧
      Tendsto (fun q : ℝ × ℝ => (2 * q.2 * (1 + 2 * v q.1 + 4 * q.2)) /
        (2 * q.2 * (1 + 3 * v q.1 + 3 * q.2))) (𝓝[>] 0 ×ˢ 𝓝[>] 0) (𝓝 1) := by
  have hve : v = PlanarQuadraticExample.tieHeight := funext fun u => by
    rw [hv u, PlanarQuadraticExample.tieHeight]
  subst hve
  have hpair : Tendsto (fun q : ℝ × ℝ => (PlanarQuadraticExample.tieHeight q.1, q.2))
      (𝓝[>] 0 ×ˢ 𝓝[>] 0) (𝓝 (0, 0)) := by
    have hid : Tendsto (fun r : ℝ => r) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    have hfst : Tendsto (fun q : ℝ × ℝ => q.1) (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 0) :=
      hid.comp tendsto_fst
    have h1 : Tendsto (fun q : ℝ × ℝ => PlanarQuadraticExample.tieHeight q.1)
        (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have := (PlanarQuadraticExample.tieHeight_continuous.tendsto 0).comp hfst
      simpa [Function.comp_def, PlanarQuadraticExample.tieHeight_zero] using this
    have h2 : Tendsto (fun q : ℝ × ℝ => q.2) (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 0) :=
      hid.comp tendsto_snd
    exact h1.prodMk_nhds h2
  have hpos : ∀ᶠ q : ℝ × ℝ in 𝓝[>] 0 ×ˢ 𝓝[>] 0, 0 < q.2 :=
    Filter.Eventually.prod_inr (eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)) _
  constructor
  · have hc : ContinuousAt (fun p : ℝ × ℝ => (1 + 4 * p.1 + p.2) / (2 * (1 + 3 * p.1 + 3 * p.2)))
        (0, 0) := by
      apply ContinuousAt.div (by fun_prop) (by fun_prop)
      norm_num
    have h := hc.tendsto.comp hpair
    norm_num at h
    refine h.congr' ?_
    filter_upwards [hpos] with q hq
    simp only [Function.comp]
    rw [show q.2 * (1 + 4 * PlanarQuadraticExample.tieHeight q.1) + q.2 ^ 2 =
      q.2 * (1 + 4 * PlanarQuadraticExample.tieHeight q.1 + q.2) by ring,
      show 2 * q.2 * (1 + 3 * PlanarQuadraticExample.tieHeight q.1 + 3 * q.2) =
      q.2 * (2 * (1 + 3 * PlanarQuadraticExample.tieHeight q.1 + 3 * q.2)) by ring,
      mul_div_mul_left _ _ hq.ne']
  · have hc : ContinuousAt (fun p : ℝ × ℝ => (1 + 2 * p.1 + 4 * p.2) / (1 + 3 * p.1 + 3 * p.2))
        (0, 0) := by
      apply ContinuousAt.div (by fun_prop) (by fun_prop)
      norm_num
    have h := hc.tendsto.comp hpair
    norm_num at h
    refine h.congr' ?_
    filter_upwards [hpos] with q hq
    simp only [Function.comp]
    rw [show 2 * q.2 * (1 + 2 * PlanarQuadraticExample.tieHeight q.1 + 4 * q.2) =
      (2 * q.2) * (1 + 2 * PlanarQuadraticExample.tieHeight q.1 + 4 * q.2) by ring,
      mul_div_mul_left _ _ (by positivity : (2 * q.2) ≠ 0)]

/-! ### Non-vacuity

The standing assumptions of the theorems above can hold. (The assumptions inside the proof by
contradiction of Theorem `art:planar-cluster`, used by `planar_cluster_field`, cannot all hold:
that is what the proof shows; the theorem's own hypotheses are satisfiable, see below.) -/

/-- The gradient of a linear function $x\mapsto c^Tx$ is $c$ at every point. -/
theorem coordinateGradient_dot {n : ℕ} (c y : Vec n) :
    coordinateGradient (fun x => dot c x) y = c := by
  have h : HasFDerivAt (fun x => dot c x) (gradientFunctional c) y := by
    have he : (fun x => dot c x) = ⇑(gradientFunctional c) :=
      funext fun x => (gradientFunctional_apply c x).symm
    rw [he]
    exact (gradientFunctional c).hasFDerivAt
  exact AffineProjection.gradientFunctional_injective
    ((hasFDerivAt_coordinateGradient h.differentiableAt).unique h)

/-- The library's planar regularity alternative implies the form stated in Theorem
`art:planar-cluster` (converse of `regular_of_paper`). -/
theorem paper_of_regular {F : Vec 2 → ℝ} {p : Vec 2}
    (h : ContDiffAt ℝ 2 F p ∨ PlanarCornerCharts.ConvexTwoBranchRegularAt F p) :
    (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]) := by
  rcases h with hC | ⟨f, U, hU, hpU, hf, hrep, hact, hdet⟩
  · left
    refine ⟨interior {y | ContDiffAt ℝ 2 F y}, isOpen_interior,
      mem_interior_iff_mem_nhds.mpr (hC.eventually (by norm_num)), fun y hy => ?_⟩
    have hy' : ContDiffAt ℝ 2 F y := interior_subset hy
    exact hy'.contDiffWithinAt
  · right
    refine ⟨U, hU, hpU, f 0, f 1, (hf 0).1, (hf 1).1, (hf 0).2, (hf 1).2, fun z hz => ?_,
      hact 0, hact 1, ?_⟩
    · refine (hrep z hz).unique ⟨?_, ?_⟩
      · rcases max_choice (f 0 z) (f 1 z) with h | h
        · exact ⟨0, h.symm⟩
        · exact ⟨1, h.symm⟩
      · rintro _ ⟨i, rfl⟩
        fin_cases i
        · exact le_max_left _ _
        · exact le_max_right _ _
    · rw [LinearIndependent.pair_iff]
      intro s t hst
      have h0 := congrFun hst 0
      have h1 := congrFun hst 1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0 h1
      simp only [HomogeneousPlanar.pairDet] at hdet
      set a := coordinateGradient (f 0) p
      set b := coordinateGradient (f 1) p
      have hs : s * (a 0 * b 1 - a 1 * b 0) = 0 := by linear_combination b 1 * h0 - b 0 * h1
      have ht : t * (a 0 * b 1 - a 1 * b 0) = 0 := by linear_combination a 0 * h1 - a 1 * h0
      exact ⟨(mul_eq_zero.mp hs).resolve_right hdet, (mul_eq_zero.mp ht).resolve_right hdet⟩

/-- The assumptions of Lemma `art:localization` and of its displays `disp/001`-`disp/002` hold
for $F=\|x\|^2$ on $\R$, $x_*=0$, $U=\R$, $r=1$. -/
example : ∃ (F : Vec 1 → ℝ) (xstar : Vec 1) (U : Set (Vec 1)) (r δ : ℝ),
    1 ≤ 1 ∧ ConvexOn ℝ univ F ∧ (∀ x, F xstar ≤ F x) ∧ (∀ x, F x = F xstar → x = xstar) ∧
      U ∈ 𝓝 xstar ∧ 0 < r ∧ {x | ‖euclideanVector (x - xstar)‖ ≤ r} ⊆ U ∧
      δ = sInf ((fun u => F (xstar + u) - F xstar) '' {u | ‖euclideanVector u‖ = r}) := by
  refine ⟨fun x => sqNorm x, 0, univ, 1, _, le_rfl, sqNorm_convex, fun x => ?_, fun x hx => ?_,
    univ_mem, one_pos, subset_univ _, rfl⟩
  · simpa [sqNorm] using sqNorm_nonneg x
  · have h0 : sqNorm (0 : Vec 1) = 0 := by simp [sqNorm]
    have hx' : sqNorm x = sqNorm 0 := hx
    rw [h0] at hx'
    exact (CertificateGeometry.sqNorm_eq_zero_iff x).mp hx'

/-- The assumptions of displays `disp/003`-`disp/004` (the hypotheses of Theorem
`art:polyhedral` together with the proof's ball, discarded cells and Lipschitz bound) hold for
$F(x)=|x|$ on $\R$ with the cells $\{x\le0\}$, $\{x\ge0\}$, the linear extensions $-x$, $x$,
$U=V_i=\R$, $r=1$ and $L=0$. -/
example : ∃ (F : Vec 1 → ℝ) (xstar : Vec 1) (U : Set (Vec 1)) (a : Fin 2 → Fin 1 → Vec 1)
    (b : Fin 2 → Fin 1 → ℝ) (P V : Fin 2 → Set (Vec 1)) (f : Fin 2 → Vec 1 → ℝ) (r : ℝ)
    (B : Set (Vec 1)) (L : ℝ),
    1 ≤ 1 ∧ ConvexOn ℝ univ F ∧ (∀ x, F xstar ≤ F x) ∧ (∀ x, F x = F xstar → x = xstar) ∧
      IsOpen U ∧ xstar ∈ U ∧ (∀ i, P i = {x | ∀ j, dot (a i j) x ≤ b i j}) ∧
      (∀ i, (interior (P i)).Nonempty) ∧ U ⊆ ⋃ i, P i ∧ (∀ i, IsOpen (V i)) ∧
      (∀ i, U ∩ P i ⊆ V i) ∧ (∀ i, CenteredSmoothSublinear.LocallyC11On (V i) (f i)) ∧
      (∀ i, ∀ x ∈ U ∩ P i, F x = f i x) ∧ 0 < r ∧
      B = {x | ‖euclideanVector (x - xstar)‖ < r} ∧ B ⊆ U ∧ (∀ i, xstar ∈ P i → B ⊆ V i) ∧
      (∀ i, (B ∩ P i).Nonempty → xstar ∈ P i) ∧ 0 ≤ L ∧
      (∀ i, xstar ∈ P i → ∀ y ∈ B, ∀ y' ∈ B,
        ‖euclideanVector (coordinateGradient (f i) y - coordinateGradient (f i) y')‖ ≤
          L * ‖euclideanVector (y - y')‖) := by
  set sg : Fin 2 → ℝ := ![1, -1] with hsg
  have hdot : ∀ (u : ℝ) (x : Vec 1), dot (fun _ : Fin 1 => u) x = u * x 0 := by
    intro u x; simp [dot]
  have hl : ConvexOn ℝ univ (fun x : Vec 1 => x 0) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).toLinearMap.convexOn
      convex_univ
  have hn : ConvexOn ℝ univ (fun x : Vec 1 => -x 0) :=
    (-(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)).toLinearMap.convexOn
      convex_univ
  have h0P : ∀ i, (0 : Vec 1) ∈ {x : Vec 1 | ∀ j : Fin 1,
      dot ((fun i _ => fun _ => sg i : Fin 2 → Fin 1 → Vec 1) i j) x ≤ 0} := by
    intro i j
    simp [dot]
  refine ⟨fun x => |x 0|, 0, univ, fun i _ => fun _ => sg i, fun _ _ => 0,
    fun i => {x | ∀ j : Fin 1, dot ((fun i _ => fun _ => sg i : Fin 2 → Fin 1 → Vec 1) i j) x ≤ 0},
    fun _ => univ, fun i x => dot (fun _ => -sg i) x, 1, {x | ‖euclideanVector (x - 0)‖ < 1}, 0,
    le_rfl, (hl.sup hn).congr (fun x _ => by simp [abs_eq_max_neg]), fun x => by simp,
    fun x hx => ?_, isOpen_univ, mem_univ _, fun _ => rfl, fun i => ?_, fun x _ => ?_,
    fun _ => isOpen_univ, fun _ _ _ => mem_univ _, fun i => ?_, fun i x hx => ?_, one_pos, rfl,
    subset_univ _, fun _ _ _ _ => mem_univ _, fun i _ => h0P i, le_rfl, ?_⟩
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
  · apply ConvexCellRadial.contDiffOn_two_locallyC11 isOpen_univ
    show ContDiffOn ℝ 2 (fun x => dot (fun _ : Fin 1 => -sg i) x) univ
    have he : (fun x => dot (fun _ : Fin 1 => -sg i) x) =
        ⇑(gradientFunctional (fun _ : Fin 1 => -sg i)) :=
      funext fun x => (gradientFunctional_apply _ x).symm
    rw [he]
    exact (gradientFunctional (fun _ : Fin 1 => -sg i)).contDiff.contDiffOn
  · have h : dot (fun _ => sg i) x ≤ 0 := hx.2 0
    rw [hdot] at h
    show |x 0| = dot (fun _ => -sg i) x
    rw [hdot]
    fin_cases i
    · have h' : x 0 ≤ 0 := by simpa [hsg] using h
      simp [hsg, abs_of_nonpos h']
    · have h' : 0 ≤ x 0 := by simp [hsg] at h; linarith
      simp [hsg, abs_of_nonneg h']
  · intro i _ y _ y' _
    rw [coordinateGradient_dot, coordinateGradient_dot, sub_self,
      show euclideanVector (0 : Vec 1) = 0 from rfl, norm_zero, zero_mul]

/-- The assumptions of the lasso statements (`lasso_neighborhood` to `lasso_local_basin`) hold
for $A=1$, $b=0$, $\lambda=1$ on $\R$ ($F(x)=\frac12x^2+|x|$, $x_*=0$, $I_0=\{0\}$, $N=\R$). -/
example : ∃ (A : Matrix (Fin 1) (Fin 1) ℝ) (b : Vec 1) (lam : ℝ) (F : Vec 1 → ℝ) (xstar : Vec 1)
    (I0 : Finset (Fin 1)) (σ : Fin 1 → ℝ) (N : Set (Vec 1)),
    0 < lam ∧ (∀ x, F x = 1 / 2 * sqNorm (A *ᵥ x - b) + lam * ∑ i, |x i|) ∧
      (∀ x, F xstar ≤ F x) ∧ (∀ x, F x = F xstar → x = xstar) ∧
      I0 = Finset.univ.filter (fun i => xstar i = 0) ∧ (∀ i ∉ I0, σ i = Real.sign (xstar i)) ∧
      N = {x | ∀ i ∉ I0, 0 < σ i * x i} := by
  refine ⟨1, 0, 1, fun x => 1 / 2 * sqNorm ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ x - 0) +
    1 * ∑ i, |x i|, 0, Finset.univ, 0, _, one_pos, fun x => rfl, fun x => ?_, fun x hx => ?_,
    by ext i; simp, fun i hi => absurd (Finset.mem_univ i) hi, rfl⟩
  · simp only [Matrix.one_mulVec, sub_zero, one_mul]
    have : sqNorm (0 : Vec 1) = 0 := by simp [sqNorm]
    rw [this]
    simp only [Pi.zero_apply, abs_zero, Finset.sum_const_zero, mul_zero, add_zero]
    have := sqNorm_nonneg x
    positivity
  · simp only [Matrix.one_mulVec, sub_zero, one_mul] at hx
    have h0 : sqNorm (0 : Vec 1) = 0 := by simp [sqNorm]
    rw [h0] at hx
    simp only [Pi.zero_apply, abs_zero, Finset.sum_const_zero, mul_zero, add_zero] at hx
    have h1 := sqNorm_nonneg x
    have h2 : 0 ≤ ∑ i, |x i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    have h3 : sqNorm x = 0 := by linarith
    exact (CertificateGeometry.sqNorm_eq_zero_iff x).mp h3

/-- The assumptions of `euclidean_residuals_local_form` and `euclidean_residuals_basin` hold for
the loss $0$ and one residual $\|x\|$ on $\R$ ($x_*=0$). -/
example : ∃ (loss : Vec 1 → ℝ) (A : Unit → Matrix (Fin 1) (Fin 1) ℝ) (b : Unit → Vec 1)
    (F : Vec 1 → ℝ) (xstar : Vec 1),
    ConvexOn ℝ univ loss ∧ CenteredSmoothSublinear.LocallyC11On univ loss ∧
      (∀ x, F x = loss x + ∑ j, ‖euclideanVector (A j *ᵥ x - b j)‖) ∧
      (∀ x, F xstar ≤ F x) ∧ (∀ x, F x = F xstar → x = xstar) := by
  refine ⟨fun _ => 0, fun _ => 1, fun _ => 0, fun x => ‖euclideanVector x‖, 0,
    convexOn_const 0 convex_univ, ConvexCellRadial.contDiffOn_two_locallyC11 isOpen_univ
      contDiffOn_const, fun x => by simp, fun x => ?_, fun x hx => ?_⟩
  · show ‖euclideanVector (0 : Vec 1)‖ ≤ ‖euclideanVector x‖
    rw [show euclideanVector (0 : Vec 1) = 0 from rfl, norm_zero]
    exact norm_nonneg _
  · change ‖euclideanVector x‖ = ‖euclideanVector (0 : Vec 1)‖ at hx
    rw [show euclideanVector (0 : Vec 1) = 0 from rfl, norm_zero] at hx
    have h := euclid_norm_sq x
    rw [hx] at h
    exact (CertificateGeometry.sqNorm_eq_zero_iff x).mp (by rw [← h]; norm_num)

open AffineCriticalObjective in
/-- The hypotheses of Theorem `art:planar-cluster` and Corollary `art:planar-convergence` hold for
the objective of Theorem `art:nonradial-example`, with $F_*=0$ and $b=1/100$. -/
example : ∃ (F : Vec 2 → ℝ) (Fstar b : ℝ),
    ConvexOn ℝ univ F ∧ IsLeast (Set.range F) Fstar ∧ Fstar < b ∧ IsCompact {x | F x ≤ b} ∧
      (∀ t, Fstar < t → t ≤ b →
        ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {z | F z ≤ t} → x = y) ∧
      (∀ p, F p ≤ b → ¬ IsAffineCritical F p →
        (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
        (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
          ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
          (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
          LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p])) ∧
      {p | IsAffineCritical F p} ∩ {x | F x ≤ b} ⊆ argmin F := by
  refine ⟨PlanarQuadraticExample.objective, 0, 1 / 100,
    PlanarQuadraticExample.objective_convex, ⟨⟨0, PlanarQuadraticExample.objective_zero⟩,
      by rintro _ ⟨x, rfl⟩; exact PlanarQuadraticExample.objective_nonneg x⟩, by norm_num,
    PlanarQuadraticExample.sublevel_compact _, fun t _ _ => PlanarQuadraticExample.strict_contours t,
    fun p hp hn => paper_of_regular (PlanarQuadraticExample.regular_on_box
      (PlanarQuadraticExample.small_sublevel_mem_box hp) hn), ?_⟩
  rintro p ⟨hc, hp⟩
  exact ConvexSubdifferential.zero_mem_iff_global_minimum.mp
    (PlanarQuadraticExample.affineCorrect_on_box
      (PlanarQuadraticExample.small_sublevel_mem_box hp) hc)

/-- $x\mapsto x_1^2+cx_2$ is convex on $\R^2$. -/
theorem sq_add_lin_convex (c : ℝ) : ConvexOn ℝ univ (fun x : Vec 2 => x 0 ^ 2 + c * x 1) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hb' : b = 1 - a := by linarith
  subst hb'
  nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x 0 - y 0))]

/-- The gradient of $x\mapsto x_1^2+cx_2$ at $p$ is $(2p_1,c)$. -/
theorem coordinateGradient_sq_add_lin (c : ℝ) (p : Vec 2) :
    coordinateGradient (fun x : Vec 2 => x 0 ^ 2 + c * x 1) p = ![2 * p 0, c] := by
  have h0 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).hasFDerivAt (x := p)
  have h1 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).hasFDerivAt (x := p)
  have hsq := ((hasDerivAt_id (p 0)).pow 2).comp_hasFDerivAt p h0
  have h : HasFDerivAt (fun x : Vec 2 => x 0 ^ 2 + c * x 1) (gradientFunctional ![2 * p 0, c]) p := by
    convert hsq.add (h1.const_mul c) using 1
    ext v
    simp [gradientFunctional_apply, dot, Fin.sum_univ_two]
  exact AffineProjection.gradientFunctional_injective
    ((hasFDerivAt_coordinateGradient h.differentiableAt).unique h)

open ConvexSubdifferential in
/-- For $F(u,v)=u^2+|v|$, every subgradient at $p$ has first coordinate $2p_1$. -/
theorem unexcited_subgradient_first (p g : Vec 2)
    (hg : g ∈ subdifferential UnexcitedMetric.objective p) : g 0 = 2 * p 0 := by
  have h := hg (p + ![(g 0 - 2 * p 0) / 2, 0])
  simp only [add_sub_cancel_left, UnexcitedMetric.objective, Pi.add_apply, dot,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, add_zero,
    mul_zero] at h
  have hsq : (g 0 - 2 * p 0) ^ 2 ≤ 0 := by nlinarith
  have h2 : (g 0 - 2 * p 0) ^ 2 = 0 := le_antisymm hsq (sq_nonneg _)
  have h3 := (pow_eq_zero_iff two_ne_zero).mp h2
  linarith

open ConvexSubdifferential AffineCriticalObjective in
/-- For $F(u,v)=u^2+|v|$ the only affine-critical point is the minimizer $0$: off the axis $v=0$
the objective is differentiable, and at $(u,0)$ with $u\ne0$ the direction $(-1/(2u),0)$ is an
equal-rate descent direction. -/
theorem unexcited_affineCritical_eq_zero (p : Vec 2)
    (hc : IsAffineCritical UnexcitedMetric.objective p) : p = 0 := by
  by_cases h0 : p 0 = 0
  · by_cases h1 : p 1 = 0
    · ext i; fin_cases i
      · exact h0
      · exact h1
    · -- a differentiable point: affine criticality forces optimality
      set σ : ℝ := if 0 < p 1 then 1 else -1 with hσdef
      have hσ : σ ^ 2 = 1 := by by_cases h : 0 < p 1 <;> simp [hσdef, h]
      have hr : 0 < |p 1| := abs_pos.mpr h1
      have hp : p = UnexcitedMetric.point σ |p 1| := by
        ext i; fin_cases i
        · simp [UnexcitedMetric.point, h0]
        · by_cases h : 0 < p 1
          · simp [UnexcitedMetric.point, hσdef, h, abs_of_pos h]
          · have hneg : p 1 < 0 := lt_of_le_of_ne (not_lt.mp h) h1
            simp [UnexcitedMetric.point, hσdef, h, abs_of_neg hneg]
      have hd := UnexcitedMetric.actual_gradient hσ hr
      rw [← hp] at hd
      have hmin := zero_mem_iff_global_minimum.mp
        (affineCorrectAt_of_hasFDerivAt UnexcitedMetric.objective_convex hd hc)
      have hle := hmin 0
      have h00 : UnexcitedMetric.objective 0 = 0 := by simp [UnexcitedMetric.objective]
      have heq : UnexcitedMetric.objective p = UnexcitedMetric.objective 0 :=
        le_antisymm (by rw [h00]; exact h00 ▸ hle) (by rw [h00]; exact UnexcitedMetric.objective_nonneg p)
      exact UnexcitedMetric.unique_minimum heq
  · exfalso
    apply (equal_rate_exists_iff_not_affineCritical UnexcitedMetric.objective_convex p).mp _ hc
    refine ⟨![-1 / (2 * p 0), 0], fun g hg => ?_⟩
    have hg0 := unexcited_subgradient_first p g hg
    simp only [dot, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      mul_zero, add_zero, hg0]
    field_simp

/-- For $F(u,v)=u^2+|v|$, no boundary of a sublevel set contains a nontrivial segment. -/
theorem unexcited_strict_contours (t : ℝ) (x y : Vec 2)
    (hxy : segment ℝ x y ⊆ frontier {z | UnexcitedMetric.objective z ≤ t}) : x = y := by
  have hcont : Continuous UnexcitedMetric.objective :=
    convex_continuous UnexcitedMetric.objective_convex
  have hlev : ∀ w ∈ segment ℝ x y, UnexcitedMetric.objective w = t := fun w hw =>
    frontier_le_subset_eq hcont continuous_const (hxy hw)
  have hm : ((1 : ℝ) / 2) • x + ((1 : ℝ) / 2) • y ∈ segment ℝ x y :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
  have hx := hlev x (left_mem_segment ℝ x y)
  have hy := hlev y (right_mem_segment ℝ x y)
  have hmv := hlev _ hm
  simp only [UnexcitedMetric.objective, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx hy hmv
  have habs : |1 / 2 * x 1 + 1 / 2 * y 1| ≤ 1 / 2 * |x 1| + 1 / 2 * |y 1| := by
    calc |1 / 2 * x 1 + 1 / 2 * y 1| ≤ |1 / 2 * x 1| + |1 / 2 * y 1| := abs_add_le _ _
      _ = 1 / 2 * |x 1| + 1 / 2 * |y 1| := by
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have hsq : (x 0 - y 0) ^ 2 ≤ 0 := by nlinarith
  have hx0 : x 0 = y 0 := by
    have h2 : (x 0 - y 0) ^ 2 = 0 := le_antisymm hsq (sq_nonneg _)
    have := (pow_eq_zero_iff two_ne_zero).mp h2
    linarith
  have hx1 : x 1 = y 1 := by
    rw [hx0] at hmv hx
    have e1 : |x 1| = |y 1| := by linarith
    have e2 : |1 / 2 * x 1 + 1 / 2 * y 1| = |y 1| := by linarith
    rcases abs_eq_abs.mp e1 with h | h
    · exact h
    · rw [h, show 1 / 2 * -y 1 + 1 / 2 * y 1 = (0 : ℝ) by ring, abs_zero] at e2
      have hy1 : y 1 = 0 := abs_eq_zero.mp e2.symm
      rw [h, hy1, neg_zero]
  ext i; fin_cases i
  · exact hx0
  · exact hx1

open AffineCriticalObjective in
/-- The hypotheses of Theorem `art:planar-cluster`, of Corollary `art:planar-convergence` and of
their proof displays `disp/007` and `disp/009` hold together with an actual admissible run that
starts in $K$: $F(u,v)=u^2+|v|$ (`UnexcitedMetric.objective`), $F_*=0$, $b=1$, and the library's run
`UnexcitedMetric.run` with $A=1$, $v_0=1/2$, $\rho=1/2$, $c_1=1/4$, $c_2=1/2$ (iterates
$(0,(-1/2)^kv_0)$). The contours are pairs of parabolic arcs; off $\mathcal C_{\rm aff}=\{0\}$ the
regular structure comes from the branches $u^2\pm v$, with gradients $(2u,\pm1)$. For
`planar_cluster_energy` at $k=0$ the data $w=0$, $\lambda=1$, $\beta=m=C=L=0$ work; for
`planar_cluster_segment_values` any $k$ and $\theta\in[0,1]$. -/
example : ∃ (F : Vec 2 → ℝ) (Fstar b : ℝ) (R : AdmissibleBFGSRun 2 F),
    ConvexOn ℝ univ F ∧ IsLeast (Set.range F) Fstar ∧ Fstar < b ∧ IsCompact {x | F x ≤ b} ∧
      (∀ t, Fstar < t → t ≤ b →
        ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {z | F z ≤ t} → x = y) ∧
      (∀ p, F p ≤ b → ¬ IsAffineCritical F p →
        (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
        (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
          ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
          (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
          LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p])) ∧
      {p | IsAffineCritical F p} ∩ {x | F x ≤ b} ⊆ argmin F ∧
      R.x 0 ∈ {x | F x ≤ b} ∧
      ∃ (w : Vec 2 → Vec 2) (E : ℕ → ℝ) (m C L lam β : ℝ),
        (∀ k, E k = dot (w (R.x k)) ((R.H k)⁻¹ *ᵥ w (R.x k))) ∧ 0 < lam ∧
        w (R.x (0 + 1)) = lam • w (R.x 0) + β • (R.x (0 + 1) - R.x 0) ∧
        m ≤ (dot (R.g 0) (w (R.x 0))) ^ 2 ∧
        (dot (R.g (0 + 1) - R.g 0) (w (R.x (0 + 1)))) ^ 2 /
          dot (R.g (0 + 1) - R.g 0) (R.x (0 + 1) - R.x 0) ≤ C ∧
        lam ^ 2 ≤ 1 + L * R.d 0 := by
  set F := UnexcitedMetric.objective with hFdef
  have h00 : F 0 = 0 := by simp [hFdef, UnexcitedMetric.objective]
  have hmin : ∀ x, F 0 ≤ F x := fun x => by rw [h00]; exact UnexcitedMetric.objective_nonneg x
  have huniq : ∀ x, F x = F 0 → x = 0 := fun x hx => UnexcitedMetric.unique_minimum hx
  let fb : Fin 2 → Vec 2 → ℝ := ![fun x => x 0 ^ 2 + 1 * x 1, fun x => x 0 ^ 2 + -1 * x 1]
  have hfb : ∀ i, ConvexOn ℝ univ (fb i) ∧ ContDiffOn ℝ 2 (fb i) univ := by
    intro i
    fin_cases i
    · exact ⟨sq_add_lin_convex 1, (((contDiff_apply ℝ ℝ (0 : Fin 2)).pow 2).add
        (contDiff_const.mul (contDiff_apply ℝ ℝ (1 : Fin 2)))).contDiffOn⟩
    · exact ⟨sq_add_lin_convex (-1), (((contDiff_apply ℝ ℝ (0 : Fin 2)).pow 2).add
        (contDiff_const.mul (contDiff_apply ℝ ℝ (1 : Fin 2)))).contDiffOn⟩
  have hgr : ∀ p : Vec 2, (fun i => coordinateGradient (fb i) p) = ![![2 * p 0, 1], ![2 * p 0, -1]] := by
    intro p
    funext i
    fin_cases i
    · exact coordinateGradient_sq_add_lin 1 p
    · exact coordinateGradient_sq_add_lin (-1) p
  have hrep : ∀ z : Vec 2, IsGreatest (Set.range fun i => fb i z) (F z) := by
    intro z
    refine ⟨?_, ?_⟩
    · rcases le_total 0 (z 1) with h | h
      · exact ⟨0, by simp [fb, hFdef, UnexcitedMetric.objective, abs_of_nonneg h]⟩
      · exact ⟨1, by simp [fb, hFdef, UnexcitedMetric.objective, abs_of_nonpos h]⟩
    · rintro _ ⟨i, rfl⟩
      fin_cases i
      · simp [fb, hFdef, UnexcitedMetric.objective, le_abs_self]
      · simp [fb, hFdef, UnexcitedMetric.objective, neg_le_abs]
  have hρ : (1 / 2 : ℝ) < (1 - 1 / 4) / (1 + 1 / 4) := by norm_num
  refine ⟨F, 0, 1, UnexcitedMetric.run 1 (1 / 2) (1 / 2) (1 / 4) (1 / 2) one_pos (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hρ,
    UnexcitedMetric.objective_convex, ⟨⟨0, h00⟩, by rintro _ ⟨x, rfl⟩; exact h00 ▸ hmin x⟩,
    one_pos, Localization.sublevel_compact UnexcitedMetric.objective_convex 0 hmin huniq 1,
    fun t _ _ x y hxy => unexcited_strict_contours t x y hxy, fun p _ hn => ?_, ?_, ?_,
    fun _ => 0, fun _ => 0, 0, 0, 0, 1, 0, fun k => by simp [dot], one_pos, by simp,
    by simp [dot], by simp [dot], by norm_num⟩
  · apply paper_of_regular
    apply PlanarMaxRegular.regular_of_finite_max_independent UnexcitedMetric.objective_convex
      isOpen_univ (mem_univ p) hfb (Eventually.of_forall hrep) _ hn
    rw [hgr p]
    apply affineIndependent_of_ne
    intro h
    have := congrFun h 1
    norm_num at this
  · rintro p ⟨hc, _⟩
    rw [unexcited_affineCritical_eq_zero p hc]
    exact hmin
  · show F (UnexcitedMetric.point (UnexcitedMetric.sign 0) (UnexcitedMetric.radius (1 / 2) (1 / 2) 0)) ≤ 1
    rw [hFdef, UnexcitedMetric.point_value (UnexcitedMetric.sign_sq 0)
      (UnexcitedMetric.radius_pos (by norm_num) (by norm_num) 0).le]
    norm_num [UnexcitedMetric.radius]

/-- The hypotheses of Corollary `art:planar-max` (and of its Hessian sufficiency statement, with
$\mu=1$) hold for the objective of Theorem `art:nonradial-example` with its three branches,
$U=\R^2$, $I_*=\{0,1,2\}$ and weights $1/3$. -/
example : ∃ (F : Vec 2 → ℝ) (xstar : Vec 2) (f : Fin 3 → Vec 2 → ℝ) (U : Set (Vec 2))
    (I : Finset (Fin 3)) (lam : I → ℝ),
    ConvexOn ℝ univ F ∧ (∀ x, F xstar ≤ F x) ∧ (∀ x, F x = F xstar → x = xstar) ∧
      IsOpen U ∧ xstar ∈ U ∧ (∀ i, ConvexOn ℝ U (f i) ∧ ContDiffOn ℝ 2 (f i) U) ∧
      (∀ x ∈ U, IsGreatest (Set.range fun i => f i x) (F x)) ∧
      (∃ b, F xstar < b ∧ ∀ t, F xstar < t → t ≤ b →
        ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {z | F z ≤ t} → x = y) ∧
      I = Finset.univ.filter (fun i => f i xstar = F xstar) ∧
      (AffineIndependent ℝ fun i : I => coordinateGradient (f i) xstar) ∧
      (∀ i, 0 < lam i) ∧ ∑ i, lam i = 1 ∧ ∑ i, lam i • coordinateGradient (f i) xstar = 0 ∧
      ∀ i ∈ I, ∀ x ∈ U, (RadialHessian.matrix (f i) x - (1 : ℝ) • (1 : Mat 2)).PosSemidef := by
  have hI : (Finset.univ.filter fun i : Fin 3 => PlanarQuadraticExample.branch i 0 =
      PlanarQuadraticExample.objective 0) = Finset.univ := by
    ext i; simp [PlanarQuadraticExample.initial_active i]
  have hD : PlanarQuadraticExample.denominator 0 ≠ 0 := by
    norm_num [PlanarQuadraticExample.denominator]
  have hg : ∀ i, coordinateGradient (PlanarQuadraticExample.branch i) 0 =
      PlanarQuadraticExample.gradient i 0 := fun i => PlanarQuadraticExample.coordinateGradient_eq i 0
  refine ⟨PlanarQuadraticExample.objective, 0, PlanarQuadraticExample.branch, univ,
    Finset.univ.filter fun i => PlanarQuadraticExample.branch i 0 =
      PlanarQuadraticExample.objective 0, fun _ => 1 / 3,
    PlanarQuadraticExample.objective_convex, PlanarQuadraticExample.objective_minimum,
    fun x hx => PlanarQuadraticExample.objective_unique_zero x
      (by rwa [PlanarQuadraticExample.objective_zero] at hx),
    isOpen_univ, mem_univ _, fun i => ⟨(PlanarQuadraticExample.branch_convex i),
      (PlanarQuadraticExample.branch_contDiff i).contDiffOn⟩,
    fun x _ => PlanarQuadraticExample.objective_isGreatest x,
    ⟨1, by rw [PlanarQuadraticExample.objective_zero]; norm_num,
      fun t _ _ => PlanarQuadraticExample.strict_contours t⟩, rfl, ?_, fun _ => by norm_num, ?_,
    ?_, fun i _ x _ => by simpa using (PlanarQuadraticExample.branch_actual_hessian_bounds i x).1⟩
  · have h := (PlanarQuadraticExample.gradient_affineIndependent hD).comp_embedding
      (Function.Embedding.subtype fun i : Fin 3 => i ∈ Finset.univ.filter fun i =>
        PlanarQuadraticExample.branch i 0 = PlanarQuadraticExample.objective 0)
    convert h using 1
    funext i
    simp [hg]
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, hI]
    norm_num
  · rw [Finset.sum_coe_sort (Finset.univ.filter fun i : Fin 3 =>
      PlanarQuadraticExample.branch i 0 = PlanarQuadraticExample.objective 0)
      (fun i => (1 / 3 : ℝ) • coordinateGradient (PlanarQuadraticExample.branch i) 0), hI,
      ← Finset.smul_sum]
    simp only [hg]
    obtain ⟨g0, g1, g2⟩ := PlanarQuadraticExample.initial_gradients
    rw [Fin.sum_univ_three, g0, g1, g2]
    ext j
    fin_cases j <;> norm_num


/-- The assumptions of Corollary `art:local-centered` hold for $F(x)=|x|$ on $\R$ with
$U=\R$, $\psi=0$, $\gamma=|\cdot|$, $x_*=0$; and those of `loss_plus_polyhedral_penalty` for
the loss $x^2$ and the penalty $|x|=\max\{x,-x\}$. -/
example : (∃ (F ψ γ : Vec 1 → ℝ) (xstar : Vec 1) (U : Set (Vec 1)),
      ConvexOn ℝ univ F ∧ (∀ x, F xstar ≤ F x) ∧ (∀ x, F x = F xstar → x = xstar) ∧
      IsOpen U ∧ Convex ℝ U ∧ xstar ∈ U ∧ ConvexOn ℝ U ψ ∧
      CenteredSmoothSublinear.LocallyC11On U ψ ∧ ConvexOn ℝ univ γ ∧
      Homogeneous.PositiveDegreeOne γ ∧ ∀ x ∈ U, F x = ψ x + γ (x - xstar)) ∧
    (∃ (loss φ F : Vec 1 → ℝ) (p : Fin 2 → Vec 1) (q : Fin 2 → ℝ) (xstar : Vec 1),
      ConvexOn ℝ univ loss ∧ CenteredSmoothSublinear.LocallyC11On univ loss ∧
      (∀ x, IsGreatest (Set.range fun j => dot (p j) x + q j) (φ x)) ∧
      (∀ x, F x = loss x + φ x) ∧ (∀ x, F xstar ≤ F x) ∧ (∀ x, F x = F xstar → x = xstar)) := by
  have hγc : ConvexOn ℝ univ (fun r : Vec 1 => 1 * ∑ i ∈ Finset.univ, |r i|) :=
    weighted_abs_sum_convex 1 zero_le_one Finset.univ
  have hval : ∀ x : Vec 1, (1 : ℝ) * ∑ i ∈ Finset.univ, |x i| = |x 0| := fun x => by simp
  have h0 : ∀ x : Vec 1, |x 0| = 0 → x = 0 := fun x hx => by
    ext i; fin_cases i; simpa using hx
  refine ⟨⟨fun x => |x 0|, fun _ => 0, fun r => |r 0|, 0, univ,
    hγc.congr (fun x _ => hval x), fun x => by simp, fun x hx => h0 x (by simpa using hx),
    isOpen_univ, convex_univ, mem_univ _, convexOn_const 0 convex_univ,
    ConvexCellRadial.contDiffOn_two_locallyC11 isOpen_univ contDiffOn_const,
    hγc.congr (fun x _ => hval x), fun t ht r => by
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg ht],
    fun x _ => by simp⟩, ⟨fun x => sqNorm x, fun x => |x 0|, fun x => sqNorm x + |x 0|,
    ![![1], ![-1]], fun _ => 0, 0, sqNorm_convex, ?_, fun x => ?_, fun x => rfl,
    fun x => ?_, fun x hx => ?_⟩⟩
  · apply ConvexCellRadial.contDiffOn_two_locallyC11 isOpen_univ
    simp only [sqNorm]
    exact (ContDiff.sum fun i _ => (contDiff_apply ℝ ℝ i).pow 2).contDiffOn
  · refine ⟨?_, ?_⟩
    · rcases le_total 0 (x 0) with h | h
      · exact ⟨0, by simp [dot, abs_of_nonneg h]⟩
      · exact ⟨1, by simp [dot, abs_of_nonpos h]⟩
    · rintro _ ⟨j, rfl⟩
      fin_cases j
      · simp [dot, le_abs_self]
      · simp [dot, neg_le_abs]
  · have := sqNorm_nonneg x
    simp [sqNorm]
    positivity
  · have h1 := sqNorm_nonneg x
    have h2 := abs_nonneg (x 0)
    have hz : sqNorm (0 : Vec 1) + |(0 : Vec 1) 0| = 0 := by simp [sqNorm]
    have hx' : sqNorm x + |x 0| = 0 := hx.trans hz
    exact h0 x (by linarith)

end BfgsCoverage.Article.Local
