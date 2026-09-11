import BfgsVerification.ObjectiveRun

/-!
# Module M: localization around an attained unique minimizer

The sphere minimum is stated on a nontrivial finite-dimensional real normed
space, so its sphere is nonempty. Boundedness and compactness of every sublevel
also cover the zero-dimensional (subsingleton) case. The radial inequalities
hold for any real normed space and any certified positive sphere gap.
-/

noncomputable section
open scoped Topology
open Set Metric

namespace BfgsVerification.Localization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Convexity converts a lower gap on a sphere to a linear radial lower bound
outside that sphere. -/
theorem radial_lower_bound {F : E → ℝ} (hF : ConvexOn ℝ Set.univ F)
    {xStar : E} {r ω : ℝ} (hr : 0 < r)
    (hgap : ∀ z, dist z xStar = r → ω ≤ F z - F xStar)
    {x : E} (hx : r ≤ dist x xStar) :
    (dist x xStar / r) * ω ≤ F x - F xStar := by
  let R := dist x xStar
  have hR : 0 < R := lt_of_lt_of_le hr hx
  let a := r / R
  have ha : 0 ≤ a := div_nonneg hr.le hR.le
  have haone : a ≤ 1 := (div_le_one hR).2 hx
  let z := (1 - a) • xStar + a • x
  have hz : dist z xStar = r := by
    have hsub : z - xStar = a • (x - xStar) := by
      dsimp [z]
      rw [smul_sub, sub_smul, one_smul]
      abel
    rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
    rw [← dist_eq_norm]
    change (r / R) * R = r
    exact div_mul_cancel₀ r hR.ne'
  have hc := hF.2 (show xStar ∈ Set.univ by trivial) (show x ∈ Set.univ by trivial)
    (sub_nonneg.mpr haone) ha (show (1 - a) + a = 1 by ring)
  have hg := hgap z hz
  have hscalar : ω ≤ a * (F x - F xStar) := by
    change F z ≤ (1 - a) * F xStar + a * F x at hc
    linarith
  have hscaled : ω * R ≤ r * (F x - F xStar) := by
    calc
      ω * R ≤ (a * (F x - F xStar)) * R := mul_le_mul_of_nonneg_right hscalar hR.le
      _ = r * (F x - F xStar) := by
        dsimp [a]
        field_simp
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hr).2
  nlinarith [hscaled]

/-- The radial factor is at least one outside the ball. -/
theorem gap_outside_ball {F : E → ℝ} (hF : ConvexOn ℝ Set.univ F)
    {xStar : E} {r ω : ℝ} (hr : 0 < r) (hω : 0 ≤ ω)
    (hgap : ∀ z, dist z xStar = r → ω ≤ F z - F xStar)
    {x : E} (hx : r ≤ dist x xStar) : ω ≤ F x - F xStar := by
  have hratio : 1 ≤ dist x xStar / r := (le_div_iff₀ hr).2 (by simpa using hx)
  calc
    ω = 1 * ω := by ring
    _ ≤ (dist x xStar / r) * ω := mul_le_mul_of_nonneg_right hratio hω
    _ ≤ F x - F xStar := radial_lower_bound hF hr hgap hx

/-- A sublevel whose value gap is strictly below the sphere gap is contained
in the open ball. -/
theorem low_sublevel_subset_ball {F : E → ℝ} (hF : ConvexOn ℝ Set.univ F)
    {xStar : E} {r ω a : ℝ} (hr : 0 < r) (hω : 0 ≤ ω)
    (hgap : ∀ z, dist z xStar = r → ω ≤ F z - F xStar)
    (ha : a - F xStar < ω) : {x | F x ≤ a} ⊆ Metric.ball xStar r := by
  intro x hx
  change dist x xStar < r
  by_contra hn
  have h := gap_outside_ball hF hr hω hgap (le_of_not_gt hn)
  dsimp only [Set.mem_setOf_eq] at hx
  linarith

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- An attained unique minimizer has an attained, strictly positive minimum
gap on every positive-radius sphere. Nontriviality ensures the sphere is nonempty. -/
theorem sphere_gap [Nontrivial E] {F : E → ℝ}
    (hF : ConvexOn ℝ Set.univ F) (xStar : E)
    (hmin : ∀ x, F xStar ≤ F x)
    (hunique : ∀ x, F x = F xStar → x = xStar)
    {r : ℝ} (hr : 0 < r) :
    ∃ ω : ℝ, 0 < ω ∧
      (∃ z, dist z xStar = r ∧ F z - F xStar = ω) ∧
      ∀ z, dist z xStar = r → ω ≤ F z - F xStar := by
  have hcont : Continuous F :=
    continuous_iff_continuousOn_univ.mpr (hF.continuousOn isOpen_univ)
  obtain ⟨z, hz, hleast⟩ := (isCompact_sphere xStar r).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hr.le) hcont.continuousOn
  have hzdist : dist z xStar = r := hz
  have hne : z ≠ xStar := by
    intro he
    subst z
    simp at hzdist
    linarith
  have hvalue_ne : F z ≠ F xStar := fun he => hne (hunique z he)
  have hstrict : F xStar < F z := lt_of_le_of_ne (hmin z) hvalue_ne.symm
  refine ⟨F z - F xStar, sub_pos.mpr hstrict, ⟨z, hzdist, rfl⟩, ?_⟩
  intro y hy
  exact sub_le_sub_right (hleast hy) _

/-- Every sublevel of a finite convex function with an attained unique
minimizer is bounded, including in the zero-dimensional case. -/
theorem sublevel_bounded {F : E → ℝ} (hF : ConvexOn ℝ Set.univ F) (xStar : E)
    (hmin : ∀ x, F xStar ≤ F x)
    (hunique : ∀ x, F x = F xStar → x = xStar) (a : ℝ) :
    Bornology.IsBounded {x | F x ≤ a} := by
  cases subsingleton_or_nontrivial E
  · apply (Bornology.isBounded_singleton (x := xStar)).subset
    intro x _
    exact Set.mem_singleton_iff.mpr (Subsingleton.elim x xStar)
  · obtain ⟨ω, hω, _, hgap⟩ := sphere_gap hF xStar hmin hunique (r := 1) zero_lt_one
    apply (Metric.isBounded_closedBall (x := xStar) (r := max 1 ((a - F xStar) / ω))).subset
    intro x hx
    change dist x xStar ≤ max 1 ((a - F xStar) / ω)
    by_cases hd : dist x xStar ≤ 1
    · exact hd.trans (le_max_left _ _)
    · have hlower := radial_lower_bound hF (r := 1) zero_lt_one hgap (le_of_not_ge hd)
      have hmul : dist x xStar * ω ≤ a - F xStar := by
        simp only [div_one] at hlower
        exact hlower.trans (sub_le_sub_right hx _)
      exact ((le_div_iff₀ hω).2 hmul).trans (le_max_right _ _)

/-- Every sublevel is compact; finite convexity supplies its closedness. -/
theorem sublevel_compact {F : E → ℝ} (hF : ConvexOn ℝ Set.univ F) (xStar : E)
    (hmin : ∀ x, F xStar ≤ F x)
    (hunique : ∀ x, F x = F xStar → x = xStar) (a : ℝ) :
    IsCompact {x | F x ≤ a} := by
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  have hcont : Continuous F :=
    continuous_iff_continuousOn_univ.mpr (hF.continuousOn isOpen_univ)
  exact ⟨isClosed_le hcont continuous_const, sublevel_bounded hF xStar hmin hunique a⟩

/-- A positive lower sphere gap exists also in the subsingleton case, where
its bound is vacuous; the attained-minimum theorem above deliberately requires
a nonempty sphere. -/
theorem positive_sphere_lower_gap {F : E → ℝ}
    (hF : ConvexOn ℝ Set.univ F) (xStar : E)
    (hmin : ∀ x, F xStar ≤ F x)
    (hunique : ∀ x, F x = F xStar → x = xStar)
    {r : ℝ} (hr : 0 < r) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ z, dist z xStar = r → ω ≤ F z - F xStar := by
  cases subsingleton_or_nontrivial E
  · refine ⟨1, zero_lt_one, ?_⟩
    intro z hz
    have hzeq : z = xStar := Subsingleton.elim _ _
    rw [hzeq, dist_self] at hz
    linarith
  · obtain ⟨ω, hω, _, hgap⟩ := sphere_gap hF xStar hmin hunique hr
    exact ⟨ω, hω, hgap⟩

/-- Every specified neighborhood of an attained unique minimizer contains
an entire sublevel strictly above the minimum. -/
theorem neighborhood_basin {F : E → ℝ}
    (hF : ConvexOn ℝ Set.univ F) (xStar : E)
    (hmin : ∀ x, F xStar ≤ F x)
    (hunique : ∀ x, F x = F xStar → x = xStar)
    {U : Set E} (hU : U ∈ 𝓝 xStar) :
    ∃ δ : ℝ, 0 < δ ∧ {x | F x ≤ F xStar + δ} ⊆ U := by
  obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hU
  obtain ⟨ω, hω, hgap⟩ := positive_sphere_lower_gap hF xStar hmin hunique hr
  refine ⟨ω / 2, by positivity, ?_⟩
  have hsub := low_sublevel_subset_ball hF hr hω.le hgap
    (a := F xStar + ω / 2) (by linarith)
  exact hsub.trans (Metric.ball_subset_closedBall.trans hrU)

end FiniteDimensional
end BfgsVerification.Localization

namespace BfgsVerification.AdmissibleBFGSRun

variable {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)

/-- The ordinary Armijo accepted iterates stay inside the localized open ball.
No matrix bound and no condition on rejected trials is needed. -/
theorem trapped_in_ball_of_sphere_gap (xStar : Vec n) {r ω : ℝ}
    (hr : 0 < r) (hω : 0 ≤ ω)
    (hgap : ∀ z, dist z xStar = r → ω ≤ F z - F xStar)
    (hstart : F (R.x 0) - F xStar < ω) (k : ℕ) :
    R.x k ∈ Metric.ball xStar r :=
  Localization.low_sublevel_subset_ball R.convex hr hω hgap hstart
    (R.objective_le_initial k)

/-- An attained unique minimizer supplies compactness of the initial sublevel. -/
theorem initialSublevel_compact_of_unique_minimizer (xStar : Vec n)
    (hmin : ∀ x, F xStar ≤ F x)
    (hunique : ∀ x, F x = F xStar → x = xStar) : IsCompact R.initialSublevel :=
  Localization.sublevel_compact R.convex xStar hmin hunique (F (R.x 0))

/-- A sufficiently low initial value traps all accepted iterates in any
specified neighborhood of an attained unique minimizer. -/
theorem local_basin_of_unique_minimizer (xStar : Vec n)
    (hmin : ∀ x, F xStar ≤ F x)
    (hunique : ∀ x, F x = F xStar → x = xStar)
    {U : Set (Vec n)} (hU : U ∈ 𝓝 xStar) :
    ∃ δ : ℝ, 0 < δ ∧ (F (R.x 0) ≤ F xStar + δ → ∀ k, R.x k ∈ U) := by
  obtain ⟨δ, hδ, hsub⟩ := Localization.neighborhood_basin R.convex xStar hmin hunique hU
  exact ⟨δ, hδ, fun hstart k => hsub ((R.objective_le_initial k).trans hstart)⟩

end BfgsVerification.AdmissibleBFGSRun
