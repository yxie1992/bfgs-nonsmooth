import BfgsVerification.ParabolicExamplePairs

/-! Literal radial blowup and failure even on eligible arbitrarily small
predicted decreases, with explicit accepted first-step SPD witnesses. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix

namespace BfgsVerification
namespace Parabolic
namespace Example
open TransportedCertificate RadialCertificate

theorem exists_strict_armijo_parameter {c₁ : ℝ} (hc₁ : c₁ < 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ c₁*(1+ρ) < 1 := by
  by_cases hp : 0 < c₁
  · refine ⟨(1-c₁)/(2*c₁), div_pos (sub_pos.mpr hc₁) (mul_pos (by norm_num) hp), ?_⟩
    have he : c₁*(1+(1-c₁)/(2*c₁)) = (1+c₁)/2 := by field_simp; ring
    rw [he]
    linarith
  · exact ⟨1, zero_lt_one, by push_neg at hp; nlinarith⟩

theorem armijo_iff {u ρ ε c₁ : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    (hsmall : ρ*ε < 3*u^2) :
    c₁*pairDecrease (oldPoint u ε) (newPoint u ρ ε) (oldGradient u) ≤
      objective (oldPoint u ε)-objective (newPoint u ρ ε) ↔ c₁*(1+ρ) ≤ 1 := by
  obtain ⟨hx, hz⟩ := pair_values hρ hε hsmall
  rw [pair_decrease, hx, hz]
  constructor <;> intro h
  · nlinarith
  · nlinarith [mul_le_mul_of_nonneg_right h hε.le]

theorem printed_armijo_iff {u ε c₁ : ℝ} (hε : 0 < ε) (hsmall : ε < 6*u^2) :
    c₁*pairDecrease (oldPoint u ε) (newPoint u (1/2) ε) (oldGradient u) ≤
      objective (oldPoint u ε)-objective (newPoint u (1/2) ε) ↔ c₁ ≤ 2/3 := by
  rw [armijo_iff (by norm_num : (0:ℝ)<1/2) hε (by linarith)]
  constructor <;> intro h <;> linarith

theorem pair_decrease_tendsto (u ρ : ℝ) :
    Tendsto (fun ε => pairDecrease (oldPoint u ε) (newPoint u ρ ε) (oldGradient u))
      (𝓝[>] 0) (𝓝 0) := by
  simpa only [pair_decrease, mul_zero] using
    (show Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) from nhdsWithin_le_nhds).const_mul (1+ρ)

theorem pair_points_tendsto (u ρ : ℝ) :
    Tendsto (oldPoint u) (𝓝[>] 0) (𝓝 (oldPoint u 0)) ∧
    Tendsto (newPoint u ρ) (𝓝[>] 0) (𝓝 (oldPoint u 0)) := by
  have ho : Continuous (oldPoint u) := by
    apply continuous_pi
    intro i
    fin_cases i
    · change Continuous (fun _ : ℝ => u)
      fun_prop
    · change Continuous (fun ε : ℝ => 2*u^2+ε)
      fun_prop
  have hn : Continuous (newPoint u ρ) := by
    apply continuous_pi
    intro i
    fin_cases i
    · change Continuous (fun _ : ℝ => u)
      fun_prop
    · change Continuous (fun ε : ℝ => 2*u^2-ρ*ε)
      fun_prop
  exact ⟨(ho.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds,
    by simpa [oldPoint, newPoint] using (hn.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds⟩

theorem radial_quotient_tendsto {u ρ : ℝ} (hu : u ≠ 0) (hρ : 0 < ρ) :
    Tendsto (fun ε => (radialNumerator 0 (newPoint u ρ ε) (oldGradient u) (newGradient u))^2 /
      pairCurvature (oldPoint u ε) (newPoint u ρ ε) (oldGradient u) (newGradient u))
      (𝓝[>] 0) atTop := by
  have he : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hn : Tendsto (fun ε : ℝ => (2*u^2+ρ*ε)^2) (𝓝[>] 0) (𝓝 ((2*u^2)^2)) := by
    simpa using ((he.const_mul ρ).const_add (2*u^2)).pow 2
  have hd : Tendsto (fun ε : ℝ => (1+ρ)*ε) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa using he.const_mul (1+ρ), ?_⟩
    filter_upwards [self_mem_nhdsWithin] with ε hε
    change 0 < ε at hε
    change 0 < (1+ρ)*ε
    positivity
  have hnum : 0 < (2*u^2)^2 := sq_pos_of_pos (mul_pos (by norm_num) (sq_pos_of_ne_zero hu))
  simpa only [radial_numerator, pair_curvature, div_eq_mul_inv] using
    hn.pos_mul_atTop hnum hd.inv_tendsto_nhdsGT_zero

/-- At every nonzero point of the upper switching parabola, every neighborhood
contains actual eligible pairs with arbitrarily small d and arbitrarily large
radial quotient. The same explicit matrix formula realizes each individual pair. -/
theorem exists_small_eligible_excess_at_base {u ρ c₁ c₂ A : ℝ} {K : Set (Vec 2)}
    (hu : u ≠ 0) (hρ : 0 < ρ) (hc₁ : c₁*(1+ρ) ≤ 1) (hc₂ : 0 ≤ c₂)
    (hA : 0 < A) (hK : K ∈ 𝓝 (oldPoint u 0)) {δ : ℝ} (hδ : 0 < δ) (C : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ρ*ε < 3*u^2 ∧
      oldPoint u ε ∈ K ∧ newPoint u ρ ε ∈ K ∧
      EligiblePair objective c₁ c₂ (oldPoint u ε) (newPoint u ρ ε) (oldGradient u) (newGradient u) ∧
      pairDecrease (oldPoint u ε) (newPoint u ρ ε) (oldGradient u) ≤ δ ∧
      C*pairCurvature (oldPoint u ε) (newPoint u ρ ε) (oldGradient u) (newGradient u) <
        (radialNumerator 0 (newPoint u ρ ε) (oldGradient u) (newGradient u))^2 ∧
      (initialMetric u A ρ ε).PosDef ∧
      bfgsStep (initialMetric u A ρ ε) (oldGradient u) 1 = pairStep (oldPoint u ε) (newPoint u ρ ε) := by
  have hs : ∀ᶠ ε : ℝ in 𝓝[>] 0, ρ*ε < 3*u^2 :=
    ((show Tendsto (fun ε : ℝ => ρ*ε) (𝓝[>] 0) (𝓝 0) from
      by simpa using (show Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) from nhdsWithin_le_nhds).const_mul ρ).eventually
        (eventually_lt_nhds (mul_pos (by norm_num) (sq_pos_of_ne_zero hu))))
  have hd := (pair_decrease_tendsto u ρ).eventually (eventually_lt_nhds hδ)
  have hr := (radial_quotient_tendsto hu hρ).eventually (eventually_gt_atTop C)
  have hpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  obtain ⟨ε, hε, hsmall, hx, hz, hdε, hratio⟩ :=
    (hpos.and (hs.and (((pair_points_tendsto u ρ).1.eventually hK).and
      (((pair_points_tendsto u ρ).2.eventually hK).and (hd.and hr))))).exists
  have hp : 0 < pairCurvature (oldPoint u ε) (newPoint u ρ ε) (oldGradient u) (newGradient u) := by
    rw [pair_curvature]; positivity
  exact ⟨ε, hε, hsmall, hx, hz, pair_eligible hρ hε hsmall hc₁ hc₂, hdε.le,
    (lt_div_iff₀ hp).mp hratio, initialMetric_posDef hA hρ hε, initialMetric_step u A ρ ε⟩

theorem exists_nonzero_base_in_neighborhood {K : Set (Vec 2)} (hK : K ∈ 𝓝 (0 : Vec 2)) :
    ∃ u : ℝ, u ≠ 0 ∧ K ∈ 𝓝 (oldPoint u 0) := by
  obtain ⟨O, hOK, hO, hzero⟩ := mem_nhds_iff.mp hK
  have hc : Continuous (fun u : ℝ => oldPoint u 0) := by
    apply continuous_pi
    intro i
    fin_cases i
    · change Continuous (fun u : ℝ => u)
      fun_prop
    · change Continuous (fun u : ℝ => 2*u^2+0)
      fun_prop
  have ht : Tendsto (fun u : ℝ => oldPoint u 0) (𝓝[>] 0) (𝓝 (0 : Vec 2)) := by
    have hzero : oldPoint 0 0 = (0 : Vec 2) := by ext i; fin_cases i <;> norm_num [oldPoint]
    rw [← hzero]
    exact (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  have hpos : ∀ᶠ u : ℝ in 𝓝[>] 0, 0 < u := self_mem_nhdsWithin
  obtain ⟨u, hu, hOu⟩ := (hpos.and (ht.eventually (hO.mem_nhds hzero))).exists
  exact ⟨u, ne_of_gt hu, mem_of_superset (hO.mem_nhds hOu) hOK⟩

/-- Exact near-stalling separation for every fixed admissible choice of
line-search constants. The positive band is chosen before every threshold and
candidate radial bound. Eligibility and the SPD first-step witness are derived. -/
theorem eligible_radial_unbounded_on_neighborhood {K : Set (Vec 2)}
    (hK : K ∈ 𝓝 (0 : Vec 2)) {c₁ c₂ : ℝ} (hc₁ : c₁ < 1) (hc₂ : 0 ≤ c₂) :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → ∀ C : ℝ,
      ∃ x z g h : Vec 2, ∃ H : Mat 2,
        x ∈ K ∧ z ∈ K ∧ η ≤ objective z ∧ objective z ≤ objective x ∧
        EligiblePair objective c₁ c₂ x z g h ∧ pairDecrease x z g ≤ δ ∧
        H.PosDef ∧ bfgsStep H g 1 = pairStep x z ∧
        C*pairCurvature x z g h < (radialNumerator 0 z g h)^2 := by
  obtain ⟨u, hu, hKu⟩ := exists_nonzero_base_in_neighborhood hK
  obtain ⟨ρ, hρ, hcρ⟩ := exists_strict_armijo_parameter hc₁
  refine ⟨3*u^2, mul_pos (by norm_num) (sq_pos_of_ne_zero hu), ?_⟩
  intro δ hδ C
  obtain ⟨ε, hε, hs, hx, hz, hp, hd, he, hH, hstep⟩ :=
    exists_small_eligible_excess_at_base (A := 1) hu hρ hcρ.le hc₂
      (by norm_num) hKu hδ C
  obtain ⟨hFx, hFz⟩ := pair_values hρ hε hs
  exact ⟨oldPoint u ε, newPoint u ρ ε, oldGradient u, newGradient u,
    initialMetric u 1 ρ ε, hx, hz, by rw [hFz], by rw [hFx, hFz]; linarith,
    hp, hd, hH, hstep, he⟩

/-- The original RS condition fails on every neighborhood of the unique
minimizer. The contradiction uses differentiable actual eligible pairs. -/
theorem not_radial_secant_on_neighborhood {K : Set (Vec 2)}
    (hK : K ∈ 𝓝 (0 : Vec 2)) : ¬ HasRadialSecantBounds objective K 0 := by
  intro hRS
  obtain ⟨u, hu, hKu⟩ := exists_nonzero_base_in_neighborhood hK
  have hη : 0 < 3*u^2 := mul_pos (by norm_num) (sq_pos_of_ne_zero hu)
  obtain ⟨C, hC⟩ := hRS (3*u^2) hη
  obtain ⟨ε, hε, hs, hx, hz, hp, _, he, _, _⟩ :=
    exists_small_eligible_excess_at_base (ρ := 1) (c₁ := 1/4) (c₂ := 1/2) (A := 1)
      hu (by norm_num) (by norm_num) (by norm_num) (by norm_num) hKu (δ := 1) (by norm_num) C
  obtain ⟨hFx, hFz⟩ := pair_values (by norm_num : (0:ℝ)<1) hε hs
  have hzero : objective 0 = 0 := family.objective_zero
  have hcurv : 0 < secantCurvature (oldPoint u ε) (newPoint u 1 ε) (oldGradient u) (newGradient u) := by
    change 0 < pairCurvature _ _ _ _
    rw [pair_curvature]; positivity
  have hb := hC _ _ _ _ hx hz (by rw [hzero, hFz]; simp) (by rw [hFx, hFz]; linarith)
    hp.gradient_x hp.gradient_z hcurv
  exact (not_lt_of_ge hb) he

theorem not_radial_secant_on_sublevel {B : ℝ} (hB : 0 < B) :
    ¬ HasRadialSecantBounds objective {x | objective x ≤ B} 0 := by
  apply not_radial_secant_on_neighborhood
  have ho : IsOpen {x : Vec 2 | objective x < B} := isOpen_lt family.objective_continuous continuous_const
  apply mem_of_superset (ho.mem_nhds (by change family.objective 0 < B; simpa only [family.objective_zero] using hB))
  intro x hx
  change objective x < B at hx
  change objective x ≤ B
  exact hx.le

end Example
end Parabolic
end BfgsVerification
