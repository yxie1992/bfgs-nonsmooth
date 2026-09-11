import BfgsVerification.TransportedCertificateVariants

/-! Module T's local statement for a neighborhood of the entire solution set.
The basin is chosen before every run and initial positive definite matrix. -/

noncomputable section
open scoped Topology
open Set Filter

namespace BfgsVerification
namespace Localization

/-- A compact low sublevel and a neighborhood of all minimizers contain a
strictly positive lower sublevel. No uniqueness is required. -/
theorem compact_solution_neighborhood_basin {E : Type*} [TopologicalSpace E]
    {F : E → ℝ} (hF : Continuous F) (star : E) (hmin : ∀ x, F star ≤ F x)
    (b : ℝ) (hb : F star < b) (hK : IsCompact {x | F x ≤ b})
    {U : Set E} (hU : ∀ x, F x = F star → U ∈ 𝓝 x) :
    ∃ δ : ℝ, 0 < δ ∧ F star + δ ≤ b ∧ {x | F x ≤ F star + δ} ⊆ U := by
  classical
  let C := {x | F x ≤ b} \ interior U
  have hC : IsCompact C := hK.diff isOpen_interior
  by_cases hne : C.Nonempty
  · obtain ⟨z, hz, hzmin⟩ := hC.exists_isMinOn hne hF.continuousOn
    have hgap : F star < F z := by
      apply lt_of_le_of_ne (hmin z)
      intro he
      exact hz.2 (mem_interior_iff_mem_nhds.mpr (hU z he.symm))
    refine ⟨min (b - F star) ((F z - F star) / 2),
      lt_min (sub_pos.mpr hb) (by linarith), ?_, ?_⟩
    · linarith [min_le_left (b - F star) ((F z - F star) / 2)]
    · intro x hx
      have hxb : F x ≤ b := by
        change F x ≤ F star + min (b - F star) ((F z - F star) / 2) at hx
        linarith [min_le_left (b - F star) ((F z - F star) / 2)]
      by_contra hxu
      have hxc : x ∈ C := ⟨hxb, fun hi => hxu (interior_subset hi)⟩
      have hzx : F z ≤ F x := hzmin hxc
      change F x ≤ F star + min (b - F star) ((F z - F star) / 2) at hx
      linarith [min_le_right (b - F star) ((F z - F star) / 2)]
  · refine ⟨b - F star, sub_pos.mpr hb, by linarith, ?_⟩
    intro x hx
    by_contra hxu
    apply hne
    exact ⟨x, (by change F x ≤ b; simpa using hx), fun hi => hxu (interior_subset hi)⟩

end Localization
namespace TransportedCertificate

/-- The neighborhood of the entire (possibly nonunique) minimizer set gives a
uniform basin and actual Euclidean solution-set convergence. -/
theorem local_transported_certificate_basin_of_compact_solution_set
    {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (star : Vec n) (hmin : ∀ x, F star ≤ F x) (b : ℝ) (hb : F star < b)
    (hK : IsCompact {x | F x ≤ b}) {U : Set (Vec n)}
    (hU : ∀ x, F x = F star → U ∈ 𝓝 x) {c₁ c₂ : ℝ}
    (hcert : HasBandCertificates F ({x | F x ≤ b} ∩ U) (F star) c₁ c₂) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ R : AdmissibleBFGSRun n F,
      R.c₁ = c₁ → R.c₂ = c₂ → F (R.x 0) ≤ F star + δ →
      (∀ k, F (R.x k) ≤ b ∧ R.x k ∈ U) ∧
      Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧
      Tendsto (fun k => euclideanSolutionDistance F (R.x k)) atTop (𝓝 0) ∧
      ((∀ x, F x = F star → x = star) → Tendsto R.x atTop (𝓝 star)) := by
  have hcont : Continuous F := continuous_iff_continuousOn_univ.mpr
    (hF.continuousOn isOpen_univ)
  obtain ⟨δ, hδ, hδb, hsubU⟩ :=
    Localization.compact_solution_neighborhood_basin hcont star hmin b hb hK hU
  let K' := {x | F x ≤ F star + δ}
  have hsubK : K' ⊆ {x | F x ≤ b} := fun x hx => hx.trans hδb
  have hK' : IsCompact K' := hK.of_isClosed_subset
    (isClosed_le hcont continuous_const) hsubK
  have hsub : K' ⊆ {x | F x ≤ b} ∩ U := fun x hx => ⟨hsubK hx, hsubU hx⟩
  refine ⟨δ, hδ, ?_⟩
  intro R hc₁ hc₂ hstart
  have hc : HasBandCertificates F K' (F star) R.c₁ R.c₂ := by
    rw [hc₁, hc₂]
    exact hasBandCertificates_restrict hcert hsub
  have hxK : ∀ k, R.x k ∈ K' := fun k => (R.objective_le_initial k).trans hstart
  have hv := R.transported_certificate_values K' hK' hxK star hmin hc
  refine ⟨fun k => hsub (hxK k), hv, ?_, ?_⟩
  · exact euclidean_distance_to_argmin_of_values hcont star hmin hK' hxK hv
  · intro hu
    exact R.iterates_tendsto_unique_min_of_values star hmin hu hv

end TransportedCertificate
end BfgsVerification
