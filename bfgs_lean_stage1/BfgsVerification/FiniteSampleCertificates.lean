import BfgsVerification.PairRealizability
import BfgsVerification.TransportedNormalization
import BfgsVerification.CompactConvergence

/-! Module G: free-constant finite sample feasibility. Uniform continuum
certificate existence or nonexistence does not follow from this finite theorem. -/

noncomputable section
open scoped BigOperators Topology
open Matrix Set

namespace BfgsVerification
namespace TransportedCertificate

/-- Positive data on a finite set have a common strictly positive lower bound,
including the empty set. -/
theorem finite_positive_lower_bound {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ S, 0 < f i) : ∃ m : ℝ, 0 < m ∧ ∀ i ∈ S, m ≤ f i := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert a S ha ih =>
    obtain ⟨m, hm, hmf⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    refine ⟨min (f a) m, lt_min (hf a (Finset.mem_insert_self a S)) hm, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hmf i hi)

theorem metricEnergy_identity {n : ℕ} (g : Vec n) :
    metricEnergy (1 : Mat n) g = sqNorm g := by
  simp [metricEnergy, dot, sqNorm, pow_two]

/-- Every finite sample of nonstationary gradients and eligible pairs admits
one constant identity field. Visibility and suppression constants are finite
and uniform over the sample; projected transport is exact equality. -/
theorem finite_sample_identity_certificate {n r : ℕ} {F : Vec n → ℝ} {c₁ c₂ : ℝ}
    (hc₂ : c₂ < 1) (x g : Fin r → Vec n) (hg : ∀ i, g i ≠ 0)
    (P : Finset (Fin r × Fin r))
    (hp : ∀ p ∈ P, EligiblePair F c₁ c₂ (x p.1) (x p.2) (g p.1) (g p.2)) :
    ∃ m C : ℝ, (1 : Mat n).PosSemidef ∧ 0 < m ∧ 0 ≤ C ∧
      (∀ i, m ≤ metricEnergy (1 : Mat n) (g i)) ∧
      (∀ p ∈ P, metricEnergy (1 : Mat n) (g p.2 - g p.1) ≤
        C * pairCurvature (x p.1) (x p.2) (g p.1) (g p.2)) ∧
      (∀ s : Vec n, (stepProjector s * (1 : Mat n) * (stepProjector s)ᵀ -
        stepProjector s * (1 : Mat n) * (stepProjector s)ᵀ).PosSemidef) := by
  classical
  obtain ⟨m, hm, hmg⟩ := finite_positive_lower_bound Finset.univ
    (fun i => metricEnergy (1 : Mat n) (g i))
    (fun i _ => metricEnergy_pos Matrix.PosDef.one (hg i))
  let t : Fin r × Fin r → ℝ := fun p => pairCurvature (x p.1) (x p.2) (g p.1) (g p.2)
  let a : Fin r × Fin r → ℝ := fun p => sqNorm (g p.2 - g p.1) / t p
  have ht : ∀ p ∈ P, 0 < t p := fun p hP => eligible_curvature_pos (hp p hP) hc₂
  have ha : ∀ p ∈ P, 0 ≤ a p := fun p hP =>
    div_nonneg (sqNorm_nonneg _) (ht p hP).le
  refine ⟨m, ∑ p ∈ P, a p, Matrix.PosSemidef.one, hm, Finset.sum_nonneg ha,
    fun i => hmg i (Finset.mem_univ i), ?_, ?_⟩
  · intro p hP
    have hle : a p ≤ ∑ q ∈ P, a q := Finset.single_le_sum ha hP
    rw [metricEnergy_identity]
    exact (div_le_iff₀ (ht p hP)).mp hle
  · intro s
    simpa only [sub_self] using (Matrix.PosSemidef.zero : (0 : Mat n).PosSemidef)

/-- Differentiable positive-band points are nonstationary, so a finite objective
sample satisfies the preceding theorem without an extra gradient premise. -/
theorem positive_band_gradient_ne_zero {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (star : Vec n) {x g : Vec n}
    (hg : HasFDerivAt F (gradientFunctional g) x) (hx : F star < F x) : g ≠ 0 := by
  intro he
  subst g
  have hmin := global_minimum_of_zero_gradient hF hg
  exact (not_le_of_gt hx) (hmin star)

/-- The fully objective-level finite feasibility statement on a positive band.
There is no continuity or boundedness hypothesis on any unknown field: the
verified field is explicitly I and all constants are selected from finite data. -/
theorem positive_band_finite_sample_feasible {n r : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (star : Vec n) {c₁ c₂ : ℝ} (hc₂ : c₂ < 1)
    (x g : Fin r → Vec n) (hdiff : ∀ i, HasFDerivAt F (gradientFunctional (g i)) (x i))
    (hband : ∀ i, F star < F (x i)) (P : Finset (Fin r × Fin r))
    (hp : ∀ p ∈ P, EligiblePair F c₁ c₂ (x p.1) (x p.2) (g p.1) (g p.2)) :
    ∃ m C : ℝ, (1 : Mat n).PosSemidef ∧ 0 < m ∧ 0 ≤ C ∧
      (∀ i, m ≤ metricEnergy (1 : Mat n) (g i)) ∧
      (∀ p ∈ P, metricEnergy (1 : Mat n) (g p.2 - g p.1) ≤
        C * pairCurvature (x p.1) (x p.2) (g p.1) (g p.2)) ∧
      (∀ s : Vec n, (stepProjector s * (1 : Mat n) * (stepProjector s)ᵀ -
        stepProjector s * (1 : Mat n) * (stepProjector s)ᵀ).PosSemidef) :=
  finite_sample_identity_certificate hc₂ x g
    (fun i => positive_band_gradient_ne_zero hF star (hdiff i) (hband i)) P hp

end TransportedCertificate
end BfgsVerification
